include "generate-pprint.mc"
include "generate-eq.mc"

include "mlang/loader.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "name.mc"
include "mexpr/info.mc"
include "basic-types.mc"

lang StripUtestLoader = MCoreLoader + UtestDeclAst + OpaqueAst
  syn Hook +=
  | StripUtestHook ()

  sem stripUtests : Expr -> Expr
  sem stripUtests =
  | TmDecl (t & {decl = DeclUtest _}) -> stripUtests t.inexpr
  | t & TmOpaque _ -> t
  | t -> smap_Expr_Expr stripUtests t

  sem _postTypecheck loader decl += | StripUtestHook _ ->
    let decl = match decl with DeclUtest x
      then DeclLet
        { ident = nameNoSym ""
        , tyAnnot = tyunknown_
        , tyBody = tyunit_
        , body = unit_
        , info = x.info
        }
      else smap_Decl_Expr stripUtests decl
    in (loader, decl)
end

lang UtestLoader = MCoreLoader + GenerateEqLoader + GeneratePprintLoader + StripUtestLoader
  syn Hook +=
  | UtestHook
    { defaultOnFail : Name
    , runner : Name
    , exitOnFailure : Name
    , includeUtestIf : {static : Bool, info : Info} -> Bool
    }

  -- Enable code generation replacing `utest` with equivalent
  -- code. Will remove `StripUtestHook` if present.
  sem enableUtestGeneration : ({static : Bool, info : Info} -> Bool) -> Loader -> Loader
  sem enableUtestGeneration includeUtestIf = | loader ->
    if hasHook (lam x. match x with UtestHook _ then true else false) loader then loader else

    -- NOTE(vipa, 2025-01-27): We strip utests found in files before
    -- we're ready. Notably, this means that we can never utest things
    -- that eq-generation, pprint-generation, or the utest-runtime
    -- depend on.
    let loader = addHook loader (StripUtestHook ()) in
    let loader = enableEqGeneration loader in
    let loader = enablePprintGeneration loader in
    match includeFileExn "." "stdlib::mexpr/utest-runtime.mc" loader with (utestEnv, loader) in

    let hook =
      { defaultOnFail = _getVarExn "utestDefaultOnFail" utestEnv
      , runner = _getVarExn "utestRunner" utestEnv
      , exitOnFailure = _getVarExn "utestExitOnFailure" utestEnv
      , includeUtestIf = includeUtestIf
      } in
    let loader = remHook (lam x. match x with StripUtestHook _ then true else false) loader in
    addHook loader (UtestHook hook)

  sem _preBuildFullAst loader += | UtestHook hook ->
    let decl = DeclLet
      { ident = nameNoSym ""
      , tyAnnot = tyunknown_
      , tyBody = tyunknown_
      , body = app_ (nvar_ (hook.exitOnFailure)) unit_
      , info = NoInfo ()
      } in
    _addDeclExn loader decl

  sem _postTypecheck loader decl += | UtestHook hook ->
    match decl with DeclUtest d then
      if hook.includeUtestIf {static = true, info = d.info} then
        match replaceUtests hook true loader (bind_ decl unit_) with (loader, expr) in
        let decl = DeclLet
          { ident = nameNoSym ""
          , tyAnnot = tyunit_
          , tyBody = tyunit_
          , body = expr
          , info = d.info
          } in
        (loader, decl)
      else
        let noop = DeclLet
          { ident = nameNoSym ""
          , tyAnnot = tyunknown_
          , tyBody = tyunit_
          , body = unit_
          , info = d.info
          } in
        (loader, noop)
    else
      smapAccumL_Decl_Expr (replaceUtests hook true) loader decl

  sem replaceUtests hook static loader =
  | tm & TmLam _ -> smapAccumL_Expr_Expr (replaceUtests hook false) loader tm
  | tm & TmOpaque _ -> (loader, tm)
  | tm -> smapAccumL_Expr_Expr (replaceUtests hook static) loader tm
  | TmDecl (x & {decl = DeclUtest t}) ->
    if hook.includeUtestIf {static = static, info = t.info} then
      let infoStr = str_ (info2str t.info) in

      match
        match t.tusing with Some eqfn
        then (loader, str_ (concat "    Using: " (expr2str eqfn)), eqfn)
        else match eqFunctionsFor [tyTm t.expected] loader with (loader, [eqfn]) in (loader, str_ "", eqfn)
      with (loader, usingStr, eqFn) in

      match
        match t.tonfail with Some ppfn then (loader, ppfn) else
        match pprintFunctionsFor [tyTm t.test, tyTm t.expected] loader with (loader, [testF, expectedF]) in
        (loader, appf2_ (nvar_ hook.defaultOnFail) testF expectedF)
      with (loader, onFailFn) in

      -- NOTE(vipa, 2025-01-27): This doesn't replace utests occurring
      -- in `using` or `else`, which is consistent with the old
      -- implementation, but maybe not ideal? It should be *very* rare
      -- that it matters though.
      match replaceUtests hook static loader t.test with (loader, test) in
      match replaceUtests hook static loader t.expected with (loader, expected) in
      match replaceUtests hook static loader x.inexpr with (loader, inexpr) in

      let test = appSeq_ (nvar_ hook.runner) [infoStr, usingStr, onFailFn, eqFn, test, expected] in
      let tm = TmDecl
        { decl = DeclLet
          { ident = nameNoSym ""
          , tyAnnot = tyunknown_
          , tyBody = tyunit_
          , body = test
          , info = t.info
          }
        , inexpr = inexpr
        , ty = tyTm inexpr
        , info = x.info
        } in
      (loader, tm)
    else
      replaceUtests hook static loader x.inexpr
end
