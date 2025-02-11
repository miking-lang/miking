include "generate-pprint.mc"
include "generate-eq.mc"

include "mlang/loader.mc"

lang StripUtestLoader = MCoreLoader + UtestAst
  syn Hook =
  | StripUtestHook ()

  sem stripUtests : Expr -> Expr
  sem stripUtests =
  | TmUtest t -> stripUtests t.next
  | t -> smap_Expr_Expr stripUtests t

  sem _postTypecheck loader decl = | StripUtestHook _ ->
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
  syn Hook =
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

  -- Should be called when the entire program has been loaded and
  -- constructed. Inserts the code that checks if any tests have
  -- failed and, if so, exits the program.
  sem insertUtestExitCheck : Loader -> Loader
  sem insertUtestExitCheck = | loader ->
    let f = lam loader. lam x.
      match x with UtestHook hook then
        let decl = DeclLet
          { ident = nameNoSym ""
          , tyAnnot = tyunknown_
          , tyBody = tyunknown_
          , body = app_ (nvar_ (hook.exitOnFailure)) unit_
          , info = NoInfo ()
          } in
        Some (_addDeclExn loader decl, ())
      else None () in
    (withHookState f loader).0

  sem _postTypecheck loader decl = | UtestHook hook ->
    match decl with DeclUtest d then
      if hook.includeUtestIf {static = true, info = d.info} then
        match replaceUtests hook true loader (declAsExpr unit_ decl) with (loader, expr) in
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
  | tm -> smapAccumL_Expr_Expr (replaceUtests hook static) loader tm
  | TmUtest x ->
    if hook.includeUtestIf {static = static, info = x.info} then
      let infoStr = str_ (info2str x.info) in

      match
        match x.tusing with Some eqfn
        then (loader, str_ (concat "    Using: " (expr2str eqfn)), eqfn)
        else match eqFunctionsFor [tyTm x.expected] loader with (loader, [eqfn]) in (loader, str_ "", eqfn)
      with (loader, usingStr, eqFn) in

      match
        match x.tonfail with Some ppfn then (loader, ppfn) else
        match pprintFunctionsFor [tyTm x.test, tyTm x.expected] loader with (loader, [testF, expectedF]) in
        (loader, appf2_ (nvar_ hook.defaultOnFail) testF expectedF)
      with (loader, onFailFn) in

      -- NOTE(vipa, 2025-01-27): This doesn't replace utests occurring
      -- in `using` or `else`, which is consistent with the old
      -- implementation, but maybe not ideal? It should be *very* rare
      -- that it matters though.
      match replaceUtests hook static loader x.test with (loader, test) in
      match replaceUtests hook static loader x.expected with (loader, expected) in
      match replaceUtests hook static loader x.next with (loader, next) in

      let test = appSeq_ (nvar_ hook.runner) [infoStr, usingStr, onFailFn, eqFn, test, expected] in
      let tm = TmLet
        { ident = nameNoSym ""
        , tyAnnot = tyunknown_
        , tyBody = tyunit_
        , body = test
        , inexpr = next
        , ty = tyTm next
        , info = x.info
        } in
      (loader, tm)
    else
      replaceUtests hook static loader x.next
end
