include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"
include "symbolize.mc"

include "mexpr/type-check.mc"

include "seq.mc"
include "option.mc"

lang DeclTypeCheck = TypeCheck + DeclAst

  sem typeCheckDecl : TCEnv -> Decl -> (TCEnv, Decl)
end

lang DeclSemTypeCheck = SemDeclAst + ResolveType + DeclTypeCheck +
                        SubstituteUnknown + ResolveType + SubstituteNewReprs +
                        PatTypeCheck
  sem typeCheckSemDecls : TCEnv -> [DeclSemType] -> (TCEnv, [DeclSemType])
  sem typeCheckSemDecls env =
  | sems ->
    -- First: Generate a new environment a type variable for each semantic
    -- function.
    let semIteratee = lam acc. lam t : DeclSemType.
      let tyAnnot = resolveType t.info env false t.tyAnnot in
      let tyAnnot = substituteNewReprs env tyAnnot in
      let tyBody = substituteUnknown t.info {env with currentLvl = 0} (Poly ()) tyAnnot in
      let newEnv = _insertVar t.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 (stripTyAll tyBody).0 in
      ((newEnv, newTyVars), {t with tyAnnot = tyAnnot, tyBody = tyBody})
    in
    match mapAccumL semIteratee (env, mapEmpty nameCmp) sems
    with ((recLetEnv, tyVars), sems) in

    let newTyVarEnv =
      mapFoldWithKey (lam vs. lam v. lam k. mapInsert v (0, k) vs) recLetEnv.tyVarEnv tyVars in
    let newEnv = {recLetEnv with currentLvl = 0, tyVarEnv = newTyVarEnv} in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckCase
      : Type -> TCEnv -> {pat : Pat, thn : Expr} -> {pat : Pat, thn : Expr}
      = lam targetTy. lam env. lam c : {pat : Pat, thn : Expr}.
      match typeCheckPat env (mapEmpty nameCmp) c.pat with (patEnv, pat) in
      let env = {env with varEnv = mapUnion env.varEnv patEnv} in
      unify env [NoInfo (), NoInfo ()] (tyPat pat) targetTy;
      let thn = typeCheckExpr env c.thn in
      {pat = pat, thn = thn}
    in

    let typeCheckSem = lam env : TCEnv. lam semType : DeclSemType.
      match semType.args with Some args in

      let insertArg : TCEnv -> {ident : Name, tyAnnot : Type} -> (TCEnv, Type) =
        lam env. lam a.

        let resultTy = substituteUnknown (NoInfo ()) env (Mono ()) a.tyAnnot in
        let resultEnv = _insertVar a.ident resultTy env in
        (resultEnv, resultTy)
      in

      match mapAccumL insertArg env args with (env, tyParams) in

      let targetTy = newmetavar (Mono ()) 2 (NoInfo ())  in

      let cases = map (lam c. typeCheckCase targetTy env c) semType.cases in

      let headThn = (head cases).thn in
      iter (lam c. unify env [NoInfo (), NoInfo ()] (tyTm headThn) (tyTm c.thn)) (tail cases);

      let resultTy = tyarrow_ targetTy (tyTm headThn) in
      let resultTy = foldr tyarrow_ resultTy tyParams in
      (env, {semType with cases = cases, tyBody = resultTy})
    in
    match mapAccumL typeCheckSem newEnv sems with (newEnv, sems) in

    let envIteratee = lam acc. lam s.
      match gen env.currentLvl acc.1 s.tyBody with (tyBody, vars) in
      let newEnv = _insertVar s.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
      ((newEnv, newTyVars), {s with tyBody = tyBody})
    in
    match mapAccumL envIteratee (env, tyVars) sems with ((env, _), sems) in

    (env, sems)
end

lang DeclLangTypeCheck = DeclTypeCheck + LangDeclAst + SemDeclAst + SynDeclAst +
                         TypeDeclAst + DeclSemTypeCheck
  sem typeCheckDecl env =
  | DeclLang d ->
    let typeDecls = mapOption (lam d. match d with DeclType d then Some (DeclType d) else None ()) d.decls in
    let synDecls = mapOption (lam d. match d with DeclSyn d then Some (DeclSyn d) else None ()) d.decls in
    let semDeclTypes = mapOption (lam d. match d with DeclSem d then Some d else None ()) d.decls in

    match mapAccumL typeCheckDecl env typeDecls with (env, typeDecls) in
    match mapAccumL typeCheckDecl env synDecls with (env, synDecls) in
    match typeCheckSemDecls env semDeclTypes with (env, semDeclTypes) in


    let semDecls = map (lam x. DeclSem x) semDeclTypes in

    (env, DeclLang {d with decls = join [typeDecls, synDecls, semDecls]})
end

lang DeclSynTypeCheck = DeclTypeCheck + SynDeclAst + ResolveType
  sem typeCheckDecl env =
  | DeclSyn d ->
    -- We add a tyConEnv to the env if this is the base syn definition.
    let env = if null d.includes then
      {env with tyConEnv = mapInsert d.ident (0, d.params, tyvariant_ []) env.tyConEnv}
    else
      env
    in

    let typeCheckDef = lam env. lam def.
      let tyIdent = resolveType d.info env false def.tyIdent in
      let tyArrow = TyArrow {from = tyIdent, to = ntycon_ d.ident, info = d.info} in
      let env = {env with conEnv = mapInsert def.ident (0, tyArrow) env.conEnv} in
      (env, {def with tyIdent = tyIdent})
    in

    match mapAccumL typeCheckDef env d.defs with (env, defs) in
    (env, DeclSyn {d with defs = defs})
end

lang ProgramTypeCheck = DeclTypeCheck + MLangTopLevel
  sem typeCheckProgram : MLangProgram -> MLangProgram
  sem typeCheckProgram =
  | program ->
    match mapAccumL typeCheckDecl typcheckEnvDefault program.decls with (env, decls) in
    let expr = typeCheckExpr env program.expr in
    {decls = decls, expr = expr}
end

lang MLangTypeCheck = ProgramTypeCheck + MExprTypeCheck + MLangPrettyPrint +
                      DeclSynTypeCheck +
                      DeclLangTypeCheck

end

lang MyPPrintLang = MLangPrettyPrint + MExprPrettyPrint + MetaVarTypePrettyPrint
end

mexpr
use MLangTypeCheck in
use MyPPrintLang in
use MLangSym in

let p : MLangProgram = {
  decls = [(ulet_ "x" (int_ 10))],
  expr = addi_ (var_ "x") (int_ 1)
} in

typeCheckProgram p ;

let p : MLangProgram = {
  decls = [
    type_ "Foo" [] tyint_,
    let_ "x" (tycon_ "Foo") (int_ 50)
  ],
  expr = (var_ "x")
} in

typeCheckProgram p ;

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_syn_ "SomeSyn" [("Foo", tyint_), ("Bar", tystr_)]
    ],
    let_ "x" (tycon_ "SomeSyn") (conapp_ "Foo" (int_ 10))
  ],
  expr = matchex_
      (var_ "x")
      (pcon_ "Foo" (pvar_ "x"))
      (addi_ (var_ "x") (int_ 1))
} in

typeCheckProgram p ;

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_sem_ "g" [("y", tyunknown_)] [
        (pvar_ "x", addi_ (var_ "x") (app_ (var_ "f") (var_ "y")))
      ]
      ,
      decl_sem_ "f" [] [
        (pvar_ "x", addi_ (var_ "x") (int_ 1))
      ]
    ]
  ],
  -- expr = app_ (var_ "f") (char_ 'c')
  -- expr = app_ (var_ "f") (int_ 1)
  expr = appf2_ (var_ "g") (int_ 1) (int_ 3)
} in

let p = typeCheckProgram p in
-- printLn (mlang2str p);

let p : MLangProgram = {
  decls = [
    utest_ (int_ 1) (int_ 2),
    utestu_ (int_ 1) (int_ 2) (uconst_ (CNeqi ()))
  ],
  expr = uunit_
} in

let p = typeCheckProgram p in

let odd = (ulam_ "x"
  (if_
    (eqi_ (var_ "x") (int_ 0))
    (false_)
    (appf1_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
in
let even = (ulam_ "x"
  (if_
    (eqi_ (var_ "x") (int_ 0))
    (true_)
    (appf1_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
in
let p : MLangProgram = {
    decls = [
        ureclets_ [("odd", odd), ("even", even)]
    ],
    expr = appf1_ (var_ "odd") (int_ 9)
} in
let p = typeCheckProgram p in
()
