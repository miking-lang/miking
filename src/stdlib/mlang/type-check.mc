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

lang DeclLetTypeCheck = DeclTypeCheck + LetDeclAst + LamAst + FunTypeAst + 
                        ResolveType + SubstituteUnknown +
                        NonExpansive + MetaVarDisableGeneralize + 
                        PropagateTypeAnnot + SubstituteNewReprs
  sem typeCheckDecl env =
  | DeclLet d -> 
    -- A DeclLet is treated exactly as a TmLet in the MExpr type checker.
    let newLvl = addi 1 env.currentLvl in
    let tyAnnot = resolveType d.info env false d.tyAnnot in
    let tyAnnot = substituteNewReprs env tyAnnot in
    let tyBody = substituteUnknown d.info {env with currentLvl = newLvl} (Poly ()) tyAnnot in
    match
      if nonExpansive true d.body then
        match stripTyAll tyBody with (vars, stripped) in
        let newTyVarEnv =
          foldr (lam v. mapInsert v.0 (newLvl, v.1)) env.tyVarEnv vars in
        let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
        let body = typeCheckExpr newEnv (propagateTyAnnot (d.body, tyAnnot)) in
        -- Unify the annotated type with the inferred one and generalize
        unify newEnv [infoTy d.tyAnnot, infoTm body] stripped (tyTm body);
        (if env.disableRecordPolymorphism then
           disableRecordGeneralize env.currentLvl tyBody else ());
        match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
        (body, tyBody)
      else
        let body = typeCheckExpr {env with currentLvl = newLvl} d.body in
        unify env [infoTy d.tyAnnot, infoTm body] tyBody (tyTm body);
        -- TODO(aathn, 2023-05-07): Relax value restriction
        weakenMetaVars env.currentLvl tyBody;
        (body, tyBody)
    with (body, tyBody) in

    let env = _insertVar d.ident tyBody env in 

    (env, DeclLet {d with body = body,
                          tyAnnot = tyAnnot,
                          tyBody = tyBody})
end

lang DeclUtestTypeCheck = DeclTypeCheck + UtestDeclAst
  sem typeCheckDecl env =
  | DeclUtest t ->
    let test = typeCheckExpr env t.test in
    let expected = typeCheckExpr env t.expected in
    let tusing = optionMap (typeCheckExpr env) t.tusing in

    (switch tusing 
      case Some tu then 
        unify env [infoTm test, infoTm expected, infoTm tu] 
          (tyarrows_ [tyTm test, tyTm expected, tybool_]) (tyTm tu)
      case None _ then 
        unify env [infoTm test, infoTm expected] (tyTm test) (tyTm expected)
    end);
    (env, DeclUtest {t with test = test, expected = expected, tusing = tusing})
end

lang DeclConDefTypeCheck = DeclTypeCheck + DataDeclAst + DataTypeCheck
  sem typeCheckDecl env = 
  | DeclConDef t ->
    let tyIdent = resolveType t.info env false t.tyIdent in
    let tyIdent = substituteNewReprs env tyIdent in

    match _makeConstructorType t.info env.disableConstructorTypes t.ident tyIdent
    with (target, tydeps, tyIdent) in

    let tydeps =
      mapInsert target tydeps
        (setFold (lam m. lam t. mapInsert t (setOfSeq nameCmp [target]) m)
                 (mapEmpty nameCmp) tydeps) in
                 
    let env = {env with conEnv = mapInsert t.ident (0, tyIdent) env.conEnv,
                        typeDeps = mapUnionWith setUnion tydeps env.typeDeps,
                        conDeps = mapInsertWith setUnion target
                               (setOfSeq nameCmp [t.ident]) env.conDeps} in 

    (env, DeclConDef {t with tyIdent = tyIdent})
end

lang DeclRecLetsTypeCheck = DeclTypeCheck + RecLetsDeclAst + 
                            MetaVarDisableGeneralize + PropagateTypeAnnot +
                            SubstituteUnknown + ResolveType + 
                            SubstituteNewReprs
  sem typeCheckDecl env =
  | DeclRecLets t ->
    -- NOTE(aathn, 2024-05-24): This code assumes that each recursive let-binding
    -- is a syntactic lambda, so that generalization is always safe.
    let newLvl = 0 in 
    -- First: Generate a new environment containing the recursive bindings
    let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
      let tyAnnot = resolveType t.info env false b.tyAnnot in
      let tyAnnot = substituteNewReprs env tyAnnot in
      let tyBody = substituteUnknown t.info {env with currentLvl = newLvl} (Poly ()) tyAnnot in
      let newEnv = _insertVar b.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 (stripTyAll tyBody).0 in
      ((newEnv, newTyVars), {b with tyAnnot = tyAnnot, tyBody = tyBody})
    in
    match mapAccumL recLetEnvIteratee (env, mapEmpty nameCmp) t.bindings
    with ((recLetEnv, tyVars), bindings) in
    let newTyVarEnv =
      mapFoldWithKey (lam vs. lam v. lam k. mapInsert v (newLvl, k) vs) recLetEnv.tyVarEnv tyVars in
    let newEnv = {recLetEnv with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckBinding = lam b: RecLetBinding.
      let body =
        let body = typeCheckExpr newEnv (propagateTyAnnot (b.body, b.tyAnnot)) in
        -- Unify the inferred type of the body with the annotated one
        unify newEnv [infoTy b.tyAnnot, infoTm body] (stripTyAll b.tyBody).1 (tyTm body);
        body
      in
      {b with body = body}
    in
    let bindings = map typeCheckBinding bindings in
    (if env.disableRecordPolymorphism then
       iter (lam b. disableRecordGeneralize env.currentLvl b.tyBody) bindings
     else ());

    -- Third: Produce a new environment with generalized types
    let envIteratee = lam acc. lam b : RecLetBinding.
      match gen env.currentLvl acc.1 b.tyBody with (tyBody, vars) in
      let newEnv = _insertVar b.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
      ((newEnv, newTyVars), {b with tyBody = tyBody})
    in
    match mapAccumL envIteratee (env, tyVars) bindings with ((env, _), bindings) in
    (env, DeclRecLets {t with bindings = bindings})
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

lang DeclTypeTypeCheck = DeclTypeCheck + TypeDeclAst + VariantTypeAst + ResolveType
  sem typeCheckDecl env =
  | DeclType d ->   
    -- A DeclType is treated exactly as a TmType in the MExpr type checker.
    let tyIdent = resolveType d.info env false d.tyIdent in
    -- let newLvl = match tyIdent with !TyVariant _ then addi 1 env.currentLvl else 0 in
    -- figure out whether to keep this level
    let newTyConEnv = mapInsert d.ident (0, d.params, tyIdent) env.tyConEnv in

    let env = {env with tyConEnv = newTyConEnv} in 

    (env, DeclType {d with tyIdent = tyIdent})
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

lang DeclExtTypeCheck = DeclTypeCheck + ExtDeclAst + ResolveType 
  sem typeCheckDecl env =
  | DeclExt t ->
    -- TODO(vipa, 2023-06-15): Error if a RepType shows up in an external definition?
    let tyIdent = resolveType t.info env true t.tyIdent in
    let env = {env with varEnv = mapInsert t.ident tyIdent env.varEnv} in
    (env, DeclExt {t with tyIdent = tyIdent})
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
                      DeclLetTypeCheck + DeclTypeTypeCheck + DeclSynTypeCheck +
                      DeclLangTypeCheck + DeclUtestTypeCheck + DeclConDefTypeCheck +
                      DeclRecLetsTypeCheck + DeclExtTypeCheck

end

lang MyPPrintLang = MLangPrettyPrint + MExprPrettyPrint + MetaVarTypePrettyPrint 
end

mexpr
use MLangTypeCheck in 
use MyPPrintLang in
use MLangSym in  

let p : MLangProgram = {
  decls = [(decl_ulet_ "x" (int_ 10))],
  expr = addi_ (var_ "x") (int_ 1)
} in 

typeCheckProgram p ; 

let p : MLangProgram = {
  decls = [
    decl_type_ "Foo" [] tyint_,
    decl_let_ "x" (tycon_ "Foo") (int_ 50)
  ],
  expr = (var_ "x")
} in 

typeCheckProgram p ; 

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_syn_ "SomeSyn" [("Foo", tyint_), ("Bar", tystr_)]
    ],
    decl_let_ "x" (tycon_ "SomeSyn") (conapp_ "Foo" (int_ 10))
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
    decl_utest_ (int_ 1) (int_ 2),
    decl_utestu_ (int_ 1) (int_ 2) (uconst_ (CNeqi ()))
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
        decl_ureclets_ [("odd", odd), ("even", even)]
    ],
    expr = appf1_ (var_ "odd") (int_ 9)
} in 
let p = typeCheckProgram p in 
()