include "mexpr/type-check.mc"
include "ast.mc"

lang TypeCheckDecl = TypeCheck
  sem typeCheckDecl : TCEnv -> Decl -> (TCEnv, Decl)
end

-- NOTE(vipa, 2024-11-27): These implementations should follow the
-- corresponding Expr implementations in mexpr/type-check.mc

lang TypeCheckLetDecl = TypeCheckDecl + LetDeclAst
  + MetaVarDisableGeneralize + PropagateTypeAnnot + NonExpansive + SubstituteUnknown
  + SubstituteNewReprs + ResolveType
  sem typeCheckDecl env =
  | DeclLet t ->
    let newLvl = addi 1 env.currentLvl in
    let tyAnnot = resolveType t.info env false t.tyAnnot in
    let tyAnnot = substituteNewReprs env tyAnnot in
    let tyBody = substituteUnknown t.info {env with currentLvl = newLvl} (Poly ()) tyAnnot in
    match
      if nonExpansive true t.body then
        match stripTyAll tyBody with (vars, stripped) in
        let newTyVarEnv =
          foldr (lam v. mapInsert v.0 (newLvl, v.1)) env.tyVarEnv vars in
        let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
        let body = typeCheckExpr newEnv (propagateTyAnnot (t.body, tyAnnot)) in
        -- Unify the annotated type with the inferred one and generalize
        unify newEnv [infoTy t.tyAnnot, infoTm body] stripped (tyTm body);
        (if env.disableRecordPolymorphism then
           disableRecordGeneralize env.currentLvl tyBody else ());
        match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
        (body, tyBody)
      else
        let body = typeCheckExpr {env with currentLvl = newLvl} t.body in
        unify env [infoTy t.tyAnnot, infoTm body] tyBody (tyTm body);
        -- TODO(aathn, 2023-05-07): Relax value restriction
        weakenMetaVars env.currentLvl tyBody;
        (body, tyBody)
    with (body, tyBody) in
    let env = _insertVar t.ident tyBody env in
    ( env
    , DeclLet {t with body = body, tyAnnot = tyAnnot, tyBody = tyBody}
    )
end

lang TypeCheckRecLetsDecl = TypeCheckDecl + RecLetsDeclAst
  + MetaVarDisableGeneralize + PropagateTypeAnnot + NonExpansive + SubstituteUnknown
  + SubstituteNewReprs + ResolveType
  sem typeCheckDecl env =
  | DeclRecLets t ->
    -- NOTE(aathn, 2024-05-24): This code assumes that each recursive let-binding
    -- is a syntactic lambda, so that generalization is always safe.
    let newLvl = addi 1 env.currentLvl in
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

lang TypeCheckTypeDecl = TypeCheckDecl + TypeDeclAst + ResolveType
  sem typeCheckDecl env =
  | DeclType t ->
    let tyIdent = resolveType t.info env false t.tyIdent in
    -- NOTE(aathn, 2023-05-08): Aliases are treated as the underlying
    -- type and do not need to be scope checked.
    let newLvl =
      match tyIdent with !TyVariant _ then addi 1 env.currentLvl else 0 in
    let newTyConEnv = mapInsert t.ident (newLvl, t.params, tyIdent) env.tyConEnv in
    let env =
      { env with currentLvl = addi 1 env.currentLvl
      , tyConEnv = newTyConEnv
      , reptypes = env.reptypes
      } in
    (env, DeclType {t with tyIdent = tyIdent})
end

lang TypeCheckDataDecl = TypeCheckDecl + DataDeclAst + ResolveType + DataTypeCheck
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
    let newLvl = addi 1 env.currentLvl in
    let env =
      { env with currentLvl = newLvl
      , conEnv = mapInsert t.ident (newLvl, tyIdent) env.conEnv
      , typeDeps = mapUnionWith setUnion tydeps env.typeDeps
      , conDeps = mapInsertWith setUnion target
        (setOfSeq nameCmp [t.ident]) env.conDeps
      } in
    (env, DeclConDef {t with tyIdent = tyIdent})
end

lang TypeCheckUtestDecl = TypeCheckDecl + UtestDeclAst
  sem typeCheckDecl env =
  | DeclUtest t ->
    let test = typeCheckExpr env t.test in
    let expected = typeCheckExpr env t.expected in
    let tusing = optionMap (typeCheckExpr env) t.tusing in
    let tonfail = optionMap (typeCheckExpr env) t.tonfail in
    (switch (tusing, tonfail)
     case (Some tu, Some to) then
       unify env [infoTm tu]
         (tyarrows_ [tyTm test, tyTm expected, tybool_]) (tyTm tu);
       unify env [infoTm to]
         (tyarrows_ [tyTm test, tyTm expected, tystr_]) (tyTm to)
     case (Some tu, None _) then
       unify env [infoTm tu]
         (tyarrows_ [tyTm test, tyTm expected, tybool_]) (tyTm tu)
     case (None _, Some to) then
       unify env [infoTm to]
         (tyarrows_ [tyTm test, tyTm expected, tystr_]) (tyTm to)
     case (None _, None _) then
       unify env [infoTm test, infoTm expected] (tyTm test) (tyTm expected)
     end);
    ( env
    , DeclUtest {t with test = test, expected = expected, tusing = tusing, tonfail = tonfail}
    )
end

lang TypeCheckExtDecl = TypeCheckDecl + ExtDeclAst + ResolveType
  sem typeCheckDecl env =
  | DeclExt t ->
    -- TODO(vipa, 2023-06-15): Error if a RepType shows up in an external definition?
    let tyIdent = resolveType t.info env true t.tyIdent in
    let env = {env with varEnv = mapInsert t.ident tyIdent env.varEnv} in
    (env, DeclExt {t with tyIdent = tyIdent})
end

lang TypeCheckMExprDecls
  = TypeCheckRecLetsDecl
  + TypeCheckTypeDecl
  + TypeCheckDataDecl
  + TypeCheckUtestDecl
  + TypeCheckExtDecl
  + TypeCheckLetDecl
end
