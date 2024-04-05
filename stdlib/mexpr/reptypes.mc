include "ast.mc"
include "cmp.mc"
include "type-check.mc"
include "type.mc"
include "const-transformer.mc"
include "builtin.mc"
include "eval.mc"
include "lazy.mc"
include "heap.mc"
include "mexpr/annotate.mc"
include "multicore/pseq.mc"
include "sys.mc"
include "json.mc"
include "these.mc"

lang AnnotateSimple = HtmlAnnotator + AnnotateSources
end

-- TODO(vipa, 2023-12-13): Move to a more central location when we've
-- fully decided on what guarantees this function should have
let _symCmp = lam a. lam b. subi (sym2hash a) (sym2hash b)

lang LamRepTypesAnalysis = TypeCheck + LamAst + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmLam t ->
    let tyParam = substituteNewReprs env t.tyParam in
    let body = typeCheckExpr (_insertVar t.ident tyParam env) t.body in
    let tyLam = ityarrow_ t.info tyParam (tyTm body) in
    TmLam {t with body = body, tyParam = tyParam, ty = tyLam}
end

lang LetRepTypesAnalysis = TypeCheck + LetAst + SubstituteNewReprs + OpImplAst + OpDeclAst + NonExpansive + MetaVarDisableGeneralize
  sem typeCheckExpr env =
  | TmLet t ->
    let newLvl = addi 1 env.currentLvl in
    let isValue = nonExpansive true t.body in
    let shouldBeOp = if env.reptypes.inImpl
      then false
      else if isValue
        then containsRepr t.tyBody
        else false in
    if shouldBeOp then
      -- Replace with an OpDecl and OpImpl
      match withNewReprScope env (lam env.
        let env = {env with reptypes = {env.reptypes with inImpl = true}} in
        let tyBody = substituteNewReprs env t.tyBody in
        match stripTyAll tyBody with (vars, stripped) in
        let newTyVars = foldr (lam v. mapInsert v.0 (newLvl, v.1)) env.tyVarEnv vars in
        let env = {env with currentLvl = newLvl, tyVarEnv = newTyVars} in
        let body = typeCheckExpr env t.body in
        unify env [infoTm body] stripped (tyTm body);
        (body, tyBody))
      with ((body, tyBody), reprScope, delayedReprUnifications) in
      (if env.disableRecordPolymorphism then
        disableRecordGeneralize env.currentLvl tyBody else ());
      match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
      let env = _insertVar t.ident tyBody env in
      let env = {env with reptypes = {env.reptypes with opNamesInScope = mapInsert t.ident (None ()) env.reptypes.opNamesInScope}} in
      let inexpr = typeCheckExpr env t.inexpr in
      let ty = tyTm inexpr in
      TmOpDecl
      { info = t.info
      , ident = t.ident
      , tyAnnot = tyBody
      , ty = ty
      , inexpr = TmOpImpl
        { ident = t.ident
        , implId = negi 1
        , selfCost = 1.0
        , body = body
        , specType = tyBody
        , delayedReprUnifications = delayedReprUnifications
        , inexpr = inexpr
        , ty = ty
        , reprScope = reprScope
        , metaLevel = env.currentLvl
        , info = t.info
        }
      }
    else
      -- Keep it as a Let in the current reprScope, use normal inference
      let tyBody = substituteNewReprs env t.tyBody in
      -- NOTE(vipa, 2023-06-26): this is slightly changed from actual
      -- normal inference, because it uses the type set in `tyBody`
      -- and does not touch `tyAnnot`.
      match
        if isValue then
          match stripTyAll tyBody with (vars, stripped) in
          let newTyVars = foldr (lam v. mapInsert v.0 (newLvl, v.1)) env.tyVarEnv vars in
          let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVars} in
          let body = typeCheckExpr newEnv t.body in
          -- Unify the annotated type with the inferred one and generalize
          unify newEnv [infoTy t.tyAnnot, infoTm body] stripped (tyTm body);
          (if env.disableRecordPolymorphism then
            disableRecordGeneralize env.currentLvl tyBody else ());
          match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
          (body, tyBody)
        else
          let body = typeCheckExpr {env with currentLvl = newLvl} t.body in
          unify env [infoTm body] tyBody (tyTm body);
          -- TODO(aathn, 2023-05-07): Relax value restriction
          weakenMetaVars env.currentLvl tyBody;
          (body, tyBody)
        with (body, tyBody) in
      let inexpr = typeCheckExpr (_insertVar t.ident tyBody env) t.inexpr in
      TmLet {t with body = body,
                    tyBody = tyBody,
                    inexpr = inexpr,
                    ty = tyTm inexpr}
end

lang RecLetsRepTypesAnalysis = TypeCheck + RecLetsAst + MetaVarDisableGeneralize + RecordAst + OpImplAst + OpDeclAst + RepTypesHelpers + NonExpansive + SubstituteNewReprs + PropagateTypeAnnot + SubstituteUnknown + ResolveType
  sem typeCheckExpr env =
  | TmRecLets t ->
    let newLvl = addi 1 env.currentLvl in
    -- First: Generate a new environment containing the recursive bindings
    let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
      let tyAnnot = resolveType t.info env false b.tyBody in
      let tyAnnot = substituteNewReprs env tyAnnot in
      let tyBody = substituteUnknown t.info {env with currentLvl = newLvl} (Poly ()) tyAnnot in
      let vars = if nonExpansive true b.body then (stripTyAll tyBody).0 else [] in
      let newEnv = _insertVar b.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
      ((newEnv, newTyVars), {b with tyBody = tyBody})
    in
    match mapAccumL recLetEnvIteratee (env, mapEmpty nameCmp) t.bindings
    with ((recLetEnv, tyVars), bindings) in
    let newTyVarEnv =
      mapFoldWithKey (lam vs. lam v. lam k. mapInsert v (newLvl, k) vs) recLetEnv.tyVarEnv tyVars in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckBinding = lam b: RecLetBinding.
      let body =
        if nonExpansive true b.body then
          let newEnv = {recLetEnv with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
          match stripTyAll b.tyBody with (_, stripped) in
          let body = typeCheckExpr newEnv (propagateTyAnnot (b.body, b.tyBody)) in
          -- Unify the inferred type of the body with the annotated one
          unify newEnv [infoTy b.tyBody, infoTm body] stripped (tyTm body);
          body
        else
          let body = typeCheckExpr {recLetEnv with currentLvl = newLvl} b.body in
          unify recLetEnv [infoTy b.tyBody, infoTm body] b.tyBody (tyTm body);
          body
      in
      {b with body = body}
    in
    let bindings = map typeCheckBinding bindings in

    -- Third: Produce a new environment with generalized types
    let envIteratee = lam acc. lam b : RecLetBinding.
      match
        if nonExpansive true b.body then
          (if env.disableRecordPolymorphism then
             disableRecordGeneralize env.currentLvl b.tyBody else ());
          gen env.currentLvl acc.1 b.tyBody
        else
          weakenMetaVars env.currentLvl b.tyBody;
          (b.tyBody, [])
      with (tyBody, vars) in
      let newEnv = _insertVar b.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
      ((newEnv, newTyVars), {b with tyBody = tyBody})
    in
    match mapAccumL envIteratee (env, tyVars) bindings with ((env, _), bindings) in
    let inexpr = typeCheckExpr env t.inexpr in
    TmRecLets {t with bindings = bindings, inexpr = inexpr, ty = tyTm inexpr}
-- NOTE(vipa, 2024-04-22): This currently just uses the normal
-- type-checking for TmRecLets. In the end we want to infer when
-- something should be replaced with a letop and letimpl pair, but the
-- current analysis didn't do quite what we wanted, so we're leaving
-- it out for now.

--   sem typeCheckExpr env =
--   | TmRecLets t ->
--     let typeCheckRecLets = lam env. lam t.
--       let newLvl = addi 1 env.currentLvl in
--       -- Build env with the recursive bindings
--       let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
--         let tyBody = substituteNewReprs env b.tyBody in
--         let vars = if nonExpansive true b.body then (stripTyAll tyBody).0 else [] in
--         let newEnv = _insertVar b.ident tyBody acc.0 in
--         let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
--         ((newEnv, newTyVars), {b with tyBody = tyBody}) in
--       match mapAccumL recLetEnvIteratee (env, mapEmpty nameCmp) t.bindings
--         with ((recLetEnv, tyVars), bindings) in
--       let newTyVarEnv = mapFoldWithKey
--         (lam vs. lam v. lam. mapInsert v newLvl vs)
--         recLetEnv.tyVarEnv
--         tyVars in

--       -- Type check each body
--       let typeCheckBinding = lam b: RecLetBinding.
--         let body =
--           if nonExpansive true b.body then
--             let newEnv = {recLetEnv with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
--             match stripTyAll b.tyBody with (_, stripped) in
--             let body = typeCheckExpr newEnv b.body in
--             -- Unify the inferred type of the body with the annotated one
--             unify newEnv [infoTy b.tyAnnot, infoTm body] stripped (tyTm body);
--             body
--           else
--             let body = typeCheckExpr {recLetEnv with currentLvl = newLvl} b.body in
--             unify recLetEnv [infoTy b.tyAnnot, infoTm body] b.tyBody (tyTm body);
--             body
--         in {b with body = body} in
--       let bindings = map typeCheckBinding bindings in

--       -- Build env with generalized types
--       let envIteratee = lam acc. lam b : RecLetBinding.
--         match
--           if nonExpansive true b.body then
--             (if env.disableRecordPolymorphism then
--               disableRecordGeneralize env.currentLvl b.tyBody else ());
--             gen env.currentLvl acc.1 b.tyBody
--           else
--             weakenMetaVars env.currentLvl b.tyBody;
--             (b.tyBody, [])
--           with (tyBody, vars) in
--         let newEnv = _insertVar b.ident tyBody acc.0 in
--         let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
--         ((newEnv, newTyVars), {b with tyBody = tyBody}) in
--       match mapAccumL envIteratee (env, tyVars) bindings
--         with ((env, _), bindings) in

--       let inexpr = typeCheckExpr env t.inexpr in
--       { t with bindings = bindings
--              , inexpr = inexpr
--              , ty = tyTm inexpr
--       }
--     in

--     let shouldBeOp = if env.reptypes.inImpl then false else
--       if forAll (lam b. nonExpansive true b.body) t.bindings
--       then any (lam b. containsRepr b.tyBody) t.bindings
--       else false in
--     -- TODO(vipa, 2024-02-22): This translation doesn't quite do what
--     -- we want, because each function in the letrec gets generalized,
--     -- whereby any opuses inside have to satisfy a rigid
--     -- typevariable. For now we just don't translate rec lets to
--     -- letops, and we'll have to figure out how to do it later
--     let shouldBeOp = false in
--     if not shouldBeOp then TmRecLets (typeCheckRecLets env t) else
--     let bindingToBindingPair = lam b.
--       ( stringToSid (nameGetStr b.ident)
--       , TmVar
--         { ident = b.ident
--         , ty = tyunknown_
--         , info = t.info
--         , frozen = false
--         }
--       ) in
--     let opRecord = TmRecord
--       { bindings = mapFromSeq cmpSID (map bindingToBindingPair t.bindings)
--       , ty = tyunknown_
--       , info = t.info
--       } in
--     let newLvl = addi 1 env.currentLvl in
--     let implEnv = {env with currentLvl = newLvl, reptypes = {env.reptypes with inImpl = true}} in
--     match withNewReprScope implEnv (lam env. typeCheckRecLets env {t with inexpr = opRecord})
--       with (newT, reprScope, delayedReprUnifications) in
--     (if env.disableRecordPolymorphism
--       then disableRecordGeneralize env.currentLvl newT.ty
--       else ());
--     match gen env.currentLvl (mapEmpty nameCmp) newT.ty with (newTy, _) in
--     let recordName =
--       let ident = (head newT.bindings).ident in
--       nameSym (concat (nameGetStr ident) "_etc") in
--     let inexpr =
--       let opNamesInScope = foldl
--         (lam acc. lam b. mapInsert b.ident (Some (recordName, stringToSid (nameGetStr b.ident))) acc)
--         env.reptypes.opNamesInScope
--         newT.bindings in
--       let opNamesInScope = mapInsert recordName (None ()) opNamesInScope in
--       let env = _insertVar recordName newTy env in
--       let env = {env with reptypes = {env.reptypes with opNamesInScope = opNamesInScope}} in
--       typeCheckExpr env t.inexpr in
--     let ty = tyTm inexpr in
--     TmOpDecl
--     { info = t.info
--     , ident = recordName
--     , tyAnnot = newTy
--     , ty = ty
--     , inexpr = TmOpImpl
--       { ident = recordName
--       , implId = negi 1
--       , selfCost = 1.0
--       , body = TmRecLets newT
--       , specType = newTy
--       , delayedReprUnifications = delayedReprUnifications
--       , inexpr = inexpr
--       , ty = ty
--       , reprScope = reprScope
--       , metaLevel = env.currentLvl
--       , info = t.info
--       }
--     }
end

lang VarRepTypesAnalysis = TypeCheck + VarAst + OpVarAst + RepTypesHelpers + SubstituteNewReprs + NeverAst + MatchAst + NamedPat + RecordPat
  sem typeCheckExpr env =
  | TmVar t ->
    let opInfo = mapLookup t.ident env.reptypes.opNamesInScope in
    match opInfo with Some (Some (rName, label)) then
      -- NOTE(vipa, 2023-06-16): "Desugar" the variable to an access
      -- of the record it was changed into
      let tmp = nameSym "tmp" in
      let newTm = TmMatch
        { target = TmVar {ident = rName, ty = tyunknown_, frozen = false, info = t.info}
        , pat = PatRecord
          { info = t.info
          , ty = tyunknown_
          , bindings = mapInsert label (PatNamed {ident = PName tmp, info = t.info, ty = tyunknown_})
            (mapEmpty cmpSID)
          }
          -- TODO(vipa, 2023-06-16): I believe this handles frozen
          -- variables correctly, but it should probably be checked
          -- more closely
        , thn = TmVar {ident = tmp, ty = tyunknown_, frozen = t.frozen, info = t.info}
        , els = TmNever {info = t.info, ty = tyunknown_}
        , ty = tyunknown_
        , info = t.info
        } in
      typeCheckExpr env newTm
    else
    match mapLookup t.ident env.varEnv with Some ty then
      let ty =
        if t.frozen then ty
        else inst t.info env.currentLvl ty
      in
      if optionIsSome opInfo then
        -- NOTE(vipa, 2023-06-16): We're looking at an operator,
        -- insert new reprs and record this fact
        let ty = substituteNewReprs env ty in
        TmOpVar
          { ident = t.ident
          , ty = ty
          , info = t.info
          , frozen = t.frozen
          , scaling = 1.0
          }
      else TmVar {t with ty = ty}
    else
      let msg = join [
        "* Encountered an unbound variable: ",
        nameGetStr t.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle [t.info] msg
end

lang OpImplRepTypesAnalysis = TypeCheck + OpImplAst + ResolveType + SubstituteNewReprs + RepTypesHelpers + ApplyReprSubsts
  sem typeCheckExpr env =
  | TmOpImpl x ->
    let typeCheckBody = lam env.
      let env = {env with reptypes = {env.reptypes with inImpl = true}} in
      let newLvl = addi 1 env.currentLvl in
      let specType = substituteNewReprs env x.specType in
      let newEnv = {env with currentLvl = newLvl} in
      let reprType = applyReprSubsts newEnv specType in
      match stripTyAll reprType with (vars, reprType) in
      let newTyVars = foldr (lam v. mapInsert v.0 (newLvl, v.1)) newEnv.tyVarEnv vars in
      let newEnv = {newEnv with tyVarEnv = newTyVars} in
      match captureDelayedReprUnifications newEnv
        (lam. typeCheckExpr newEnv x.body)
        with (body, delayedReprUnifications) in
      unify newEnv [infoTy reprType, infoTm body] reprType (tyTm body);
      { x with body = body
      , delayedReprUnifications = delayedReprUnifications
      , specType = specType
      }
    in
    match withNewReprScope env (lam env. typeCheckBody env)
      with (x, reprScope, []) in
    let inexpr = typeCheckExpr env x.inexpr in
    TmOpImpl
    { x with reprScope = reprScope
    , metaLevel = env.currentLvl
    , inexpr = inexpr
    , ty = tyTm inexpr
    }
end

-- NOTE(vipa, 2023-06-26): The RepTypes analysis is essentially
-- type-checking, except we want actual type-/checking/, not
-- inference; we want to have precise type annotations to start. We
-- thus replace the type-checking of AST nodes with a tyAnnot field
-- with a version that uses the inferred field instead (TmLam, TmLet,
-- TmRecLets).
--
-- Additionally, we find TmLets and TmRecLets that are values and
-- mention collections and replace them with an TmOpDecl and TmOpImpl
-- each, to make it easier to swap representations, as well as get
-- smaller individual problems to solve.
--
-- Finally, we replace the TmVars that reference TmOpDecls with
-- TmOpVars.
lang RepTypesAnalysis = LamRepTypesAnalysis + LetRepTypesAnalysis + RecLetsRepTypesAnalysis + VarRepTypesAnalysis + OpImplRepTypesAnalysis + OpDeclTypeCheck + RepTypesUnify + OpVarTypeCheck + ReprDeclTypeCheck
end

lang MExprRepTypesAnalysis = MExprTypeCheckMost + RepTypesAnalysis + MExprPrettyPrint + RepTypesPrettyPrint
end

lang RepTypesFragments = ReprTypeAst + ReprSubstAst + ReprTypeUnify + OpDeclAst + OpDeclSym + OpDeclTypeCheck + TyWildAst + TyWildUnify + RepTypesPrettyPrint
end

lang RepTypesShallowSolverInterface = OpVarAst + OpImplAst + UnifyPure + AliasTypeAst
  -- NOTE(vipa, 2023-07-05): Potential global state shared between
  -- individual solving processes
  syn SolverGlobal a =
  sem initSolverGlobal : all a. () -> SolverGlobal a

  -- NOTE(vipa, 2023-10-25): Solver state passed along each branch of
  -- the AST.
  syn SolverBranch a =
  sem initSolverBranch : all a. SolverGlobal a -> SolverBranch a
  sem initSolverTopQuery : all a. SolverGlobal a -> SolverTopQuery a

  -- NOTE(vipa, 2023-10-25): A solution to some particular op
  syn SolverSolution a =
  -- NOTE(vipa, 2023-10-25): A set of solutions to some particular op
  syn SolverTopQuery a =

  type OpImpl a =
    { implId: ImplId
    , op : Name
    , opUses : [TmOpVarRec]
    , selfCost : OpCost
    , uni : Unification
    , specType : Type
    , originalSpecType : Type
    , reprScope : Int
    , metaLevel : Int
    , info : Info
    -- NOTE(vipa, 2023-07-06): A token used by the surrounding system
    -- to carry data required to reconstruct a solved AST.
    , token : a
    }
  sem cmpOpImpl : all a. OpImpl a -> OpImpl a -> Int
  sem cmpOpImpl a = | b ->
    subi a.implId b.implId

  -- NOTE(vipa, 2023-10-25): There's a new `OpImpl` in scope
  sem addImpl : all a. SolverGlobal a -> SolverBranch a -> OpImpl a -> SolverBranch a

  -- NOTE(vipa, 2023-07-06): This is the only time the surrounding
  -- system will ask for a solution from a solution set. Every other
  -- solution will be acquired through concretizeSolution.
  sem addOpUse : all a. Bool -> SolverGlobal a -> SolverBranch a -> SolverTopQuery a -> TmOpVarRec -> (SolverBranch a, SolverTopQuery a)

  -- NOTE(vipa, 2023-11-03): Create some form of debug output for the
  -- branch state
  sem debugBranchState : all a. SolverGlobal a -> SolverBranch a -> ()
  -- NOTE(vipa, 2023-11-11): Create some form of debug output for a
  -- particular (top-)solution
  sem debugSolution : all a. SolverGlobal a -> [SolverSolution a] -> String

  -- NOTE(vipa, 2023-10-25): Solve the top-level, i.e., find a
  -- `SolverSolution` per previous call to `addOpUse`. The string is a
  -- path to a file in which to read/write a previous/new solution.
  sem topSolve : all a. Bool -> Option String -> SolverGlobal a -> SolverTopQuery a -> [SolverSolution a]

  -- NOTE(vipa, 2023-10-25): Solve the top-level fully, i.e., find a
  -- `SolverSolution` per previous call to `addOpUse`, and find all
  -- possible such allocations.
  sem topSolveAll : all a. Bool -> SolverGlobal a -> SolverTopQuery a -> [[SolverSolution a]]

  -- NOTE(vipa, 2023-07-05): The returned list should have one picked
  -- solution per element in `opUses`. The returned `ImplId` should be
  -- the greatest `ImplId` in use in this solution.
  sem concretizeSolution : all a. SolverGlobal a -> SolverSolution a -> (a, ImplId, [SolverSolution a])

  -- NOTE(vipa, 2023-10-25): An arbitrary ordering over solutions
  sem cmpSolution : all a. SolverSolution a -> SolverSolution a -> Int

  sem opImplDebugJson : all a. OpImpl a -> JsonValue
  sem opImplDebugJson = | impl ->
    recursive let removeAliases = lam ty.
      match ty with TyAlias x
      then removeAliases x.content
      else smap_Type_Type removeAliases ty in
    let env = pprintEnvEmpty in
    match pprintVarName env impl.op with (env, name) in
    match getTypeStringCode 0 env (removeAliases impl.specType) with (env, specType) in
    let convertOpUse = lam env. lam opUse.
      match pprintVarName env opUse.ident with (env, ident) in
      match getTypeStringCode 0 env (removeAliases opUse.ty) with (env, ty) in
      let json = JsonObject (mapFromSeq cmpString
        [ ("op", JsonString ident)
        , ("ty", JsonString ty)
        ]) in
      (env, json) in
    match mapAccumL convertOpUse env impl.opUses with (env, opUses) in
    match unificationToDebug "" env impl.uni with (env, uni) in
    let json = JsonObject (mapFromSeq cmpString
      [ ("name", JsonString name)
      , ("specType", JsonString specType)
      , ("opUses", JsonArray opUses)
      , ("uni", JsonArray (map (lam x. JsonString x) (strSplit "\n" uni)))
      ]) in
    json
end

type VarMap v = {reprs : Map Symbol v, metas : Map Name v}
let varMapEmpty : all v. VarMap v = unsafeCoerce
  { metas = mapEmpty nameCmp
  , reprs = mapEmpty _symCmp
  }
let varMapSingleton
  : all a. Either Symbol Name -> a -> VarMap a
  = lam k. lam v. switch k
    case Left sym then
      {varMapEmpty with reprs = mapInsert sym v varMapEmpty.reprs}
    case Right name then
      {varMapEmpty with metas = mapInsert name v varMapEmpty.metas}
    end
let varMapEq
  : all v. (v -> v -> Bool) -> VarMap v -> VarMap v -> Bool
  = lam eq. lam a. lam b.
    if not (mapEq eq a.reprs b.reprs) then false else
    if not (mapEq eq a.metas b.metas) then false else
    true
let varMapMap
  : all a. all b. (a -> b) -> VarMap a -> VarMap b
  = lam f. lam a.
    { metas = mapMap f a.metas
    , reprs = mapMap f a.reprs
    }
let varMapHasMeta
  : all a. Name -> VarMap a -> Bool
  = lam n. lam m. mapMem n m.metas
let varMapHasRepr
  : all a. Symbol -> VarMap a -> Bool
  = lam s. lam m. mapMem s m.reprs
let varMapDifference
  : all a. all b. VarMap a -> VarMap b -> VarMap a
  = lam a. lam b.
    { metas = mapDifference a.metas b.metas
    , reprs = mapDifference a.reprs b.reprs
    }
let varMapUnion
  : all a. VarMap a -> VarMap a -> VarMap a
  = lam a. lam b.
    { metas = mapUnion a.metas b.metas
    , reprs = mapUnion a.reprs b.reprs
    }
let varMapIntersect
  : all a. all b. VarMap a -> VarMap b -> VarMap a
  = lam a. lam b.
    { metas = mapIntersectWith (lam a. lam. a) a.metas b.metas
    , reprs = mapIntersectWith (lam a. lam. a) a.reprs b.reprs
    }
let varMapSubset
  : all a. all b. VarMap a -> VarMap b -> Bool
  = lam a. lam b.
    if mapAllWithKey (lam k. lam. mapMem k b.reprs) a.reprs
    then mapAllWithKey (lam k. lam. mapMem k b.metas) a.metas
    else false
let varMapIsEmpty
  : all a. VarMap a -> Bool
  = lam a. if mapIsEmpty a.metas then mapIsEmpty a.reprs else false
let varMapMinBy
  : all a. (a -> a -> Int) -> VarMap a -> Option (Either Symbol Name, a)
  = lam cmp. lam a.
    let pickSmallest : all k. Option (k, a) -> k -> a -> Option (k, a) = lam opt. lam k. lam a.
      match opt with Some (pk, pa) then
        if lti (cmp a pa) 0 then Some (k, a) else opt
      else Some (k, a) in
    let res = mapFoldWithKey (lam acc. lam k. lam v. pickSmallest acc (Left k) v) (None ()) a.reprs in
    let res = mapFoldWithKey (lam acc. lam k. lam v. pickSmallest acc (Right k) v) res a.metas in
    res

lang VarAccessHelpers = Ast + ReprTypeAst + MetaVarTypeAst
  sem getMetaHere : Type -> Option MetaVarRec
  sem getMetaHere =
  | TyMetaVar x ->
    match deref x.contents with Unbound x
    then Some x
    else None ()
  | _ -> None ()

  sem getReprHere : Type -> Option {sym : Symbol, scope : Int}
  sem getReprHere =
  | TyRepr x ->
    match deref (botRepr x.repr) with BotRepr x
    then Some x
    else None ()
  | _ -> None ()

  sem getVarsInType : {metaLevel : Int, scope : Int} -> VarMap Int -> Type -> VarMap Int
  sem getVarsInType filter acc = | ty ->
    let addMeta = lam x. if geqi x.level filter.metaLevel
      then mapInsert x.ident x.level acc.metas
      else acc.metas in
    let addRepr = lam x. if geqi x.scope filter.scope
      then mapInsert x.sym x.scope acc.reprs
      else acc.reprs in
    let metas = optionMapOr acc.metas addMeta (getMetaHere ty) in
    let reprs = optionMapOr acc.reprs addRepr (getReprHere ty) in
    sfold_Type_Type (getVarsInType filter) {metas = metas, reprs = reprs} ty

  sem typeMentionsVarInVarMap : all a. VarMap a -> Type -> Bool
  sem typeMentionsVarInVarMap m = | ty ->
    if optionMapOr false (lam x. varMapHasMeta x.ident m) (getMetaHere ty) then true else
    if optionMapOr false (lam x. varMapHasRepr x.sym m) (getReprHere ty) then true else
    sfold_Type_Type (lam found. lam ty. if found then found else typeMentionsVarInVarMap m ty) false ty
end

lang LocallyNamelessStuff = MetaVarTypeAst + ReprTypeAst + AllTypeAst + VarTypeAst + UnifyPure
  type NamelessState =
    { metas : [Name]
    , vars : [Name]
    , reprs : [Symbol]
    }
  type NamelessMapping =
    { var : Map Name Name
    , repr : Map Symbol (Symbol, Int)
    , meta : Map Name (Name, Int)
    }
  sem applyLocallyNamelessMappingTy : NamelessMapping -> Type -> Type
  sem applyLocallyNamelessMappingTy mapping =
  | ty -> smap_Type_Type (applyLocallyNamelessMappingTy mapping) ty
  | TyAll x ->
    let ident = mapLookupOr x.ident x.ident mapping.var in
    TyAll {x with ident = ident, ty = applyLocallyNamelessMappingTy mapping x.ty}
  | TyVar x ->
    let ident = mapLookupOr x.ident x.ident mapping.var in
    TyVar {x with ident = ident}
  | ty & TyMetaVar _ ->
    switch unwrapType ty
    case TyMetaVar x then
      match deref x.contents with Unbound u in
      match mapLookupOr (u.ident, u.level) u.ident mapping.meta with (ident, level) in
      TyMetaVar {x with contents = ref (Unbound {u with ident = ident, level = level})}
    case ty then applyLocallyNamelessMappingTy mapping ty
    end
  | TyRepr x ->
    match deref (botRepr x.repr) with BotRepr r in
    match mapLookupOr (r.sym, r.scope) r.sym mapping.repr with (sym, scope) in
    TyRepr {x with repr = ref (BotRepr {r with sym = sym, scope = scope}), arg = applyLocallyNamelessMappingTy mapping x.arg}

  sem applyLocallyNamelessMappingUni : NamelessMapping -> Unification -> Option Unification
  sem applyLocallyNamelessMappingUni mapping = | uni ->
    substituteInUnification
      (lam x. mapLookupOr x x.0 mapping.meta)
      (lam x. mapLookupOr x x.0 mapping.repr)
      (applyLocallyNamelessMappingTy mapping)
      uni

  sem applyLocallyNamelessMappingReprPuf : all a. NamelessMapping -> PureUnionFind Symbol a -> PureUnionFind Symbol a
  sem applyLocallyNamelessMappingReprPuf mapping = | puf ->
    (pufMapAll _symCmp
      (lam k. optionGetOr k (mapLookup k.0 mapping.repr))
      (lam x. x)
      (lam. error "applyLocallyNamelessMappingReprPuf")
      puf).puf

  sem mkLocallyNameless : all a. NamelessState -> Type -> {state : NamelessState, forward : NamelessMapping, backward : NamelessMapping, res : Type}
  sem mkLocallyNameless nameless = | ty ->
    type NlSmall x =
      { forward : Map x (x, Int)
      , reverse : Map x (x, Int)
      , nextIdx : Int
      , vals : [x]
      } in
    type NlEnv =
      { metas : NlSmall Name
      , vars : NlSmall Name
      , reprs : NlSmall Symbol
      } in
    let nextNameless : all x. (() -> x) -> NlSmall x -> (NlSmall x, x)
      = lam mkNew. lam st.
        let st = if lti st.nextIdx (length st.vals)
          then st
          else {st with vals = snoc st.vals (mkNew ())} in
        ({st with nextIdx = addi 1 st.nextIdx}, get st.vals st.nextIdx) in
    let getNameless : all x. (() -> x) -> (x, Int) -> NlSmall x -> (NlSmall x, (x, Int))
      = lam mkNew. lam x. lam st.
        match mapLookup x.0 st.forward with Some x then (st, x) else
        -- NOTE(vipa, 2023-11-13): The use of `uniFilter` later
        -- depends on the level/scope returned here is strictly less
        -- than the current level/scope of the impl. This is true for
        -- -1, so we go with that.
        match nextNameless mkNew st with (st, newX) in
        ( { st with forward = mapInsert x.0 (newX, negi 1) st.forward
          , reverse = mapInsert newX x st.reverse
          }
        , (newX, negi 1)
        )
    in
    recursive let locallyNameless : NlEnv -> Type -> (NlEnv, Type) = lam acc. lam ty.
      switch unwrapType ty
      case TyAll x then
        match getNameless (lam. nameSym "bound") (x.ident, 0) acc.vars with (vars, (ident, _)) in
        let acc = {acc with vars = vars} in
        match locallyNameless acc x.ty with (acc, ty) in
        (acc, TyAll {x with ident = ident, ty = ty})
      case TyVar x then
        match getNameless (lam. nameSym "unbound") (x.ident, 0) acc.vars with (vars, (ident, _)) in
        (acc, TyVar {x with ident = ident})
      case ty & TyRepr x then
        match deref (botRepr x.repr) with BotRepr r in
        match getNameless gensym (r.sym, r.scope) acc.reprs with (reprs, (sym, scope)) in
        let acc = {acc with reprs = reprs} in
        match locallyNameless acc x.arg with (acc, arg) in
        (acc, TyRepr {x with repr = ref (BotRepr {r with sym = sym, scope = scope}), arg = arg})
      case TyMetaVar x then
        switch deref x.contents
        case Unbound u then
          match getNameless (lam. nameSym "meta") (u.ident, u.level) acc.metas with (metas, (ident, level)) in
          let acc = {acc with metas = metas} in
          (acc, TyMetaVar {x with contents = ref (Unbound {u with ident = ident, level = level})})
        case Link ty then
          locallyNameless acc ty
        end
      case ty then
        smapAccumL_Type_Type locallyNameless acc ty
      end in
    let nlEnv =
      { metas =
        { forward = mapEmpty nameCmp
        , reverse = mapEmpty nameCmp
        , nextIdx = 0
        , vals = nameless.metas
        }
      , reprs =
        { forward = mapEmpty _symCmp
        , reverse = mapEmpty _symCmp
        , nextIdx = 0
        , vals = nameless.reprs
        }
      , vars =
        { forward = mapEmpty nameCmp
        , reverse = mapEmpty nameCmp
        , nextIdx = 0
        , vals = nameless.vars
        }
      } in
    match locallyNameless nlEnv ty with (nlEnv, ty) in
    { state = {metas = nlEnv.metas.vals, reprs = nlEnv.reprs.vals, vars = nlEnv.vars.vals}
    , forward = {meta = nlEnv.metas.forward, repr = nlEnv.reprs.forward, var = mapMap (lam x. x.0) nlEnv.vars.forward}
    , backward = {meta = nlEnv.metas.reverse, repr = nlEnv.reprs.reverse, var = mapMap (lam x. x.0) nlEnv.vars.reverse}
    , res = ty
    }
end

type SolutionDebugTarget
con SDTNone : () -> SolutionDebugTarget
con SDTStdout : () -> SolutionDebugTarget
con SDTFunc : (Int -> String -> ()) -> SolutionDebugTarget
type ReprSolverOptions =
  { debugBranchState : Bool
  , debugFinalSolution : SolutionDebugTarget
  , debugSolveProcess : Bool
  , debugSolveTiming : Bool
  , debugImpls : Bool
  , solveAll : Bool
  , solutionCacheFile : Option String
  }

let defaultReprSolverOptions : ReprSolverOptions =
  { debugBranchState = false
  , debugFinalSolution = SDTNone ()
  , debugSolveProcess = false
  , debugSolveTiming = false
  , debugImpls = false
  , solveAll = false
  , solutionCacheFile = None ()
  }

lang RepTypesSolveAndReconstruct = RepTypesShallowSolverInterface + OpImplAst + VarAst + LetAst + OpDeclAst + ReprDeclAst + ReprTypeAst + UnifyPure + AliasTypeAst + PrettyPrint + ReprSubstAst + RepTypesHelpers
  -- Top interface, meant to be used outside --
  sem reprSolve : ReprSolverOptions -> Expr -> [Expr]
  sem reprSolve options = | tm ->
    let global = initSolverGlobal () in
    -- NOTE(vipa, 2023-10-25): Right now we do not handle nested impls
    -- in the collection phase
    let initState =
      { branch = initSolverBranch global
      , topQuery = initSolverTopQuery global
      , nextId = 0
      , options = options
      } in
    let preCollect = wallTimeMs () in
    match collectForReprSolve global initState tm with (state, tm) in
    let postCollect = wallTimeMs () in
    let pickedSolutions = if options.solveAll
      then topSolveAll options.debugSolveProcess global state.topQuery
      else [topSolve options.debugSolveProcess options.solutionCacheFile global state.topQuery] in
    let postTopSolve = wallTimeMs () in
    (switch options.debugFinalSolution
     case SDTNone _ then ()
     case SDTStdout _ then
       for_ pickedSolutions (lam s. printLn (debugSolution global s))
     case SDTFunc f then
       iteri (lam i. lam s. f i (debugSolution global s)) pickedSolutions
     end);
    -- NOTE(vipa, 2023-10-25): The concretization phase *does* handle
    -- nested impls, so it shouldn't have to be updated if the
    -- collection phase is improved later on
    let concretizeOne = lam pickedSolutions.
      let initState =
        { remainingSolutions = pickedSolutions
        , requests = mapEmpty subi
        , requestsByOpAndSol = mapEmpty (lam a. lam b.
          let res = nameCmp a.0 b.0 in
          if neqi res 0 then res else
          cmpSolution a.1 b.1)
        , global = global
        } in
      match concretizeAlt initState tm with (state, tm) in
      mapFoldWithKey (lam. lam id. lam deps. printLn (join ["(compiler error) Left-over dep, id: ", int2string id, ", num deps: ", int2string (length deps)])) () state.requests;
      tm in
    let preConcretize = wallTimeMs () in
    let exprs = map concretizeOne pickedSolutions in
    let postConcretize = wallTimeMs () in
    (if options.debugSolveTiming then
      printLn (join
        [ "Collect time: ", float2string (subf postCollect preCollect), "ms\n"
        , "Top-solve time: ", float2string (subf postTopSolve postCollect), "ms\n"
        , "Concretize time: ", float2string (subf postConcretize preConcretize), "ms\n"
        ])
     else ());
    map removeReprExpr exprs

  -- Collecting and solving sub-problems --
  type CollectState =
    { branch : SolverBranch Expr
    , topQuery : SolverTopQuery Expr
    , nextId : Int
    , options : ReprSolverOptions
    }

  sem collectForReprSolve
    : SolverGlobal Expr
    -> CollectState
    -> Expr
    -> (CollectState, Expr)
  sem collectForReprSolve global state =
  | tm -> smapAccumL_Expr_Expr (collectForReprSolve global) state tm
  | tm & TmOpVar x ->
    match addOpUse state.options.debugSolveProcess global state.branch state.topQuery x with (branch, topQuery) in
    ({state with branch = branch, topQuery = topQuery}, tm)
  | TmOpImpl x ->
    let implId = state.nextId in
    let state = {state with nextId = addi state.nextId 1} in
    recursive let addSubstsToUni = lam oUni. lam ty.
      switch unwrapType ty
      case TySubst x then
        match unwrapType x.arg with TyRepr r then
          let oUni = optionBind oUni (lam uni. unifySetReprPure uni r.repr x.subst) in
          addSubstsToUni oUni r.arg
        else errorSingle [x.info] "Substitutions must be applied to repr-types."
      case ty then
        sfold_Type_Type addSubstsToUni oUni ty
      end in
    let opImpl =
      { implId = implId
      , op = x.ident
      , opUses = findOpUses [] x.body
      , selfCost = x.selfCost
      -- NOTE(vipa, 2023-11-04): repr unification cannot fail until
      -- repr substitutions have been applied, which they haven't here
      , uni =
        let uni = optionGetOrElse (lam. error "Compiler error in reptype solver")
          (optionFoldlM
            (lam acc. lam pair. unifyReprPure acc pair.0 pair.1)
            (emptyUnification ())
            x.delayedReprUnifications) in
        let oUni = addSubstsToUni (Some uni) x.specType in
        optionGetOrElse (lam. errorSingle [infoTy x.specType] "This type makes inconsistent repr substitutions.")
          oUni
      , specType = removeReprSubsts x.specType
      , originalSpecType = x.specType
      , reprScope = x.reprScope
      , metaLevel = x.metaLevel
      , info = x.info
      , token = x.body
      } in
    (if state.options.debugImpls then
      printLn (json2string (opImplDebugJson opImpl))
     else ());
    let newBranch = addImpl global state.branch opImpl in
    match collectForReprSolve global {state with branch = newBranch} x.inexpr
      with (newState, inexpr) in
    -- NOTE(vipa, 2023-10-25): Here we restore the old branch, since
    -- any new solutions attained along the new branch might use this
    -- new impl, which isn't in scope in whatever we're returning to
    ( {newState with branch = state.branch}
    , TmOpImpl
      { x with implId = implId
      , inexpr = inexpr
      }
    )

  sem findOpUses : [TmOpVarRec] -> Expr -> [TmOpVarRec]
  sem findOpUses acc =
  | tm -> sfold_Expr_Expr findOpUses acc tm
  | TmOpVar x -> snoc acc x
  | TmOpImpl x -> errorSingle [x.info]
    "This impl is nested within another impl, which the current solver doesn't handle."

  -- Insert selected solutions --
  type ConcreteState =
    { remainingSolutions : [SolverSolution Expr]
    -- NOTE(vipa, 2023-10-25): ImplId is set up in such a way that the
    -- most recent impl to be added is the largest, i.e., we can find
    -- the insertion point of a concrete solution by inserting it by
    -- the greatest `ImplId` used in the solution
    , requests : Map ImplId [{solName : Name, body : Expr}]
    , requestsByOpAndSol : Map (Name, SolverSolution Expr) Name
    , global : SolverGlobal Expr
    }

  sem lookupSolName : Name -> SolverSolution Expr -> ConcreteState -> (ConcreteState, Name)
  sem lookupSolName op sol = | state ->
    match mapLookup (op, sol) state.requestsByOpAndSol
    with Some name then (state, name) else
      let name = nameSetNewSym op in
      match concretizeSolution state.global sol with (token, implId, sols) in
      match concretizeAlt {state with remainingSolutions = sols} token
        with (newState, body) in
      let state =
        { newState with remainingSolutions = state.remainingSolutions
        , requests = mapInsertWith concat
          implId
          [{solName = name, body = body}]
          newState.requests
        , requestsByOpAndSol = mapInsert (op, sol) name newState.requestsByOpAndSol
        } in
      (state, name)

  sem concretizeAlt : ConcreteState -> Expr -> (ConcreteState, Expr)
  sem concretizeAlt state =
  | tm -> smapAccumL_Expr_Expr concretizeAlt state tm
  | TmOpDecl {inexpr = inexpr} | TmReprDecl {inexpr = inexpr} ->
    concretizeAlt state inexpr
  | TmOpVar x ->
    match state.remainingSolutions with [sol] ++ remainingSolutions in
    match lookupSolName x.ident sol state with (state, name) in
    ( {state with remainingSolutions = remainingSolutions}
    , TmVar {ident = name, ty = x.ty, info = x.info, frozen = x.frozen}
    )
  | TmOpImpl x ->
    match concretizeAlt state x.inexpr with (state, inexpr) in
    let reqs = mapLookupOr [] x.implId state.requests in
    let wrap = lam req. lam inexpr. TmLet
      { ident = req.solName
      , tyAnnot = tyunknown_
      , tyBody = tyTm req.body
      , body = req.body
      , inexpr = inexpr
      , ty = tyTm inexpr
      , info = x.info
      } in
    let res = foldr wrap inexpr reqs in
    let state = {state with requests = mapRemove x.implId state.requests} in
    (state, res)

  -- TODO(vipa, 2023-07-07): This swaps all `TyRepr`s with
  -- `TyUnknown`. This *should* be good enough for the OCaml backend,
  -- but isn't as good as it could be; we should be able to insert
  -- precise types according to what reprs were chosen. I leave that
  -- for later.
  sem removeReprExpr : Expr -> Expr
  sem removeReprExpr = | tm ->
    let tm = smap_Expr_Expr removeReprExpr tm in
    let tm = smap_Expr_Type removeReprTypes tm in
    let tm = smap_Expr_TypeLabel removeReprTypes tm in
    tm

  sem removeReprTypes : Type -> Type
  sem removeReprTypes =
  | ty -> smap_Type_Type removeReprTypes ty
  -- NOTE(vipa, 2023-10-26): Aliases can contain TyRepr in `content`
  -- without showing them in `display`, at which point it gets
  -- confusing if we keep the same alias, even though the content is
  -- different from the type alias definition suggests it is.
  | TyAlias x -> removeReprTypes x.content
  | TyRepr x -> TyUnknown {info = x.info}
end

type SolInterface constraint childInfo env =
  -- NOTE(vipa, 2023-12-12): We given `c = approxOr a b` we assume the
  -- following holds:
  -- * a -> c
  -- * b -> c
  -- Notably we do *not* assume that `c -> a || b` holds.
  { approxOr : constraint -> constraint -> constraint
  -- NOTE(vipa, 2023-12-12): Are two constraints equivalent (i.e., `eq
  -- a b` should be true if a <-> b holds)
  , eq : constraint -> constraint -> Bool
  -- NOTE(vipa, 2023-12-08): Update the constraints of a parent and
  -- child because one or both of them have changed. The two functions
  -- differ by which constraint-space they're called in: fromAbove is
  -- called in the constraint space of the child, fromBelow is called
  -- in the constraint space of the parent.
  , constrainFromAbove
    : {parent : constraint, here : constraint, path : [childInfo]}
    -> Option {parentChanged : Bool, hereChanged : Bool, res : constraint}
  , constrainFromBelow
    : {here : constraint, child : constraint, path : [childInfo]}
    -> Option {hereChanged : Bool, childChanged : Bool, res : constraint}
  -- NOTE(vipa, 2023-12-08): Take a constraint and a set of dependent
  -- subproblems, split the constraint into conjunctions, and
  -- partition the subproblems such that they are independent
  -- regardless of which of the new constraints is chosen. If it's not
  -- useful to make a split here, return `None`.
  , split
    : all x. constraint
    -> [{spaceSize : Int, maxCost : Float, minCost : Float, token : x}]  -- TODO(vipa, 2023-12-17): Provide enough information to actually partition by type here
    -> Option ([[x]], [constraint])
  , pprintConstraint : String -> env -> constraint -> (env, String)
  , pprintChildInfo : String -> env -> childInfo -> (env, String)
  -- NOTE(vipa, 2023-12-19): Merge the given list of constraints, if
  -- they are compatible. If they are not, compute which constraints
  -- conflict. The latter should be represented as a mapping from
  -- constraint-index (in the input list) to the indices with
  -- conflicting constraints.
  , mergeAndFindIncompat : [constraint] -> Either (Map Int (Set Int)) constraint
  }

type SolTree constraint childInfo a
type AndComponents constraint childInfo a
con AndDep : all constraint. all childInfo. all a. [{scale : Float, child : SolTree constraint childInfo a}] -> AndComponents constraint childInfo a
con AndIndep : all constraint. all childInfo. all a. [SolTree constraint childInfo a] -> AndComponents constraint childInfo a
type STAndRec a b constraint childInfo =
  { construct : [b] -> a
  , components : AndComponents constraint childInfo b
  , constraint : constraint
  , childInfo : Option childInfo
  , selfCost : Float
  , minCost : Float
  , maxCost : Float
  , spaceSize : Int
  }
con STAnd : all a. all b. all constraint. all childInfo.
  STAndRec a b constraint childInfo -> SolTree constraint childInfo a
con STConstraintTransform : all a. all constraint. all childInfo.
  { child : SolTree constraint childInfo a
  -- NOTE(vipa, 2023-12-13): If either of these functions fail
  -- (returning `None`), then the subtree at this point is dead.
  , fromAbove : constraint -> Option constraint
  , fromBelow : constraint -> Option constraint
  } -> SolTree constraint childInfo a
con STOr : all a. all constraint. all childInfo.
  { alternatives : [SolTree constraint childInfo a]
  , minCost : Float
  , maxCost : Float
  , spaceSize : Int
  } -> SolTree constraint childInfo a
con STSingle : all a. all constraint. all childInfo.
  { res : a
  , cost : Float
  , constraint : constraint
  , childInfo : Option childInfo
  } -> SolTree constraint childInfo a

let andComponentsToList : all constraint. all childInfo. all a.
  AndComponents constraint childInfo a -> [SolTree constraint childInfo a]
  = lam comp. switch comp
    case AndIndep x then x
    case AndDep x then
      map (lam x. x.child) x
    end

type SolTreeInput constraint childInfo a
con STIAndDep : all a. all b. all constraint. all childInfo.
  { components : [{scale : Float, child : SolTreeInput constraint childInfo b}]
  , childInfo : childInfo
  , cost : Float
  , construct : [b] -> a
  , constraint : constraint
  } -> SolTreeInput constraint childInfo a
con STIConstraintTransform : all a. all constraint. all childInfo.
  { child : SolTreeInput constraint childInfo a
  -- NOTE(vipa, 2023-12-13): If either of these functions fail
  -- (returning `None`), then the subtree at this point is dead.
  , fromAbove : constraint -> Option constraint
  , fromBelow : constraint -> Option constraint
  } -> SolTreeInput constraint childInfo a
con STIOr : all a. all constraint. all childInfo.
  { alternatives : [SolTreeInput constraint childInfo a]
  } -> SolTreeInput constraint childInfo a

recursive let solTreeMap : all a. all b. all constraint. all childInfo.
  (a -> b) -> SolTreeInput constraint childInfo a -> SolTreeInput constraint childInfo b
  = lam f. lam tree. switch tree
    case STIAndDep x then STIAndDep
      { components = x.components
      , childInfo = x.childInfo
      , cost = x.cost
      , construct = lam bs. f (x.construct bs)
      , constraint = x.constraint
      }
    case STIConstraintTransform x then STIConstraintTransform
      { child = solTreeMap f x.child
      , fromAbove = x.fromAbove
      , fromBelow = x.fromBelow
      }
    case STIOr x then STIOr
      { alternatives = map (solTreeMap f) x.alternatives
      }
    end
end

let solTreeConvert : all constraint. all a. all childInfo. SolTreeInput constraint childInfo a -> SolTree constraint childInfo a
  = lam sti.
    recursive let work = lam sti. switch sti
      case STIAndDep x then
        let transformChild = lam acc. lam child.
          match work child.child with ((min, max, space), newChild) in
          ( (addf acc.0 (mulf child.scale min), addf acc.1 (mulf child.scale max), muli acc.2 space)
          , {scale = child.scale, child = newChild}
          ) in
        match mapAccumL transformChild (x.cost, x.cost, 1) x.components with (acc, components) in
        ( acc
        , STAnd
          { construct = x.construct
          , constraint = x.constraint
          , components = AndDep components
          , childInfo = Some x.childInfo
          , selfCost = x.cost
          , minCost = acc.0
          , maxCost = acc.1
          , spaceSize = acc.2
          }
        )
      case STIConstraintTransform x then
        match work x.child with (acc, child) in
        ( acc
        , STConstraintTransform
          { child = child
          , fromAbove = x.fromAbove
          , fromBelow = x.fromBelow
          }
        )
      case STIOr {alternatives = [alt] ++ alts} then
        let transformAlt = lam acc. lam alt.
          match work alt with ((min, max, space), alt) in
          ((minf acc.0 min, maxf acc.1 max, addi acc.2 space), alt) in
        match work alt with (acc, alt) in
        match mapAccumL transformAlt acc alts with (acc, alts) in
        ( acc
        , STOr
          { alternatives = cons alt alts
          , minCost = acc.0
          , maxCost = acc.1
          , spaceSize = acc.2
          }
        )
      case STIOr {alternatives = []} then
        let min = divf 1.0 0.0 in
        let max = negf min in
        ( (min, max, 0)
        , STOr
          { alternatives = []
          , minCost = min
          , maxCost = max
          , spaceSize = 0
          }
        )
      end
    in (work sti).1

let debugSolTree
  : all a. all constraint. all env. all childInfo.
  (String -> env -> childInfo -> (env, String))
  -> (String -> env -> constraint -> (env, String))
  -> env
  -> SolTree constraint childInfo a
  -> (env, JsonValue)
  = lam pchild. lam pconstraint. lam env. lam tree.
    let pconstraint = lam indent. lam env. lam constraint.
      match pconstraint indent env constraint with (env, constraintLines) in
      (env, JsonArray (map (lam x. JsonString x) (strSplit "\n" constraintLines))) in
    let commonFields = lam fields.
      let res =
        [ ("min", JsonFloat fields.min)
        , ("max", JsonFloat fields.max)
        , ("size", JsonInt fields.size)
        ] in
      (env, res) in
    recursive let work = lam env. lam tree.
      switch tree
      case STAnd x then
        match commonFields {min = x.minCost, max = x.maxCost, size = x.spaceSize} with (env, common) in
        match pconstraint "" env x.constraint with (env, constraint) in
        match optionMapAccum (pchild "") env x.childInfo with (env, chinfo) in
        let chinfo = optionGetOr "" chinfo in
        match
          switch x.components
          case AndDep components then
            let f = lam env. lam comp. work env comp.child in
            mapAccumL f env components
          case AndIndep components then
            mapAccumL work env components
          end
        with (env, components) in
        let fields = mapFromSeq cmpString (concat common
          [ ("type", JsonString "and")
          , ("dep", JsonBool (match x.components with AndDep _ then true else false))
          , ("info", JsonString chinfo)
          , ("constraint", constraint)
          , ("components", JsonArray components)
          ]) in
        (env, JsonObject fields)
      case STConstraintTransform x then
        match work env x.child with (env, child) in
        let fields = mapFromSeq cmpString
          [ ("type", JsonString "con-trans")
          , ("child", child)
          ] in
        (env, JsonObject fields)
      case STOr x then
        match commonFields {min = x.minCost, max = x.maxCost, size = x.spaceSize} with (env, common) in
        match mapAccumL work env x.alternatives with (env, alternatives) in
        let fields = mapFromSeq cmpString (concat common
          [ ("type", JsonString "or")
          , ("alternatives", JsonArray alternatives)
          ]) in
        (env, JsonObject fields)
      case STSingle x then
        match optionMapAccum (pchild "") env x.childInfo with (env, chinfo) in
        let chinfo = optionGetOr "" chinfo in
        match pconstraint "" env x.constraint with (env, constraint) in
        let fields = mapFromSeq cmpString
          [ ("type", JsonString "single")
          , ("cost", JsonFloat x.cost)
          , ("info", JsonString chinfo)
          , ("constraint", constraint)
          ] in
        (env, JsonObject fields)
      end
    in work env tree

type STMeta =
  { min : Float
  , max : Float
  , size : Int
  }

recursive let getMeta : all constraint. all a. all childInfo. SolTree constraint childInfo a -> STMeta =
  lam tree. switch tree
    case STAnd x then {min = x.minCost, max = x.maxCost, size = x.spaceSize}
    case STConstraintTransform x then getMeta x.child
    case STOr x then {min = x.minCost, max = x.maxCost, size = x.spaceSize}
    case STSingle x then {min = x.cost, max = x.cost, size = 1}
    end
end

let orMetaCombine
  : all childInfo. all constraint. all a. STMeta
  -> SolTree constraint childInfo a
  -> STMeta
  = lam acc. lam tree.
    let res = getMeta tree in
    { min = minf acc.min res.min
    , max = maxf acc.max res.max
    , size = addi acc.size res.size
    }
let andMetaEmpty = lam cost. {min = cost, max = cost, size = 1}
let andMetaCombineIndep = lam acc. lam tree.
  let res = getMeta tree in
  { min = addf acc.min res.min
  , max = addf acc.max res.max
  , size = muli acc.size res.size
  }
let andMetaCombine
  : all constraint. all a. all childInfo. STMeta
  -> {scale : Float, child : SolTree constraint childInfo a}
  -> STMeta
  = lam acc. lam item.
    let res = getMeta item.child in
    { min = addf acc.min (mulf item.scale res.min)
    , max = addf acc.max (mulf item.scale res.max)
    , size = muli acc.size res.size
    }

let exploreCombosMinFirst
  : all a. all res. all c. all b.
  (a -> Float)
  -> (a -> c)
  -> ([a] -> c -> Option b)
  -> ([c] -> Either (Map Int (Set Int)) c)
  -> [LStream a]
  -> LStream b
  = lam cost. lam constraint. lam construct. lam mergeConstraints. lam axes.
    type Combo =
      { cost : Float
      , combo : [Int]
      , here : [a]
      , tails : [LStream a]
      } in
    let cmpId = seqCmp subi in
    let cmpByCost = lam a. lam b.
      if ltf a.cost b.cost then negi 1 else
      if gtf a.cost b.cost then 1 else
      0 in
    type State =
      { queue : Heap Combo
      , consideredCombos : Set [Int]
      } in
    let individualSets : [Set Int] =
      create (length axes) (lam i. setInsert i (setEmpty subi)) in

    let optionMapAccumM3 : all a1. all b1. all c1. all a2. all b2. all c2. all acc.
      (acc -> a1 -> b1 -> c1 -> Option (acc, a2, b2, c2)) -> acc -> [a1] -> [b1] -> [c1] -> Option (acc, [a2], [b2], [c2])
      = lam f. lam acc. lam as. lam bs. lam cs.
        recursive let work = lam acc. lam a2s. lam b2s. lam c2s. lam as. lam bs. lam cs.
          match (as, bs, cs) with ([a] ++ as, [b] ++ bs, [c] ++ cs) then
            match f acc a b c with Some (acc, a, b, c) then
              work acc (snoc a2s a) (snoc b2s b) (snoc c2s c) as bs cs
            else None ()
          else Some (acc, a2s, b2s, c2s)
        in work acc [] [] [] as bs cs
    in

    let init = lam.
      match optionMapM lazyStreamUncons axes with Some axes then
        match unzip axes with (here, tails) in
        let initCombo =
          { cost = foldl (lam acc. lam item. addf acc (cost item)) 0.0 here
          , combo = map (lam. 0) axes
          , here = here
          , tails = tails
          } in
        { queue = heapSingleton initCombo
        , consideredCombos = setEmpty cmpId
        }
      else {queue = heapEmpty, consideredCombos = setEmpty cmpId}
    in

    let addSuccessors : Combo -> Map Int (Set Int) -> State -> State
      = lam combo. lam conflicts. lam state.
        let trySteps : Set Int -> Option Combo = lam idxesToStep.
          let tryStep = lam c. lam idx. lam here. lam tail.
            if setMem idx idxesToStep then
              match lazyStreamUncons tail with Some (new, tail) then
                Some (addf (subf c (cost here)) (cost new), addi idx 1, new, tail)
              else None ()
            else Some (c, idx, here, tail)
          in
          let reCombo = lam quad.
            match quad with (cost, combo, here, tails) in
            {combo = combo, cost = cost, here = here, tails = tails} in
          let res = optionMapAccumM3 tryStep combo.cost combo.combo combo.here combo.tails in
          let res = optionMap reCombo res in
          optionFilter (lam combo. not (setMem combo.combo state.consideredCombos)) res in
        let alts = if mapIsEmpty conflicts
          then individualSets
          else setToSeq (setOfSeq setCmp (mapValues conflicts)) in
        let newCombos = mapOption trySteps alts in
        { queue = heapAddMany cmpByCost newCombos state.queue
        , consideredCombos = foldl (lam acc. lam combo. setInsert combo.combo acc) state.consideredCombos newCombos
        }
    in

    recursive let step : State -> Option (() -> State, b) = lam state.
      match heapPop cmpByCost state.queue with Some (combo, queue) then
        let state = {state with queue = queue} in
        switch mergeConstraints (map constraint combo.here)
        case Left conflicts then
          step (addSuccessors combo conflicts state)
        case Right constraint then
          match construct combo.here constraint with Some b then
            Some (lam. addSuccessors combo (mapEmpty subi) state, b)
          else step (addSuccessors combo (mapEmpty subi) state)
        end
      else None ()
    in

    lazyStreamLaziest step init

let solTreeLazyMaterialize : all constraint. all childInfo. all env. all a.
  SolInterface constraint childInfo env -> env -> SolTree constraint childInfo a -> LStream a
  = lam fs. lam env. lam tree.
    type Item a = {cost : Float, constraint : constraint, res : a} in
    let cmpItem : all a. Item a -> Item a -> Int = lam a. lam b.
      if ltf a.cost b.cost then negi 1 else
      if gtf a.cost b.cost then 1 else
      0 in
    recursive let work
      : all a. SolTree constraint childInfo a -> LStream (Item a)
      = lam tree. switch tree
        case STAnd x then
          let children = switch x.components
            case AndDep components then
              let f = lam comp.
                lazyStreamMap (lam res. {res with cost = mulf comp.scale res.cost}) (work comp.child) in
              map f components
            case AndIndep components then
              map work components
            end in
          let getCost = lam item. item.cost in
          let getConstraint = lam item. item.constraint in
          let construct = lam children. lam constraint.
            let f = lam res.
              { cost = foldl (lam acc. lam item. addf acc item.cost) x.selfCost children
              , constraint = res.res
              , res = x.construct (map (lam x. x.res) children)
              } in
            optionMap f (fs.constrainFromBelow {here = x.constraint, child = constraint, path = []}) in
          exploreCombosMinFirst getCost getConstraint construct fs.mergeAndFindIncompat children
        case STConstraintTransform x then
          let transform = lam trip.
            optionMap (lam new. {trip with constraint = new}) (x.fromBelow trip.constraint) in
          lazyStreamMapOption transform (work x.child)
        case STOr x then
          lazyStreamMergeMin cmpItem (map work x.alternatives)
        case STSingle x then
          lazyStreamSingleton {cost = x.cost, constraint = x.constraint, res = x.res}
        end in
    lazyStreamMap (lam x. x.res) (work tree)

let solTreeMaterializeCheapest
  : all constraint. all a. all env. all childInfo. SolInterface constraint childInfo env -> SolTree constraint childInfo a -> Option a
  = lam fs. lam tree.
    recursive let work : all a. [childInfo] -> SolTree constraint childInfo a -> Option (constraint, a) = lam path. lam tree. switch tree
      case STAnd x then
        let path = optionMapOr path (lam item. snoc path item) x.childInfo in
        let f = lam acc. lam child.
          optionBind (work path child)
            (lam res. match res with (constraint, child) in
              optionBind (fs.constrainFromBelow {here = acc.0, child = constraint, path = path})
                (lam res. Some (res.res, snoc acc.1 child))) in
        let res = andComponentsToList x.components in
        let res = optionFoldlM f (x.constraint, []) res in
        optionMap (lam res. (res.0, x.construct res.1)) res
      case STConstraintTransform x then
        optionBind (work path x.child)
          (lam res. match res with (constraint, child) in
            optionMap (lam c. (c, child)) (x.fromBelow constraint))
      case STOr {alternatives = [item] ++ items} then
        let min = foldl
          (lam min. lam new. let newCost = (getMeta new).min in if ltf newCost min.0 then (newCost, new) else min)
          ((getMeta item).min, item)
          items in
        work path min.1
      case STSingle x then
        Some (x.constraint, x.res)
      end
    in optionMap (lam x. x.1) (work [] tree)

let trySplitAnd
  : all a. all b. all constraint. all childInfo. all env.
  SolInterface constraint childInfo env
  -> STAndRec a b constraint childInfo
  -> Option (SolTree constraint childInfo a)
  = lam fs. lam x. switch x.components
    case AndDep components then
      let prepComponent = lam i. lam comp.
        let meta = getMeta comp.child in
        { minCost = meta.min
        , maxCost = meta.max
        , spaceSize = meta.size
        , token = i
        } in
      match fs.split x.constraint (mapi prepComponent components) with Some (partitionIdxes, constraints) then
        let mkPartition = lam idxes.
          let components = map (lam idx. get components idx) idxes in
          (foldl andMetaCombine (andMetaEmpty 0.0) components, components) in
        let partitions = map mkPartition partitionIdxes in
        let buildAlt = lam constraint.
          let mkPartition = lam construct. lam chinfo. lam partition.
            match partition with (meta, components) in
            STAnd
            { components = AndDep components
            , construct = construct
            , constraint = constraint
            , childInfo = chinfo
            , selfCost = 0.0
            , minCost = meta.min
            , maxCost = meta.max
            , spaceSize = meta.size
            } in
          let indep = match partitions with [partition]
            then mkPartition x.construct x.childInfo partition
            else STAnd
              { construct = lam partitions.
                let merge = lam acc. lam idxes. lam sols.
                  foldl2 (lam acc. lam idx. lam sol. mapInsert idx sol acc) acc idxes sols in
                let merged = foldl2 merge (mapEmpty subi) partitionIdxes partitions in
                x.construct (mapValues merged)
              , components = AndIndep (map (mkPartition (lam x. x) (None ())) partitions)
              , constraint = constraint
              , childInfo = x.childInfo
              , selfCost = x.selfCost
              , minCost = x.minCost
              , maxCost = x.maxCost
              , spaceSize = x.spaceSize
              } in
          indep in
        let or = STOr
          { alternatives = map buildAlt constraints
          , minCost = x.minCost
          , maxCost = x.maxCost
          , spaceSize = muli x.spaceSize (length partitions)
          } in
        Some or
      else None ()
    case AndIndep _ then None ()
    end

let solTreeMaterializeOrSplit
  : all constraint. all a. all env. all childInfo. SolInterface constraint childInfo env -> SolTree constraint childInfo a -> Option (Either (SolTree constraint childInfo a) a)
  = lam fs. lam tree.
    type Res a = Option (Either (SolTree constraint childInfo a) (constraint, a)) in
    let allRightOrOneLeft : all a. all b. (a -> Option (Either a b)) -> [a] -> Option (Either [a] [b])
      = lam f. lam full.
        recursive let work = lam bs. lam l.
          match l with [x] ++ l then
            switch f x
            case Some (Left left) then
              match splitAt full (length bs) with (pre, [_] ++ post) then
                Some (Left (concat pre (cons left post)))
              else error "Compiler error: failed splitAt"
            case Some (Right b) then
              work (snoc bs b) l
            case None _ then
              None ()
            end
          else Some (Right bs)
        in work [] full in
    recursive let work : all a. [childInfo] -> SolTree constraint childInfo a -> Res a = lam path. lam tree. switch tree
      case STAnd x then
        let path = optionMapOr path (lam item. snoc path item) x.childInfo in
        let wrapSplit : Unknown -> Res a = lam components.
          let components = match x.components with AndDep prev
            then AndDep (zipWith (lam prev. lam child. {prev with child = child}) prev components)
            else AndIndep components in
          Some (Left (STAnd {x with components = components})) in
        let materialize : Unknown -> Res a = lam sols.
          let tryConstrain = lam acc. lam pair.
            let res = fs.constrainFromBelow {here = acc, child = pair.0, path = path} in
            optionMap (lam x. x.res) res in
          match optionFoldlM tryConstrain x.constraint sols with Some constraint then
            Some (Right (constraint, x.construct (map (lam x. x.1) sols)))
          else None () in
        let splitHere : () -> Res a = lam.
          let dprint = lam.
            match mapAccumL (fs.pprintChildInfo "| ") (unsafeCoerce pprintEnvEmpty) path with (_, path) in
            printLn (join ["Split at this path: ", strJoin ", " path]) in
          optionMap (lam x. dprint (); Left x) (trySplitAnd fs x) in

        let res = allRightOrOneLeft (work path) (andComponentsToList x.components) in
        let res = optionBind res (eitherEither wrapSplit materialize) in
        optionOrElse splitHere res
      case STConstraintTransform x then
        let wrapSplit : Unknown -> Res a = lam child.
          Some (Left (STConstraintTransform {x with child = child})) in
        let transform : Unknown -> Res a = lam pair.
          match pair with (constraint, sol) in
          optionMap (lam constraint. Right (constraint, sol)) (x.fromBelow constraint) in
        optionBind (work path x.child) (eitherEither wrapSplit transform)
      case STOr x then
        let cmpf = lam a. lam b. if ltf a b then negi 1 else if gtf a b then 1 else 0 in
        -- NOTE(vipa, 2023-12-18): Mergesort because we expect the
        -- list to be sorted most of the time
        match mergeSort (lam a. lam b. cmpf (getMeta a).min (getMeta b).min) x.alternatives with [alt] ++ alts then
          let wrapSplit = lam alt. STOr {x with alternatives = cons alt alts} in
          optionMap (eitherMapLeft wrapSplit) (work path alt)
        else error "Compiler error: empty 'or' in materalize"
      case STSingle x then
        Some (Right (x.constraint, x.res))
      end
    in optionMap (eitherMapRight (lam x. x.1)) (work [] tree)

let solTreePropagate
  : all constraint. all a. all env. all childInfo. SolInterface constraint childInfo env -> env -> Bool -> SolTree constraint childInfo a -> Option (SolTree constraint childInfo a)
  = lam fs. lam env. lam forceDepth. lam tree.
    let optionPredicated : all a. all b. all c. Option a -> (a -> Option b) -> (Option b -> Option c) -> Option c
      = lam opt. lam pred. lam next.
        match opt with Some opt then
          match pred opt with opt & Some _
          then next opt
          else None ()
        else next (None ()) in
    let asSingleton : SolTree constraint childInfo a -> Option a = lam tree.
      match tree with STSingle x then Some x.res else None () in
    recursive let getConstraint : all a. SolTree constraint childInfo a -> constraint = lam tree. switch tree
      case STAnd x then x.constraint
      case STConstraintTransform x then
        optionGetOrElse (lam. error "Compiler error: fromBelow failed on a live child") (x.fromBelow (getConstraint x.child))
      case STOr x then
        match x.alternatives with [alt] ++ alts then
          foldl (lam acc. lam alt. fs.approxOr acc (getConstraint alt)) (getConstraint alt) alts
        else error "Compiler error: alternative with no children in getConstraint"
      case STSingle x then x.constraint
      end in
    recursive
      let propagateAndList
        : all a. Bool -> [childInfo] -> constraint -> [SolTree constraint childInfo a] -> Option (Option constraint, [SolTree constraint childInfo a])
        = lam forceDepth. lam path. lam constraint. lam list.
          recursive let work = lam previouslyChanged. lam constraint. lam list.
            let f = lam acc. lam child.
              match workNodeDebug (if forceDepth then not previouslyChanged else false) path (Some acc.0) child with Some (newConstraint, child) then
                optionPredicated newConstraint (lam child. fs.constrainFromBelow {here = acc.0, child = child, path = path})
                  (lam res.
                    let res = optionGetOr {hereChanged = false, childChanged = false, res = acc.0} res in
                    -- NOTE(vipa, 2023-12-15): We ignore
                    -- `childChanged` with the assumption that it's
                    -- due to filtering that happened between the two
                    -- points in the tree
                    let changed = if acc.2 then true else res.hereChanged in
                    Some (res.res, snoc acc.1 child, changed))
              else None () in
            match optionFoldlM f (constraint, [], false) list with Some (constraint2, list, changed) then
              if changed
              then work true constraint2 list
              else Some (if previouslyChanged then Some constraint2 else None (), list)
            else None ()
          in work false constraint list
      let workNodeDebug
        : all a. Bool -> [childInfo] -> Option constraint -> SolTree constraint childInfo a -> Option (Option constraint, SolTree constraint childInfo a)
        = lam forceDepth. lam path. lam constraintM. lam tree.
          let res = workNodeReal forceDepth path constraintM tree in
          res
      let workNodeReal
        : all a. Bool -> [childInfo] -> Option constraint -> SolTree constraint childInfo a -> Option (Option constraint, SolTree constraint childInfo a)
        = lam forceDepth. lam path. lam constraintM. lam tree. switch tree
          case STOr {alternatives = []} then
            printLn "empty or";
            None ()
          case STAnd x then
            printLn "and";
            let path = optionMapOr path (lam item. snoc path item) x.childInfo in
            optionPredicated constraintM (lam parent. fs.constrainFromAbove {parent = parent, here = x.constraint, path = path})
              (lam resM.
                let res = optionGetOr {parentChanged = false, hereChanged = false, res = x.constraint} resM in
                let constraint = res.res in
                let propagateDown = if forceDepth then true else res.hereChanged in
                let belowResults =
                  if propagateDown then
                    switch x.components
                    case AndDep components then
                      let res = propagateAndList forceDepth path constraint (map (lam x. x.child) components) in
                      let rebuild = lam prev. lam child.
                        {scale = prev.scale, child = child} in
                      let juggle = lam res.
                        let rebuilt = zipWith rebuild components res.1 in
                        (res.0, foldl andMetaCombine (andMetaEmpty x.selfCost) rebuilt, AndDep rebuilt) in
                      optionMap juggle res
                    case AndIndep components then
                      let juggle = lam res.
                        (res.0, foldl andMetaCombineIndep (andMetaEmpty x.selfCost) components, AndIndep components) in
                      optionMap juggle (propagateAndList forceDepth path constraint components)
                    end
                  else Some (None (), {min = x.minCost, max = x.maxCost, size = x.spaceSize}, x.components) in
                match belowResults with Some (newConstraint, meta, components) then
                  printLn (join ["=== Post belowResults:"]);
                  (match newConstraint with Some new then
                    printLn (fs.pprintConstraint "| " env new).1
                   else printLn "No new constraint from below");
                  let constraint = optionGetOr constraint newConstraint in
                  printLn (fs.pprintConstraint "| " env constraint).1;
                  let new =
                    match optionMapM asSingleton (andComponentsToList components) with Some singles
                    then STSingle
                      { res = x.construct singles
                      , cost = meta.max
                      , constraint = constraint
                      , childInfo = x.childInfo
                      }
                    else STAnd
                      { x with components = components
                      , constraint = constraint
                      , minCost = meta.min
                      , maxCost = meta.max
                      , spaceSize = meta.size
                      } in
                  Some (optionOr newConstraint (if res.parentChanged then Some constraint else None ()), new)
                else None ())
          case STConstraintTransform x then
            printLn "constraint transform";
            match optionMapAccum (fs.pprintConstraint "| ") env constraintM with (env, pre) in
            optionPredicated constraintM x.fromAbove
              (lam transformed.
                match optionMapAccum (fs.pprintConstraint "| ") env transformed with (env, post) in
                (match (pre, post) with (Some pre, Some post) then
                  printLn pre;
                  printLn post
                 else ());
                optionBind (workNodeDebug forceDepth path transformed x.child)
                  (lam res.
                    match res with (belowConstraint, child) in
                    optionPredicated belowConstraint x.fromBelow
                      (lam transformedGoingUp.
                        let tree = match child with STSingle single
                          then
                            let constraint = optionGetOrElse
                              (lam. optionGetOrElse (lam. error "Compiler error: fromBelow failed on the constraint of a single") (x.fromBelow single.constraint))
                              transformedGoingUp in
                            STSingle {single with constraint = constraint}
                          else STConstraintTransform {x with child = child} in
                        Some (transformedGoingUp, tree))))
          case STOr x then
            printLn "non-empty or";
            let combine = lam acc. lam item. (or acc.0 item.0, fs.approxOr acc.1 item.1, concat acc.2 item.2) in
            match mapOption (workNodeDebug forceDepth path constraintM) x.alternatives with everything & ([item] ++ items) then
              let changed = if optionIsSome item.0 then true else any (lam item. optionIsSome item.0) items in
              let flattened = join (map (lam x. match x.1 with STOr x then x.alternatives else [x.1]) everything) in
              let constraintM =
                if changed then
                  let constraint = optionGetOrElse (lam. getConstraint item.1) item.0 in
                  let merge =
                    lam acc. lam item. fs.approxOr acc (optionGetOrElse (lam. getConstraint item.1) item.0) in
                  Some (foldl merge constraint items)
                else None () in
              let new = if null items
                then item.1
                else
                  let meta = foldl (lam acc. lam item. orMetaCombine acc item.1) (getMeta item.1) items in
                  STOr
                  { alternatives = flattened
                  , minCost = meta.min
                  , maxCost = meta.max
                  , spaceSize = meta.size
                  } in
              Some (constraintM, new)
            else None ()
          case tree & STSingle x then
            printLn "single";
            match constraintM with Some constraint then
            let path = optionMapOr path (lam item. snoc path item) x.childInfo in
              match fs.constrainFromAbove {parent = constraint, here = x.constraint, path = path} with Some res then
                let tree = if res.hereChanged
                  then STSingle {x with constraint = res.res}
                  else tree in
                let toAbove = if res.parentChanged
                  then Some res.res
                  else None () in
                Some (toAbove, tree)
              else None ()
            else Some (None (), tree)
          end
    in optionMap (lam x. x.1) (workNodeDebug forceDepth [] (None ()) tree)

let solTreeSplitOnce : all a. all constraint. all childInfo. all env.
  SolInterface constraint childInfo env -> SolTree constraint childInfo a -> SolTree constraint childInfo a
  = lam fs. lam tree.
    let optionMapFirst : all a. (a -> Option a) -> [a] -> Option [a] = lam f. lam full.
      recursive let work = lam idx. lam l.
        match l with [x] ++ rest then
          match f x with Some x then
            match splitAt full idx with (pre, [_] ++ post)
            then Some (concat pre (cons x rest))
            else error "Impossible"
          else work (addi idx 1) rest
        else None ()
      in work 0 full in
    recursive let work = lam tree. switch tree
      case STSingle _ then
        None ()
      case STConstraintTransform x then
        optionMap (lam child. STConstraintTransform {x with child = child}) (work x.child)
      -- NOTE(vipa, 2023-12-15): The "Or" and "And" cases are the
      -- primary points to steer where we try to split first
      case STOr x then
        let cmpf = lam a. lam b. if leqf a b then negi 1 else if gtf a b then 1 else 0 in
        let alts = sort (lam a. lam b. subi (getMeta a).size (getMeta b).size) x.alternatives in
        optionMap (lam alts. STOr {x with alternatives = alts}) (optionMapFirst work alts)
      case STAnd x then
        let splitHere = switch x.components
          case AndDep components then
            let prepComponent = lam i. lam comp.
              let meta = getMeta comp.child in
              { minCost = meta.min
              , maxCost = meta.max
              , spaceSize = meta.size
              , token = i
              } in
            match fs.split x.constraint (mapi prepComponent components) with Some (partitionIdxes, constraints) then
              let mkPartition = lam idxes.
                let components = map (lam idx. get components idx) idxes in
                (foldl andMetaCombine (andMetaEmpty 0.0) components, components) in
              let partitions = map mkPartition partitionIdxes in
              let buildAlt = lam constraint.
                let mkPartition = lam construct. lam chinfo. lam partition.
                  match partition with (meta, components) in
                  STAnd
                  { components = AndDep components
                  , construct = construct
                  , constraint = constraint
                  , childInfo = chinfo
                  , selfCost = 0.0
                  , minCost = meta.min
                  , maxCost = meta.max
                  , spaceSize = meta.size
                  } in
                let indep = match partitions with [partition]
                  then mkPartition x.construct x.childInfo partition
                  else STAnd
                    { construct = lam partitions.
                      let merge = lam acc. lam idxes. lam sols.
                        foldl2 (lam acc. lam idx. lam sol. mapInsert idx sol acc) acc idxes sols in
                      let merged = foldl2 merge (mapEmpty subi) partitionIdxes partitions in
                      x.construct (mapValues merged)
                    , components = AndIndep (map (mkPartition (lam x. x) (None ())) partitions)
                    , constraint = constraint
                    , childInfo = x.childInfo
                    , selfCost = x.selfCost
                    , minCost = x.minCost
                    , maxCost = x.maxCost
                    , spaceSize = x.spaceSize
                    } in
                indep in
              let or = STOr
                { alternatives = map buildAlt constraints
                , minCost = x.minCost
                , maxCost = x.maxCost
                , spaceSize = muli x.spaceSize (length partitions)
                } in
              Some or
            else None ()
          case AndIndep _ then None ()
          end in
        if optionIsSome splitHere then splitHere else -- NOTE(vipa, 2023-12-15): Early exit

        -- NOTE(vipa, 2023-12-15): Try to split a child
        -- TODO(vipa, 2023-12-15): Could prioritize which child to attempt first maybe?
        switch x.components
        case AndDep components then
           let components = optionMapFirst
             (lam x. optionMap (lam new. {x with child = new}) (work x.child))
             components in
           optionMap (lam components. STAnd {x with components = AndDep components}) components
        case AndIndep components then
          let components = optionMapFirst work components in
          optionMap (lam components. STAnd {x with components = AndIndep components}) components
        end
      end in
    match work tree with Some tree
    then tree
    else error "Couldn't find a point to split the soltree"

lang SolTreeSolver
  sem solTreeMinimumSolution : all a. all constraint. all env. all childInfo.
    Bool -> SolInterface constraint childInfo env -> env -> SolTreeInput constraint childInfo a -> Option a
end

lang SolTreeLazySolver = SolTreeSolver
  sem solTreeMinimumSolution debug fs env = | tree ->
    let tree = solTreeConvert tree in
    let propagate = lam tree. solTreePropagate fs env true tree in
    let lazyMaterialize = lam tree. solTreeLazyMaterialize fs env tree in
    let extractSolution = lam stream. optionMap (lam x. x.0) (lazyStreamUncons stream) in
    optionBind (optionMap lazyMaterialize (propagate tree)) extractSolution
end

lang SolTreeSoloSolver = SolTreeSolver
  sem solTreeMinimumSolution debug fs env = | tree ->
    let tree = solTreeConvert tree in
    recursive
      let materialize = lam splits. lam tree.
        (if debug then
          printLn (join ["=== Solving step ", int2string splits, ", post-propagate ==="]);
          printLn (json2string (debugSolTree fs.pprintChildInfo fs.pprintConstraint env tree).1)
         else ());
        switch solTreeMaterializeOrSplit fs tree
        case Some (Right sol) then printLn (join ["Done after ", int2string splits, " splits"]); Some sol
        case Some (Left tree) then propagate (addi splits 1) tree
        case None _ then None ()
        end
      let propagate = lam splits. lam tree.
        (if debug then
          printLn (join ["=== Solving step ", int2string splits, ", pre-propagate ==="]);
          printLn (json2string (debugSolTree fs.pprintChildInfo fs.pprintConstraint env tree).1)
         else ());
        match solTreePropagate fs env true tree with Some tree
        then materialize splits tree
        else None ()
    in propagate 0 tree
end

type Dep
con InDep : () -> Dep
con Dep : () -> Dep

type RTHistory
con HStart : String -> RTHistory
con HStep : {label : String, prev : RTHistory} -> RTHistory
con HAndConstruct : {label : String, children : [RTHistory], prev : RTHistory} -> RTHistory
con HOrConstruct : {label : String, parent : RTHistory, prev : RTHistory} -> RTHistory
con HFlatten : {label : String, parent : RTHistory, children : [RTHistory]} -> RTHistory

-- relevant: a set of variables relevant to *the parent* of each
--   node. Can be used to filter `constraint` and `approx`, but also
--   to partition independent nodes of an "and"
-- constraint: the precisely known constraints that are true if this
--   node is in the final solution. Can always be applied to children,
--   but can only be applied to a parent from an `RTSingle`.
-- approx: which vars are known to be equal if this node is in the
--   final solution, and the set of possible values if
--   known. Equalities and sets of values can always be applied to
--   children, sets of values can always be applied to parents, and
--   equalities can only be applied to parents from an `RTSingle`.
-- var: the type of a variable tracked in `approx`. There may be more
--   kinds of variables not tracked by `approx`, `constraint` is
--   always the true state of things.
-- val: the type a values that can be assigned to `var`
--   variables. Should be a simple value type, in particular, it
--   mustn't contain further `var`s that might need to be tracked.
-- ident: some kind of identifying information. Not populated for
--   newly created nodes during solving, thus it is optional. Also not
--   required to be precise; two distinct nodes may have the same
--   value for their ident.
type RepTree relevant constraint var val ident a
type RTSingleRec a constraint var val relevant ident =
  { value : a
  , cost : Float
  , relevantHere : relevant
  , relevantAbove : relevant
  , constraint : constraint
  , approx : PureUnionFind var (Set val)
  , ident : Option ident
  , history : RTHistory
  }
con RTSingle : all a. all constraint. all var. all val. all relevant. all ident.
  RTSingleRec a constraint var val relevant ident
  -> RepTree relevant constraint var val ident a
type RTAndRec a b constraint var val relevant ident =
  { children : [{scale : Float, val : RepTree relevant constraint var val ident a}]
  , selfCost : Float
  , dep : Dep
  , construct : constraint -> [a] -> b
  , constraint : constraint
  , relevantHere : relevant
  , relevantAbove : relevant
  , approx : PureUnionFind var (Set val)
  , ident : Option ident
  , history : RTHistory
  }
con RTAnd : all a. all b. all constraint. all var. all val. all relevant. all ident.
  RTAndRec a b constraint var val relevant ident
  -> RepTree relevant constraint var val ident b
type RTOrRec a b constraint var val relevant ident =
  { others : [RepTree relevant constraint var val ident a]
  , singles : [RTSingleRec a constraint var val relevant ident]
  , selfCost : Float
  , construct : constraint -> a -> b
  , constraint : constraint
  , relevantHere : relevant
  , relevantAbove : relevant
  , approx : PureUnionFind var (Set val)
  , ident : Option ident
  , history : RTHistory
  }
con RTOr : all a. all b. all constraint. all var. all val. all relevant. all ident.
  RTOrRec a b constraint var val relevant ident
  -> RepTree relevant constraint var val ident b

type RepTreeSolution ident
con RTSNode : all ident.
  { ident : Option ident
  , orIdx : Option Int
  , children : [RepTreeSolution ident]
  , cost : Float
  } -> RepTreeSolution ident

let rtGetRelevantAbove : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> relevant
  = lam tree. switch tree
    case RTAnd x then x.relevantAbove
    case RTOr x then x.relevantAbove
    case RTSingle x then x.relevantAbove
    end
let rtGetIdent : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> Option ident
  = lam tree. switch tree
    case RTAnd x then x.ident
    case RTOr x then x.ident
    case RTSingle x then x.ident
    end
let rtGetApprox : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> PureUnionFind var (Set val)
  = lam tree. switch tree
    case RTAnd x then x.approx
    case RTOr x then x.approx
    case RTSingle x then x.approx
    end
let rtGetConstraint : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> constraint
  = lam tree. switch tree
    case RTAnd x then x.constraint
    case RTOr x then x.constraint
    case RTSingle x then x.constraint
    end
let rtSetApprox : all a. all constraint. all var. all val. all relevant. all ident.
  PureUnionFind var (Set val)
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam approx. lam tree. switch tree
    case RTAnd x then RTAnd {x with approx = approx}
    case RTOr x then RTOr {x with approx = approx}
    case RTSingle x then RTSingle {x with approx = approx}
    end
let rtMap : all a. all constraint. all var. all val. all relevant. all b. all ident.
  (constraint -> a -> b)
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident b
  = lam f. lam tree. switch tree
    case RTAnd x then RTAnd
      { construct = lam c. lam a. f c (x.construct c a)
      , children = x.children
      , selfCost = x.selfCost
      , dep = x.dep
      , constraint = x.constraint
      , relevantHere = x.relevantHere
      , relevantAbove = x.relevantAbove
      , approx = x.approx
      , ident = x.ident
      , history = x.history
      }
    case RTOr x then RTOr
      { construct = lam c. lam a. f c (x.construct c a)
      , others = x.others
      , singles = x.singles
      , selfCost = x.selfCost
      , constraint = x.constraint
      , relevantHere = x.relevantHere
      , relevantAbove = x.relevantAbove
      , approx = x.approx
      , ident = x.ident
      , history = x.history
      }
    case RTSingle x then RTSingle
      { value = f x.constraint x.value
      , cost = x.cost
      , relevantHere = x.relevantHere
      , relevantAbove = x.relevantAbove
      , constraint = x.constraint
      , approx = x.approx
      , ident = x.ident
      , history = x.history
      }
    end
let rtAsSingle : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> Option (RTSingleRec a constraint var val relevant ident)
  = lam tree. match tree with RTSingle x then Some x else None ()
let rtAsSingle : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> Option (RTSingleRec a constraint var val relevant ident)
  = lam tree. match tree with RTSingle x then Some x else None ()
recursive let rtGetMinCost : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> Float
  = lam tree. switch tree
    case RTSingle x then x.cost
    case RTAnd x then
      foldl (lam acc. lam child. addf acc (mulf child.scale (rtGetMinCost child.val)))
        x.selfCost x.children
    case RTOr {singles = [], others = []} then 9999999.9999
    case RTOr ({others = [alt] ++ alts1, singles = alts2} | {others = alts1, singles = [alt] ++ alts2}) then
      foldl (lam acc. lam alt. minf acc (rtGetMinCost alt)) (rtGetMinCost alt) (concat alts1 alts2)
    end
end
recursive let rtScale : all a. all constraint. all var. all val. all relevant. all ident.
  Float
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam scale. lam tree. switch tree
    case RTSingle x then RTSingle {x with cost = mulf scale x.cost}
    case RTAnd x then
      let selfCost = mulf scale x.selfCost in
      let children = map (lam child. {child with scale = mulf scale child.scale}) x.children in
      RTAnd {x with selfCost = selfCost, children = children}
    case RTOr x then
      let selfCost = mulf scale x.selfCost in
      let others = map (rtScale scale) x.others in
      let singles = map (rtScale scale) x.singles in
      RTOr {x with selfCost = selfCost, others = others, singles = singles}
    end
end
let rtSetRelevantAbove : all a. all constraint. all var. all val. all relevant. all ident.
  relevant
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam relevant. lam tree. switch tree
    case RTSingle x then RTSingle {x with relevantAbove = relevant}
    case RTAnd x then RTAnd {x with relevantAbove = relevant}
    case RTOr x then
      RTOr {x with relevantAbove = relevant, others = concat (map (lam x. RTSingle x) x.singles) x.others, singles = []}
    end
let rtMapRelevantHere : all a. all constraint. all var. all val. all relevant. all ident.
  (relevant -> relevant)
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam f. lam tree. switch tree
    case RTSingle x then RTSingle {x with relevantHere = f x.relevantHere}
    case RTAnd x then RTAnd {x with relevantHere = f x.relevantHere}
    case RTOr x then RTOr {x with relevantHere = f x.relevantHere}
    end
let rtBoundedSize : all a. all constraint. all var. all val. all relevant. all ident.
  Int
  -> RepTree relevant constraint var val ident a
  -> Option Int
  = lam bound. lam tree.
    if leqi bound 1 then None () else
    recursive let work = lam tree. switch tree
      case RTSingle _ then Some 1
      case RTAnd x then
        let checkedMult = lam a. lam b.
          let res = muli a b in
          if lti res bound then Some res else None () in
        let childSizes = optionMapM work (map (lam x. x.val) x.children) in
        optionBind childSizes (optionFoldlM checkedMult 1)
      case RTOr x then
        let checkedAdd = lam a. lam b.
          let res = addi a b in
          if lti res bound then Some res else None () in
        let childSizes = optionMapM work x.others in
        optionBind childSizes (optionFoldlM checkedAdd (length x.singles))
      end
    in work tree

let _approxAnd : all k. all v.
  PureUnionFind k (Set v)
  -> PureUnionFind k (Set v)
  -> Option {lChanged : Bool, rChanged : Bool, res : PureUnionFind k (Set v)}
  = lam l. lam r.
    let isEmpty = ref false in
    let lChanged = ref false in
    let rChanged = ref false in
    let merge = lam a. lam b.
      let res = setIntersect a b in
      (if setIsEmpty res then modref isEmpty true else ());
      (if neqi (setSize res) (setSize a) then modref lChanged true else ());
      (if neqi (setSize res) (setSize b) then modref rChanged true else ());
      ((), res) in
    let puf = (pufMerge merge l r).puf in
    if deref isEmpty then None () else Some
    { res = puf
    , lChanged = deref lChanged
    , rChanged = deref rChanged
    }

type RTDebugInterface env relevant constraint var val ident =
  { constraintJson : env -> constraint -> (env, JsonValue)
  , relevantJson : env -> relevant -> (env, JsonValue)
  , varJson : env -> var -> (env, JsonValue)
  , valJson : env -> val -> (env, JsonValue)
  , identJson : env -> ident -> (env, JsonValue)
  }

let _rtApproxJson : all a. all constraint. all var. all val. all relevant. all env. all ident.
  RTDebugInterface env relevant constraint var val ident
  -> env
  -> PureUnionFind var (Set val)
  -> (env, JsonValue)
  = lam fs. lam env. lam approx.
    let res = pufFoldRaw
      (lam acc. lam lIn. lam rIn.
        match fs.varJson acc.env lIn.0 with (env, l) in
        match fs.varJson env rIn.0 with (env, r) in
        {env = env, parts = snoc acc.parts (JsonArray [JsonString "eq", JsonArray [l, JsonInt lIn.1], JsonArray [r, JsonInt rIn.1]])})
      (lam acc. lam lIn. lam out.
        match fs.varJson acc.env lIn.0 with (env, l) in
        match mapAccumL fs.valJson env (setToSeq out) with (env, outs) in
        {env = env, parts = snoc acc.parts (JsonArray [JsonString "out", JsonArray [l, JsonInt lIn.1], JsonArray outs])})
      {env = env, parts = []}
      approx in
    (res.env, JsonArray res.parts)

let rtDebugJson : all a. all constraint. all var. all val. all relevant. all env. all ident.
  RTDebugInterface env relevant constraint var val ident
  -> env
  -> RepTree relevant constraint var val ident a
  -> (env, JsonValue)
  = lam fs. lam env. lam tree.
    let mkHistory : RTHistory -> JsonValue = lam hist.
      recursive let work = lam acc. lam hist. switch hist
        case HStart x then JsonArray (cons (JsonString x) acc)
        case HAndConstruct x then
          let item = JsonObject (mapFromSeq cmpString
            [ ("and-construct", JsonString x.label)
            , ("children", JsonArray (map (work []) x.children))
            ]) in
          work (cons item acc) x.prev
        case HFlatten x then
          let item = JsonObject (mapFromSeq cmpString
            [ ("and-flatten", JsonString x.label)
            , ("children", JsonArray (map (work []) x.children))
            ]) in
          work (cons item acc) x.parent
        case HOrConstruct x then
          let item = JsonObject (mapFromSeq cmpString
            [ ("or-construct", JsonString x.label)
            , ("parent", work [] x.parent)
            ]) in
          work (cons item acc) x.prev
        case HStep x then
          let item = JsonString x.label in
          work (cons item acc) x.prev
        end
      in work [] hist in
    let common = lam env. lam cost. lam constraint. lam approx. lam relevantAbove. lam relevantHere. lam ident. lam history.
      let reprs =
        let mSet = pufFoldRaw
          (lam a. lam. lam. a)
          (lam acc. lam. lam out. Some (optionMapOr out (setUnion out) acc))
          (None ())
          approx in
        mapAccumL fs.valJson env (optionMapOr [] setToSeq mSet) in
      match _rtApproxJson fs reprs.0 approx with (env, approx) in
      match fs.constraintJson env constraint with (env, constraint) in
      match fs.relevantJson env relevantHere with (env, relevantHere) in
      match fs.relevantJson env relevantAbove with (env, relevantAbove) in
      match optionMapAccum fs.identJson env ident with (env, ident) in
      let res =
        [ ("constraint", constraint)
        , ("relevantHere", relevantHere)
        , ("relevantAbove", relevantAbove)
        , ("approx", approx)
        , ("approx reprs", JsonArray reprs.1)
        , ("cost", JsonFloat cost)
        , ("ident", optionGetOr (JsonNull ()) ident)
        , ("history", mkHistory history)
        ] in
      (env, res)
    in
    recursive let work = lam env. lam tree. switch tree
      case RTSingle x then
        match common env x.cost x.constraint x.approx x.relevantAbove x.relevantHere x.ident x.history with (env, common) in
        let res = JsonObject (mapFromSeq cmpString (concat common
          [ ("type", JsonString "single")
          ])) in
        (env, ((1, "1"), res))
      case RTAnd x then
        match common env x.selfCost x.constraint x.approx x.relevantAbove x.relevantHere x.ident x.history with (env, common) in
        match mapAccumL work env (map (lam x. x.val) x.children) with (env, children) in
        match unzip children with (sizes, children) in
        match unzip sizes with (sizes, strSizes) in
        let size = foldl muli 1 sizes in
        let strSize = switch strSizes
          case [] then "1"
          case [strSize] then strSize
          case strSizes then join ["(", strJoin "*" strSizes, ")"]
          end in
        let res = JsonObject (mapFromSeq cmpString (concat common
          [ ("type", JsonString "and")
          , ("dep", JsonString (match x.dep with Dep _ then "dep" else "indep"))
          , ("children", JsonArray children)
          , ("size", JsonInt size)
          , ("strSize", JsonString strSize)
          ])) in
        (env, ((size, strSize), res))
      case RTOr x then
        match common env x.selfCost x.constraint x.approx x.relevantAbove x.relevantHere x.ident x.history with (env, common) in
        match mapAccumL work env x.others with (env, others) in
        match mapAccumL (lam acc. lam sing. work acc (RTSingle sing)) env x.singles with (env, singles) in
        match unzip others with (sizes, others) in
        match unzip sizes with (sizes, strSizes) in
        let singles = map (lam x. x.1) singles in
        let strSizes = if null singles then strSizes else cons (int2string (length singles)) strSizes in
        let strSize = switch strSizes
          case [] then "0"
          case [strSize] then strSize
          case strSizes then join ["(", strJoin " + " strSizes, ")"]
          end in
        let size = foldl addi (length x.singles) sizes in
        let res = JsonObject (mapFromSeq cmpString (concat common
          [ ("type", JsonString "or")
          , ("others", JsonArray others)
          , ("singles", JsonArray singles)
          , ("strSize", JsonString strSize)
          , ("size", JsonInt size)
          ])) in
        (env, ((size, strSize), res))
      end
    in match work env tree with (env, (_, json)) in (env, json)

let rtConstrainShallow : all a. all constraint. all var. all val. all relevant.
  { constraintAnd : constraint -> constraint -> Option {lChanged : Bool, rChanged : Bool, res : constraint}
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  }
  -> { above : (constraint, PureUnionFind var (Set val))
     , here : (constraint, PureUnionFind var (Set val))
     , relevantHere : relevant
     }
  -> Option (Bool, (constraint, PureUnionFind var (Set val)))
  = lam fs. lam args.
    let filterApprox = lam relevant. lam puf.
      pufFilterFunction (lam pair. fs.filterApprox relevant pair.0) puf in
    let constraint = fs.filterConstraint args.relevantHere args.above.0 in
    let approx = filterApprox args.relevantHere args.above.1 in
    match fs.constraintAnd constraint args.here.0 with Some constraint then
      match _approxAnd approx args.here.1 with Some approx then
        Some (or constraint.rChanged approx.rChanged, (constraint.res, approx.res))
      else None ()
    else None ()

let rtAndCost_ : all a. all b. all constraint. all var. all val. all relevant. all ident. all x.
  (x -> Float)
  -> RTAndRec a b constraint var val relevant ident
  -> [x]
  -> Float
  = lam getChildCost. lam and. lam children.
    let below = zipWith (lam pre. lam post. mulf pre.scale (getChildCost post)) and.children children in
    let cost = foldl addf and.selfCost below in
    cost

let rtAndCost : all a. all b. all constraint. all var. all val. all relevant. all ident.
  RTAndRec a b constraint var val relevant ident
  -> [RTSingleRec a constraint var val relevant ident]
  -> Float
  = lam and. lam children.
    rtAndCost_ (lam c. c.cost) and children

let rtConstructAnd : all env. all a. all b. all constraint. all var. all val. all relevant. all ident.
  { constraintAnd : constraint -> constraint -> Option constraint
  , constraintEq : constraint -> constraint -> Bool
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , preComputedConstraint : Option constraint
  , preComputedApprox : Option (PureUnionFind var (Set val))
  , historyLabel : String
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
  -> RTAndRec a b constraint var val relevant ident
  -> [RTSingleRec a constraint var val relevant ident]
  -> Option (RTSingleRec b constraint var val relevant ident)
  = lam fs. lam and. lam children.
    type Approx = PureUnionFind var (Set val) in
    let filterApprox = lam relevant. lam puf.
      pufFilterFunction (lam pair. fs.filterApprox relevant pair.0) puf in
    let constraint =
      let below = map (lam c. fs.filterConstraint and.relevantHere c.constraint) children in
      let computed = optionFoldlM fs.constraintAnd and.constraint below in
      -- TODO(vipa, 2024-01-21): Figure out why this fails, then re-enable
      -- (match fs.preComputedConstraint with Some precomputed then
      --   match computed with Some computed then
      --     if fs.constraintEq precomputed computed then () else
      --     match fs.debugInterface.constraintJson fs.debugEnv precomputed with (env, precomputed) in
      --     match fs.debugInterface.constraintJson fs.debugEnv computed with (env, computed) in
      --     let msg = JsonObject (mapFromSeq cmpString
      --       [ ("msg", JsonString "rtConstructAnd got a different constraint from the pre-computed")
      --       , ("precomputed", precomputed)
      --       , ("computed", computed)
      --       ]) in
      --     printLn (json2string msg);
      --     error "Sanity check failed"
      --   else error "Inconsistency in rtConstructAnd despite getting a pre-computed constraint"
      --  else ());
      computed in
    match constraint with Some constraint then
      let approx =
        let below = map (lam c. filterApprox and.relevantHere c.approx) children in
        let computed = optionFoldlM (lam a. lam b. optionMap (lam x. x.res) (_approxAnd a b))
          and.approx below in
        -- TODO(vipa, 2024-01-19): Check that the pre-computed is correct, if supplied
        computed in
      match approx with Some approx then
        let cost = rtAndCost and children in
        let value = and.construct constraint (map (lam c. c.value) children) in
        let history = HAndConstruct
          { label = fs.historyLabel
          , children = map (lam c. c.history) children
          , prev = and.history
          } in
        let res =
          { value = value
          , cost = cost
          , relevantHere = and.relevantHere
          , relevantAbove = and.relevantAbove
          , constraint = constraint
          , approx = approx
          , ident = and.ident
          , history = history
          } in
        Some res
      else None ()
    else None ()

let rtConstructOrTree : all a. all b. all constraint. all var. all val. all relevant. all ident.
  { constraintAnd : constraint -> constraint -> Option constraint
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , preComputedConstraint : Option constraint
  , preComputedApprox : Option (PureUnionFind var (Set val))
  , historyLabel : String
  }
  -> RTOrRec a b constraint var val relevant ident
  -> RepTree relevant constraint var val ident a
  -> Option (RepTree relevant constraint var val ident b)
  = lam fs. lam or. lam alt.
    type Never in
    let constrainFs =
      { constraintAnd = lam a. lam b. optionMap (lam res. {lChanged = false, rChanged = false, res = res}) (fs.constraintAnd a b)
      , filterConstraint = fs.filterConstraint
      , filterApprox = fs.filterApprox
      } in
    switch alt
    case RTSingle x then
      let relevantHere = fs.unionRelevant or.relevantHere x.relevantHere in
      let args =
        { above = (or.constraint, or.approx)
        , here = (x.constraint, x.approx)
        , relevantHere = relevantHere
        } in
      match rtConstrainShallow constrainFs args with Some (_, (constraint, approx)) then
        let res = RTSingle
          { value = or.construct constraint x.value
          , cost = addf or.selfCost x.cost
          , relevantHere = relevantHere
          , relevantAbove = or.relevantAbove
          , constraint = constraint
          , approx = approx
          , ident = fs.mergeIdent {parent = or.ident, child = x.ident}
          , history = HOrConstruct {label = fs.historyLabel, parent = or.history, prev = x.history}
          } in
        Some res
      else None ()
    case RTAnd x then
      let x : RTAndRec Never a constraint var val relevant ident = x in
      let relevantHere = fs.unionRelevant or.relevantHere x.relevantHere in
      let args =
        { above = (or.constraint, or.approx)
        , here = (x.constraint, x.approx)
        , relevantHere = relevantHere
        } in
      match rtConstrainShallow constrainFs args with Some (_, (constraint, approx)) then
        let res = RTAnd
          { children = x.children
          , selfCost = addf or.selfCost x.selfCost
          , dep = x.dep
          , construct = lam constraint. lam children. or.construct constraint (x.construct constraint children)
          , relevantHere = relevantHere
          , relevantAbove = or.relevantAbove
          , constraint = constraint
          , approx = approx
          , ident = fs.mergeIdent {parent = or.ident, child = x.ident}
          , history = HOrConstruct {label = fs.historyLabel, parent = or.history, prev = x.history}
          } in
        Some res
      else None ()
    case RTOr x then
      let x : RTOrRec Never a constraint var val relevant ident = x in
      let relevantHere = fs.unionRelevant or.relevantHere x.relevantHere in
      let args =
        { above = (or.constraint, or.approx)
        , here = (x.constraint, x.approx)
        , relevantHere = relevantHere
        } in
      match rtConstrainShallow constrainFs args with Some (_, (constraint, approx)) then
        let res = RTOr
          { others = x.others
          , singles = x.singles
          , selfCost = addf or.selfCost x.selfCost
          , construct = lam constraint. lam child. or.construct constraint (x.construct constraint child)
          , relevantHere = relevantHere
          , relevantAbove = or.relevantAbove
          , constraint = constraint
          , approx = approx
          , ident = fs.mergeIdent {parent = or.ident, child = x.ident}
          , history = HOrConstruct {label = fs.historyLabel, parent = or.history, prev = x.history}
          } in
        Some res
      else None ()
    end

let rtConstructOr : all a. all b. all constraint. all var. all val. all relevant. all ident.
  { constraintAnd : constraint -> constraint -> Option constraint
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , preComputedConstraint : Option constraint
  , preComputedApprox : Option (PureUnionFind var (Set val))
  , historyLabel : String
  }
  -> RTOrRec a b constraint var val relevant ident
  -> RTSingleRec a constraint var val relevant ident
  -> Option (RTSingleRec b constraint var val relevant ident)
  = lam fs. lam or. lam alt.
    let unwrap = lam tree.
      match tree with RTSingle sing then sing else
      error "Compiler error: rtConstructOrTree gave a non-RTSingle when input was RTSingle" in
    optionMap unwrap (rtConstructOrTree fs or (RTSingle alt))

let _intersectApproxFromBelow : all relevant. all constraint. all a. all ident.
  PureUnionFind Symbol (Set Name)
  -> RepTree relevant constraint Symbol Name ident a
  -> PureUnionFind Symbol (Set Name)
  = lam puf. lam tree. pufFold
    (lam a. lam. lam. a)
    (lam a. lam k. lam out. (pufSetOut (lam a. lam b. ((), setIntersect a b)) k out a).puf)
    puf
    (rtGetApprox tree)

let _approxHasEmptyDomain : all k. all v. PureUnionFind k (Set v) -> Bool
  = lam puf. pufFold
    (lam a. lam. lam. a)
    (lam a. lam k. lam out. if a then true else setIsEmpty out)
    false
    puf

let _computeAltApproxDirect : all var. all val.
  PureUnionFind var (Set val)
  -> [PureUnionFind var (Set val)]
  -> Option (PureUnionFind var (Set val))
  = lam restr. lam below.
    let count = length below in
    let puf =
      let findOccurs = lam acc. lam approx. pufFold
        (lam a. lam. lam. a)
        (lam a. lam k. lam out. mapInsertWith (lam a. lam b. (a.0, addi a.1 b.1, setUnion a.2 b.2)) k.0 (k.1, 1, out) a)
        acc
        approx in
      let x = foldl findOccurs (mapEmpty (mapGetCmpFun restr)) below in
      let addIfConstrained = lam acc. lam k. lam v.
        if eqi v.1 count
        then (pufSetOut (lam. error "Compiler error in _computeAltApprox") (k, v.0) v.2 acc).puf
        else acc in
      let puf = pufEmpty (mapGetCmpFun restr) in
      mapFoldWithKey addIfConstrained puf x in
    optionMap (lam x. x.res) (_approxAnd restr puf)

let _computeAltApprox : all relevant. all constraint. all var. all val. all a. all ident.
  PureUnionFind var (Set val)
  -> [RepTree relevant constraint var val ident a]
  -> Option (PureUnionFind var (Set val))
  = lam restr. lam below.
    _computeAltApproxDirect restr (map rtGetApprox below)

let _pruneListElement : all l. all r. (l -> r -> {lUseful : Bool, rUseful : Bool}) -> [l] -> r -> ([l], Bool)
  = lam check. lam previous. lam new.
    let optionFilterM : all a. all x. all y. (x -> Option Bool) -> [x] -> Option [x]
      = lam f.
        recursive let work = lam kept. lam l.
          match l with [x] ++ l then
            match f x with Some keep then
              work (if keep then snoc kept x else kept) l
            else None ()
          else Some kept
        in work [] in
    let f = lam old.
      let res = check old new in
      if not res.rUseful then None () else
      Some res.lUseful in
    match optionFilterM f previous with Some pruned
    then (pruned, true)
    else (previous, false)

let lazyExploreSorted : all a. all b. ([a] -> Either Int b) -> (a -> Float) -> [LStream a] -> LStream b
  = lam constructOrStep. lam computeCost. lam streams.
    type Potential =
      { cost : Float
      , combo : [Int]
      , parts : [(a, LStream a)]
      } in
    type State =
      { queue : Heap Potential
      , consideredCombos : Set [Int]
      } in

    let cmpByCost = lam a. lam b.
      if ltf a.cost b.cost then negi 1 else
      if gtf a.cost b.cost then 1 else
      0 in
    let cmpComboId = seqCmp subi in

    let addSuccessors : Potential -> Option Int -> State -> State
      = lam pot. lam failIdx. lam st.
        let stepAtIdx : Potential -> Int -> Option Potential = lam pot. lam idx.
          let part = get pot.parts idx in
          match lazyStreamUncons part.1 with Some newPart then Some
            { cost = addf (subf pot.cost (computeCost part.0)) (computeCost newPart.0)
            , parts = set pot.parts idx newPart
            , combo = set pot.combo idx (addi 1 (get pot.combo idx))
            }
          else None () in
        let succ = match failIdx with Some failIdx
          then create failIdx (stepAtIdx pot)
          else create (length pot.parts) (stepAtIdx pot) in
        let succ = filterOption succ in
        let checkSeen = lam seen. lam pot.
          if setMem pot.combo seen
          then (seen, None ())
          else (setInsert pot.combo seen, Some pot) in
        match mapAccumL checkSeen st.consideredCombos succ with (consideredCombos, succ) in
        let succ = filterOption succ in
        { queue = heapAddMany cmpByCost succ st.queue
        , consideredCombos = consideredCombos
        }
    in

    recursive let step : State -> Option (() -> State, b) = lam st.
      match heapPop cmpByCost st.queue with Some (pot, queue) then
        let st = {st with queue = queue} in
        switch constructOrStep (map (lam x. x.0) pot.parts)
        case Right b then
          Some (lam. addSuccessors pot (None ()) st, b)
        case Left idx then
          step (addSuccessors pot (Some idx) st)
        end
      else None ()
    in

    match optionMapM lazyStreamUncons streams with Some parts then
      let mkState = lam.
        let cost = foldl (lam acc. lam x. addf acc (computeCost x.0)) 0.0 parts in
        { queue = heapSingleton {cost = cost, combo = make (length parts) 0, parts = parts}
        , consideredCombos = setEmpty cmpComboId
        } in
      lazyStreamLaziest step mkState
    else lazyStreamEmpty ()

let directedStepper : all a. all acc.
  (a -> acc)
  -> (all x. [(x, acc)] -> [([x], acc)])
  -> (acc -> acc -> Option acc)
  -> [(a, acc -> Option a)]
  -> [(acc, [a])]
  = lam getAcc. lam partitionAccs. lam mergeAccs. lam parts.
    type Point x = {acc : acc, good : [(x, a)], nextSteps : [(x, acc -> Option a)]} in
    -- NOTE(vipa, 2024-01-20): Take a stepped list of items, partition
    -- them, then return either a list of new points (if more than one
    -- partition, i.e., if inconsistent) or the final acc and items
    -- (if one partition, i.e., if consistent)
    let computePoints : all x. [(x, a, acc -> Option a)] -> Either [Point x] (acc, [(x, a)])
      = lam trips.
        let trips = map (lam trip. (trip, getAcc trip.1)) trips in
        let partitions = partitionAccs trips in
        let mkPoint = lam idx.
          match splitAt partitions idx with (pre, [here] ++ post) then
            let others = join (map (lam x. x.0) (concat pre post)) in
            let toStep = map (lam trip. (trip.0, trip.2)) others in
            let good = map (lam trip. (trip.0, trip.1)) here.0 in
            { acc = here.1
            , good = good
            , nextSteps = toStep
            }
          else error "Compiler error in mkPoint" in
        let points = create (length partitions) mkPoint in
        match points with [point]
        then Right (point.acc, point.good)
        else Left points in
    -- NOTE(vipa, 2024-01-20): Take one point, step the items waiting
    -- to be stepped, then see if the stepped items are consistent. If
    -- they are, merge their final acc with the current acc and
    -- return, otherwise return a new set of points.
    let stepPoint : all x. Point x -> Either [Point x] (acc, [(x, a)])
      = lam point.
        let stepOne = lam pair.
          optionMap (lam a. (pair.0, a, pair.1)) (pair.1 point.acc) in
        match optionMapM stepOne point.nextSteps with Some trips then
          let mergePoint = lam point2.
            match mergeAccs point.acc point2.acc with Some acc then Some
              { acc = acc
              , good = concat point.good point2.good
              , nextSteps = point2.nextSteps
              }
            else None () in
          let mergeSuccess = lam res.
            match mergeAccs point.acc res.0 with Some acc
            then (acc, concat point.good res.1)
            else error "Compiler error: mergeAccs fail in mergeSuccess" in
          let res = computePoints trips in
          eitherBiMap (mapOption mergePoint) mergeSuccess res
        else Left []
    in
    recursive let work : all x. [Point x] -> [(acc, [(x, a)])]
      = lam points.
        switch eitherPartition (map stepPoint points)
        case ([], []) then []
        case (points, []) then work (join points)
        case (_, sols) then sols
        end in
    let start = mapi (lam idx. lam pair. (idx, pair.0, pair.1)) parts in
    let fixup = lam pair.
      (pair.0, map (lam x. x.1) (sort (lam a. lam b. subi a.0 b.0) pair.1)) in
    switch computePoints start
    case Left points then map fixup (work points)
    case Right res then [fixup res]
    end

type RTMaterializeConsistentInterface env relevant constraint var val ident =
  { partitionConsistentConstraints : all x. [(x, constraint)] -> [([x], constraint)]
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , constraintAnd : constraint -> constraint -> Option constraint
  , constraintImplies : constraint -> constraint -> Bool
  , constraintEq : constraint -> constraint -> Bool
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
let rtMaterializeConsistent : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTMaterializeConsistentInterface env relevant constraint var val ident
  -> RepTree relevant constraint var val ident a
  -> Option (RTSingleRec a constraint var val relevant ident)
  = lam fs. lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    type Tree a = RepTree relevant constraint var val ident a in
    type Single a = RTSingleRec a constraint var val relevant ident in
    type QueryF a = (constraint, Approx) -> Option (Single a) in
    let cmpf = lam a. lam b.
      if ltf a b then negi 1 else
      if gtf a b then 1 else 0 in
    let cmpSingle : all a. Single a -> Single a -> Int =
      lam a. lam b. cmpf a.cost b.cost in
    let constrainFs =
      { constraintAnd = lam a. lam b. optionMap (lam res. {lChanged = false, rChanged = false, res = res}) (fs.constraintAnd a b)
      , filterConstraint = fs.filterConstraint
      , filterApprox = fs.filterApprox
      } in
    let constrain = lam args. optionMap (lam x. x.1) (rtConstrainShallow constrainFs args) in
    recursive let work : all a. Tree a -> Option (Single a, QueryF a)
      = lam tree. switch tree
        case RTSingle x then
          let update = lam pair. {x with constraint = pair.0, approx = pair.1} in
          let query = lam above.
            let res = constrain {above = above, here = (x.constraint, x.approx), relevantHere = x.relevantHere} in
            match res with Some here then
              Some {x with constraint = here.0, approx = here.1}
            else None () in
          Some (x, query)
        case RTOr x then
          let x : RTOrRec Never a constraint var val relevant ident = x in
          let orFs =
            { constraintAnd = fs.constraintAnd
            , filterConstraint = fs.filterConstraint
            , filterApprox = fs.filterApprox
            , unionRelevant = fs.unionRelevant
            , mergeIdent = fs.mergeIdent
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "mat-consistent-or"
            } in
          let alternatives = concat (map (lam x. RTSingle x) x.singles) x.others in
          let alternatives = mapOption work alternatives in
          match unzip alternatives with (rets, queries) in
          let update = lam pair. lam sing. rtConstructOr orFs {x with constraint = pair.0, approx = pair.1} sing in
          let ret = optionBind (min cmpSingle rets) (update (x.constraint, x.approx)) in
          let query = lam above.
            let res = constrain {above = above, here = (x.constraint, x.approx), relevantHere = x.relevantHere} in
            match res with Some here then
              let rets = mapOption (lam query. query here) queries in
              optionBind (min cmpSingle rets) (update here)
            else None () in
          optionMap (lam ret. (ret, query)) ret
        case RTAnd x then
          let x : RTAndRec Never a constraint var val relevant ident = x in
          let andFs =
            { constraintAnd = fs.constraintAnd
            , filterConstraint = fs.filterConstraint
            , filterApprox = fs.filterApprox
            , debugInterface = fs.debugInterface
            , debugEnv = fs.debugEnv
            , constraintEq = fs.constraintEq
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "mat-consistent-and"
            } in
          let partition = fs.partitionConsistentConstraints in
          match optionMapM (lam c. work c.val) x.children with Some children then
            match unzip children with (children, queries) in
            -- NOTE(vipa, 2024-01-20): The stepping procedure here
            -- works in a very particular constraint space: we filter
            -- by x.relevantHere (as might be expected), and all
            -- constraints must be consistent with a particular
            -- constraint. At first this is x.constraint, but in a new
            -- query it's x.constraint `and` the constraint from
            -- above.

            -- NOTE(vipa, 2024-01-20): Assumption: directedStepper
            -- assumes all relevant points of a constraint are present
            -- in the constraints in the list it is given. That means
            -- it must *always* be given items that contain the
            -- constraint of the current node `and`ed with the
            -- filtered constraint of the child, rather than the
            -- constraint of the child itself.
            let childWithConstraint = lam constraint. lam c.
              match fs.constraintAnd constraint (fs.filterConstraint x.relevantHere c.constraint)
              with Some constraint then {constraint = constraint, child = c}
              else
                match fs.debugInterface.constraintJson fs.debugEnv constraint with (env, constraint) in
                match rtDebugJson fs.debugInterface env (RTAnd x) with (env, here) in
                match rtDebugJson fs.debugInterface env (RTSingle c) with (env, child) in
                printLn "\"The constraint we should be consistent with\"";
                printLn (json2string constraint);
                printLn "\"parent RTAnd\"";
                printLn (json2string here);
                printLn "\"child materialized from below\"";
                printLn (json2string child);
                error "Compiler error: inconsistent constraint from below" in
            let updateQuery = lam constraint. lam approx. lam query. lam stepConstraint.
              optionMap (childWithConstraint stepConstraint) (query (stepConstraint, approx)) in

            let computeSelection = lam here. lam children. lam queries.
              let possibleSelections = directedStepper
                (lam x. x.constraint)
                #frozen"partition"
                fs.constraintAnd
                (zip children queries) in
              let selectionsWithCosts =
                let f = lam pair.
                  let children = map (lam x. x.child) pair.1 in
                  (rtAndCost x children, pair.0, children) in
                map f possibleSelections in
              match min (lam a. lam b. cmpf a.0 b.0) selectionsWithCosts with Some (_, constraint, children) then
                match rtConstructAnd
                  {andFs with preComputedConstraint = Some constraint}
                  {x with constraint = here.0, approx = here.1}
                  children
                with res & Some _ then res
                else
                  match fs.debugInterface.constraintJson fs.debugEnv here.0 with (env, constraint) in
                  match rtDebugJson fs.debugInterface env (RTAnd x) with (env, here) in
                  match mapAccumL (lam a. lam c. rtDebugJson fs.debugInterface a (RTSingle c)) env children with (env, children) in
                  printLn "\"The constraint we should be consistent with\"";
                  printLn (json2string constraint);
                  printLn "\"parent RTAnd\"";
                  printLn (json2string here);
                  printLn "\"children materialized from below\"";
                  printLn (json2string (JsonArray children));
                  error "Compiler error: inconsistent choice of children from directedStepper"
              else None () in

            let ret = computeSelection (x.constraint, x.approx)
              (map (childWithConstraint x.constraint) children)
              (map (updateQuery x.constraint x.approx) queries) in
            let query = lam above.
              let res = constrain {above = above, here = (x.constraint, x.approx), relevantHere = x.relevantHere} in
              match res with Some here then
                match optionMapM (lam query. query here) queries with Some children then
                  let children = map (childWithConstraint here.0) children in
                  let queries = map (updateQuery here.0 here.1) queries in
                  computeSelection here children queries
                else None ()
              else None () in

            optionMap (lam ret. (ret, query)) ret
          else None ()
        end
    in optionMap (lam pair. pair.0) (work tree)


type RTMaterializeLazyInterface env relevant constraint var val ident =
  { constraintAnd : constraint -> constraint -> Option constraint
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , pruneRedundant : constraint -> constraint -> {lUseful : Bool, rUseful : Bool}
  , constraintEq : constraint -> constraint -> Bool
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
let rtMaterializeLazyRecursive : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTMaterializeLazyInterface env relevant constraint var val ident
  -> RepTree relevant constraint var val ident a
  -> LStream (RTSingleRec a constraint var val relevant ident)
  = lam fs. lam tree.
    type Never in
    type Single a = RTSingleRec a constraint var val relevant ident in
    type Ret a = {value : a, constraint : constraint, cost : Float} in
    type Tree a = RepTree relevant constraint var val ident a in
    let cmpRet = lam a. lam b.
      if ltf a.cost b.cost then negi 1 else
      if gtf a.cost b.cost then 1 else 0 in
    let retMap = lam f. lam ret.
      { constraint = ret.constraint
      , cost = ret.cost
      , value = f ret.value
      } in
    let foldlFailIdx : all acc. all a. (acc -> a -> Option acc) -> acc -> [a] -> Either Int acc
      = lam f. lam acc. lam l.
        recursive let work = lam acc. lam idx. lam l.
          match l with [x] ++ l then
            match f acc x with Some acc
            then work acc (addi idx 1) l
            else Left (addi idx 1)
          else Right acc
        in work acc 0 l
    in
    recursive let work : all a. Tree a -> LStream (Single a)
      = lam tree. switch tree
        case RTSingle x then
          lazyStreamSingleton x
        case RTOr x then
          let x : RTOrRec Never a constraint var val relevant ident = x in
          let orFs =
            { constraintAnd = fs.constraintAnd
            , filterConstraint = fs.filterConstraint
            , filterApprox = fs.filterApprox
            , unionRelevant = fs.unionRelevant
            , mergeIdent = fs.mergeIdent
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "lazy-pick-or"
            } in
          let alts = map work (concat (map (lam x. RTSingle x) x.singles) x.others) in
          let f = lam constraints. lam new.
            let new =
              { new with constraint = fs.filterConstraint x.relevantAbove new.constraint
              } in
            match _pruneListElement (lam l. lam r. fs.pruneRedundant l r.constraint) constraints new
              with (constraints, keep) in
            if keep
            then (snoc constraints new.constraint, true)
            else (constraints, false) in
          let stream = lazyStreamMergeMin cmpRet alts in
          let stream = lazyStreamStatefulFilter f [] stream in
          lazyStreamMapOption (rtConstructOr orFs x) stream
        case RTAnd x then
          let x : RTAndRec Never a constraint var val relevant ident = x in
          let filterConstraint = fs.filterConstraint x.relevantHere in
          let andFs =
            { constraintAnd = fs.constraintAnd
            , filterConstraint = fs.filterConstraint
            , filterApprox = fs.filterApprox
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "lazy-and"
            , constraintEq = fs.constraintEq
            , debugInterface = fs.debugInterface
            , debugEnv = fs.debugEnv
            } in
          let f = lam child.
            let stream = work child.val in
            lazyStreamMap (lam x. {cost = mulf x.cost child.scale, val = x}) stream in
          let children = map f x.children in
          let tryMk = lam rets.
            let res = foldlFailIdx fs.constraintAnd x.constraint (map (lam x. filterConstraint x.val.constraint) rets) in
            let construct = lam constraint.
              let andFs = {andFs with preComputedConstraint = Some constraint} in
              let res = rtConstructAnd andFs x (map (lam x. x.val) rets) in
              optionMapOr (Left (length rets)) (lam x. Right x) res in
            eitherBindRight res construct in
          lazyExploreSorted tryMk (lam x. x.cost) children
        end
    in work tree

type RTMaterializeStatelessInterface env relevant constraint var val ident =
  { constraintAnd : constraint -> constraint -> Option constraint
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , constraintEq : constraint -> constraint -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , constraintEmpty : constraint
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
let rtMaterializeStateless : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTMaterializeStatelessInterface env relevant constraint var val ident
  -> RepTree relevant constraint var val ident a
  -> Iter (RTSingleRec a constraint var val relevant ident)
  = lam fs. lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    type Single a = RTSingleRec a constraint var val relevant ident in
    type Tree a = RepTree relevant constraint var val ident a in
    type FilteredStepper a = constraint -> Approx -> Iter a in
    let cmpf = lam a. lam b. if ltf a b then negi 1 else if gtf a b then 1 else 0 in
    let filterApprox = lam relevant. lam puf.
      pufFilterFunction (lam pair. fs.filterApprox relevant pair.0) puf in
    let constrain
      : relevant
      -> {here : (constraint, Approx), elsewhere : (constraint, Approx)}
      -> Option (constraint, Approx)
      = lam relevant. lam args.
        let constraint = fs.filterConstraint relevant args.elsewhere.0 in
        match fs.constraintAnd constraint args.here.0 with Some constraint then
          let approx = filterApprox relevant args.elsewhere.1 in
          match _approxAnd approx args.here.1 with Some {res = approx}
          then Some (constraint, approx)
          else None ()
        else None () in
    let fsOr : all a. FilteredStepper (Single a) -> FilteredStepper (Single a) -> FilteredStepper (Single a)
      = lam aStep. lam bStep. lam constraint. lam approx. lam.
        iterConcat (aStep constraint approx) (bStep constraint approx) () in
    let fsEmptyOr : all x. FilteredStepper x = lam. lam. iterEmpty in
    let fsAnd : all a. relevant -> FilteredStepper (Single a) -> FilteredStepper [Single a] -> FilteredStepper [Single a]
      = lam relevant. lam a. lam b. lam constraint. lam approx. lam.
        let givenASingle = lam aSingle.
          let arg = {here = (constraint, approx), elsewhere = (aSingle.constraint, aSingle.approx)} in
          match constrain relevant arg with Some (constraint, approx) then
            iterMap (lam bSingles. cons aSingle bSingles) (b constraint approx)
          else iterEmpty in
        iterConcatMap givenASingle (a constraint approx) () in
    let fsEmptyAnd : all x. FilteredStepper [x] = lam. lam. iterSingle [] in
    let andFs =
      { constraintAnd = fs.constraintAnd
      , filterConstraint = fs.filterConstraint
      , filterApprox = fs.filterApprox
      , preComputedConstraint = None ()
      , preComputedApprox = None ()
      , historyLabel = "stateless-child"
      , constraintEq = fs.constraintEq
      , debugInterface = fs.debugInterface
      , debugEnv = fs.debugEnv
      } in
    let orFs =
      { constraintAnd = fs.constraintAnd
      , filterConstraint = fs.filterConstraint
      , filterApprox = fs.filterApprox
      , unionRelevant = fs.unionRelevant
      , mergeIdent = fs.mergeIdent
      , preComputedConstraint = None ()
      , preComputedApprox = None ()
      , historyLabel = "stateless-or"
      } in
    recursive let work : all a. Tree a -> FilteredStepper (Single a) = lam tree. switch tree
      case RTSingle x then
        lam constraint. lam approx.
          let arg = {here = (x.constraint, x.approx), elsewhere = (constraint, approx)} in
          match constrain x.relevantHere arg with Some _
          then iterSingle x
          else iterEmpty
      case RTOr x then
        let x : RTOrRec Never a constraint var val relevant ident = x in
        let alternatives = concat
          (map (lam x. RTSingle x) (sort (lam a. lam b. cmpf a.cost b.cost) x.singles))
          x.others in
        let innerSpec = foldr fsOr fsEmptyOr (map work alternatives) in
        lam constraint. lam approx.
          let arg = {here = (x.constraint, x.approx), elsewhere = (constraint, approx)} in
          match constrain x.relevantHere arg with Some (constraint, approx) then
            let iter = innerSpec constraint approx in
            let mk = lam single. match rtConstructOr orFs x single with Some single
              then single
              else error "Compiler error: failed to rtConstructOr in materialize stateless" in
            iterMap mk iter
          else iterEmpty
      case RTAnd x then
        let x : RTAndRec Never a constraint var val relevant ident = x in
        let innerSpec = foldr (fsAnd x.relevantHere) fsEmptyAnd (map (lam x. work x.val) x.children) in
        lam constraint. lam approx.
          let arg = {here = (x.constraint, x.approx), elsewhere = (constraint, approx)} in
          match constrain x.relevantHere arg with Some (constraint, approx) then
            let iter = innerSpec constraint approx in
            let mk = lam singles. match rtConstructAnd andFs x singles with Some single
              then single
              else error "Compiler error: failed to rtConstructAnd in materialize stateless" in
            iterMap mk iter
          else iterEmpty
      end in
    work tree fs.constraintEmpty (pufEmpty (mapGetCmpFun (rtGetApprox tree)))

type RTPartitionInternalInterface relevant constraint var val =
  { varsToRelevant : [var] -> relevant
  , fixedInConstraint : constraint -> relevant
  , normalizeRelevantToConstraint : constraint -> relevant -> relevant
  , unionRelevant : relevant -> relevant -> relevant
  , intersectRelevant : relevant -> relevant -> relevant
  , subtractRelevant : relevant -> relevant -> relevant
  , partitionRelevant : all x. [(x, relevant)] -> [[x]]
  , emptyRelevant : relevant
  , filterApprox : relevant -> var -> Bool
  , filterConstraint : relevant -> constraint -> constraint
  }
let rtPartitionInternalComponents : all relevant. all constraint. all var. all val. all a. all ident.
  RTPartitionInternalInterface relevant constraint var val
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam fs. lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    let filterApprox = lam relevant. lam puf.
      pufFilterFunction (lam pair. fs.filterApprox relevant pair.0) puf in
    recursive let work : all a. RepTree relevant constraint var val ident a -> RepTree relevant constraint var val ident a
      = lam tree. switch tree
        case RTSingle _ then tree
        case RTOr x then
          let x : RTOrRec Never a constraint var val relevant ident = x in
          let others = map work x.others in
          RTOr {x with others = others}
        case RTAnd x then
          let x : RTAndRec Never a constraint var val relevant ident = x in
          let children = map (lam child. {child with val = work child.val}) x.children in
          match (children, x.dep) with ([] | [_], _) | (_, InDep _) then
            RTAnd {x with children = children}
          else  -- Early exit

          let ignorable = x.relevantAbove in
          let ignorable = fs.unionRelevant ignorable (fs.fixedInConstraint x.constraint) in
          let ignorable =
            let fixedInApprox = pufFold
              (lam acc. lam. lam. acc)
              (lam acc. lam k. lam out.
                if eqi 1 (setSize out)
                then snoc acc k.0
                else acc)
              []
              x.approx in
            fs.unionRelevant ignorable (fs.varsToRelevant fixedInApprox) in
          let juggle = lam i. lam child.
            ((i, child), fs.subtractRelevant (rtGetRelevantAbove child.val) ignorable) in
          let partitions = fs.partitionRelevant (mapi juggle children) in
          -- NOTE(vipa, 2024-01-16): Splitting out partitions
          -- containing a single child doesn't actually provide any
          -- benefit over just leaving them together, thus we put all
          -- singleton partitions and make a new partition out of
          -- them.
          match eitherPartition (map (lam part. match part with [p] then Left p else Right part) partitions)
            with (singlePart, multiParts) in
          let partitions = if null singlePart then multiParts else cons singlePart multiParts in
          switch partitions
          case [_] then RTAnd {x with children = children}
          case [_] ++ _ then
            let mkPartition = lam partition.
              match unzip partition with (idxes, children) in
              let relevantHere = foldl fs.unionRelevant fs.emptyRelevant
                (map (lam child. rtGetRelevantAbove child.val) children) in
              let relevantAbove = fs.intersectRelevant x.relevantHere relevantHere in
              let subtree = RTAnd
                { children = children
                , selfCost = 0.0
                , dep = x.dep
                , construct = lam. zipWith (lam idx. lam a. (idx, a)) idxes
                , constraint = fs.filterConstraint relevantHere x.constraint
                , approx = filterApprox relevantHere x.approx
                , relevantHere = relevantHere
                , relevantAbove = relevantAbove
                , ident = None ()
                , history = HStep {label = "partition-child", prev = x.history}
                } in
              {scale = 1.0, val = subtree} in
            RTAnd
            { children = map mkPartition partitions
            , construct = lam constraint. lam pairs.
              let pairs = join pairs in
              let pairs = sort (lam a. lam b. subi a.0 b.0) pairs in
              x.construct constraint (map (lam x. x.1) pairs)
            , selfCost = x.selfCost
            , dep = x.dep
            , constraint = x.constraint
            , approx = x.approx
            , relevantHere = x.relevantHere
            , relevantAbove = x.relevantAbove
            , ident = x.ident
            , history = HStep {label = "partition-parent", prev = x.history}
            }
          case [] then
            error "Compiler error: empty list returned from partitionRelevant"
          end
        end
    in work tree

let rtPartitionIndependent : all relevant. all constraint. all var. all val. all a. all ident.
  RTPartitionInternalInterface relevant constraint var val
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam fs. lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    let filterApprox = lam relevant. lam puf.
      pufFilterFunction (lam pair. fs.filterApprox relevant pair.0) puf in
    recursive let work : all a. RepTree relevant constraint var val ident a -> RepTree relevant constraint var val ident a
      = lam tree. switch tree
        case RTSingle _ then tree
        case RTOr x then
          let x : RTOrRec Never a constraint var val relevant ident = x in
          let others = map work x.others in
          RTOr {x with others = others}
        case RTAnd x then
          let x : RTAndRec Never a constraint var val relevant ident = x in
          let children = map (lam child. {child with val = work child.val}) x.children in
          match (children, x.dep) with ([] | [_], _) | (_, InDep _) then
            RTAnd {x with children = children}
          else  -- Early exit

          let ignorable = fs.fixedInConstraint x.constraint in
          let ignorable =
            let fixedInApprox = pufFold
              (lam acc. lam. lam. acc)
              (lam acc. lam k. lam out.
                if eqi 1 (setSize out)
                then snoc acc k.0
                else acc)
              []
              x.approx in
            fs.unionRelevant ignorable (fs.varsToRelevant fixedInApprox) in
          let juggle = lam i. lam child.
            ( (i, child)
            , fs.normalizeRelevantToConstraint x.constraint (fs.subtractRelevant (rtGetRelevantAbove child.val) ignorable)
            ) in
          let partitions = fs.partitionRelevant (mapi juggle children) in
          -- NOTE(vipa, 2024-01-16): Splitting out partitions
          -- containing a single child doesn't actually provide any
          -- benefit over just leaving them together, thus we put all
          -- singleton partitions and make a new partition out of
          -- them.
          switch partitions
          case [_] then RTAnd {x with children = children}
          case [_] ++ _ then
            let mkPartition = lam partition.
              match unzip partition with (idxes, children) in
              let relevantHere = foldl fs.unionRelevant fs.emptyRelevant
                (map (lam child. rtGetRelevantAbove child.val) children) in
              let relevantAbove = fs.intersectRelevant x.relevantHere relevantHere in
              let subtree = RTAnd
                { children = children
                , selfCost = 0.0
                , dep = x.dep
                , construct = lam. zipWith (lam idx. lam a. (idx, a)) idxes
                , constraint = fs.filterConstraint relevantHere x.constraint
                , approx = filterApprox relevantHere x.approx
                , relevantHere = relevantHere
                , relevantAbove = relevantAbove
                , ident = None ()
                , history = HStep {label = "partition-indep-child", prev = x.history}
                } in
              {scale = 1.0, val = subtree} in
            RTAnd
            { children = map mkPartition partitions
            , construct = lam constraint. lam pairs.
              let pairs = join pairs in
              let pairs = sort (lam a. lam b. subi a.0 b.0) pairs in
              x.construct constraint (map (lam x. x.1) pairs)
            , selfCost = x.selfCost
            , dep = InDep ()
            , constraint = x.constraint
            , approx = x.approx
            , relevantHere = x.relevantHere
            , relevantAbove = x.relevantAbove
            , ident = x.ident
            , history = HStep {label = "partition-indep-parent", prev = x.history}
            }
          case [] then
            error "Compiler error: empty list returned from partitionRelevant"
          end
        end
    in work tree

type RTFlattenInterface env relevant constraint var val ident =
  { constraintAnd : constraint -> constraint -> Option constraint
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
let rtFlatten : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTFlattenInterface env relevant constraint var val ident
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam fs. lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    type Single a = RTSingleRec a constraint var val relevant ident in
    -- NOTE(vipa, 2024-03-08): I don't know a way to make this fully
    -- type-safe, since each child could theoretically have a
    -- different hidden inner type. The implementation will make sure
    -- to only use the correct construct function for each child, but
    -- that's very much not something that the type-system ensures for
    -- us.
    type And a = RTAndRec Never a constraint var val relevant ident in
    type Tree a = RepTree relevant constraint var val ident a in
    recursive let work : all a. Tree a -> (Option (And a), Tree a) = lam tree. switch tree
      case RTSingle _ then (None (), tree)
      case RTOr x then
        let x : RTOrRec Never a constraint var val relevant ident = x in
        (None (), RTOr {x with others = map (lam child. (work child).1) x.others})
      case RTAnd x then
        let x : RTAndRec Never a constraint var val relevant ident = x in
        let children = map (lam child. {scale = child.scale, val = work child.val}) x.children in
        if any (lam child. optionIsSome child.val.0) children then
          let emptyMergeSpec =
            { children = []
            , constructs = []
            , constraint = Some x.constraint
            , approx = Some x.approx
            , relevantHere = x.relevantHere
            , extraCost = 0.0
            , histories = []
            } in
          let addChild = lam acc. lam child. switch child.val
            case (Some and, _) then
              { children = concat acc.children (map (lam c. {c with scale = mulf c.scale child.scale}) and.children)
              , constructs = snoc acc.constructs {construct = and.construct, relevantHere = and.relevantHere, length = length and.children}
              , constraint = optionBind acc.constraint (fs.constraintAnd and.constraint)
              , approx = optionMap (lam x. x.res) (optionBind acc.approx (_approxAnd and.approx))
              , relevantHere = fs.unionRelevant acc.relevantHere and.relevantHere
              , extraCost = addf acc.extraCost (mulf child.scale and.selfCost)
              , histories = snoc acc.histories and.history
              }
            case (None _, tree) then
              { acc with children = snoc acc.children {scale = child.scale, val = tree}
              , constructs = snoc acc.constructs {construct = lam. lam xs. head xs, relevantHere = x.relevantHere, length = 1}
              }
            end in
          match foldl addChild emptyMergeSpec children with spec & {constraint = Some constraint, approx = Some approx} then
            let constructs = spec.constructs in
            let x =
              { children = spec.children
              , selfCost = addf x.selfCost spec.extraCost
              , dep = Dep ()
              , construct = lam constraint. lam children.
                recursive let work = lam acc. lam constructs. lam children.
                  match constructs with [c] ++ constructs then
                    match splitAt children c.length with (here, children) in
                    let acc = snoc acc (c.construct (fs.filterConstraint c.relevantHere constraint) here) in
                    work acc constructs children
                  else if null children
                  then acc
                  else error "Compiler error: got more children in construct than flatten" in
                x.construct constraint (work [] constructs children)
              , constraint = constraint
              , approx = approx
              , relevantHere = spec.relevantHere
              , relevantAbove = x.relevantAbove
              , ident = None ()
              , history = HFlatten
                { label = "and-flatten"
                , parent = x.history
                , children = spec.histories
                }
              } in
            (Some x, RTAnd x)
          else error "Compiler error: flatten applied to inconsistent tree"
        else
          let children = map (lam child. {scale = child.scale, val = child.val.1}) children in
          let x = {x with children = children} in
          (Some x, RTAnd x)
      end
    in (work tree).1

let rtCartProd : all a. all constraint. all var. all val. all relevant. all ident.
  (constraint -> constraint -> Option constraint)
  -> [{approx : PureUnionFind var (Set val), constraint : constraint, value : [RTSingleRec a constraint var val relevant ident]}]
  -> [Lazy [RTSingleRec a constraint var val relevant ident]]
  -> [{approx : PureUnionFind var (Set val), constraint : constraint, value : [RTSingleRec a constraint var val relevant ident]}]
  = lam constraintAnd. lam prev. lam options.
    let stepElemElem = lam prev. lam new.
      match constraintAnd prev.constraint new.constraint with Some constraint then
        match _approxAnd prev.approx new.approx with Some approx then Some
          { constraint = constraint
          , approx = approx.res
          , value = snoc prev.value new
          }
        else None ()
      else None () in
    let stepListElem = lam acc. lam options.
      if null acc then acc else  -- NOTE(vipa, 2024-01-14): Early exit
      filterOption (seqLiftA2 stepElemElem acc (lazyForce options)) in
    foldl stepListElem prev options

type RTCollapseLeavesInterface env relevant constraint var val ident =
  { constraintAnd : constraint -> constraint -> Option constraint
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , constraintEq : constraint -> constraint -> Bool
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
let rtCollapseLeaves : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTCollapseLeavesInterface env relevant constraint var val ident
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam fs. lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    type Single a = RTSingleRec a constraint var val relevant ident in
    type Partial x = {approx : Approx, constraint : constraint, value : x} in
    let mapPartial : all x. all b. (x -> b) -> Partial x -> Partial b = lam f. lam x.
      { approx = x.approx
      , constraint = x.constraint
      , value = f x.value
      } in
    let stepElemElem : all a. Partial [Single a] -> Single a -> Option (Partial [Single a])
      = lam prev. lam new.
        match fs.constraintAnd prev.constraint new.constraint with Some constraint then
          match _approxAnd prev.approx new.approx with Some approx then Some
            { constraint = constraint
            , approx = approx.res
            , value = snoc prev.value new
            }
          else None ()
        else None ()
    in
    let stepListElem : all a. [Partial [Single a]] -> Lazy [Single a] -> [Partial [Single a]]
      = lam acc. lam options.
        if null acc then acc else  -- NOTE(vipa, 2024-01-14): Early exit
        filterOption (seqLiftA2 stepElemElem acc (lazyForce options))
    in
    recursive let work : all a.
      RepTree relevant constraint var val ident a
      -> (Option (Lazy [Single a]), RepTree relevant constraint var val ident a)
      = lam tree. switch tree
        case RTSingle x then
          let mkAlts = lam. [x]
          in (Some (lazy mkAlts), tree)
        case RTOr (x & {others = []}) then
          let x : RTOrRec Never a constraint var val relevant ident = x in
          let orFs =
            { constraintAnd = fs.constraintAnd
            , filterConstraint = fs.filterConstraint
            , filterApprox = fs.filterApprox
            , unionRelevant = fs.unionRelevant
            , mergeIdent = fs.mergeIdent
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "collapse-or"
            } in
          let mkAlts = lam. mapOption (rtConstructOr orFs x) x.singles in
          (Some (lazy mkAlts), tree)
        case RTOr x then
          let others = map (lam alt. (work alt).1) x.others in
          (None (), RTOr {x with others = others})
        case RTAnd x then
          let x : RTAndRec Never a constraint var val relevant ident = x in
          let andFs =
            { constraintAnd = fs.constraintAnd
            , filterConstraint = fs.filterConstraint
            , filterApprox = fs.filterApprox
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "collapse-child"
            , constraintEq = fs.constraintEq
            , debugInterface = fs.debugInterface
            , debugEnv = fs.debugEnv
            } in
          let children = map (lam child. work child.val) x.children in
          match optionMapM (lam x. x.0) children with Some children then
            let start =
              { constraint = x.constraint
              , approx = x.approx
              , value = []
              } in
            let results = rtCartProd fs.constraintAnd [start] children in
            let mkResult = lam result.
              let andFs =
                { andFs with preComputedConstraint = Some result.constraint
                , preComputedApprox = Some result.approx
                } in
              optionMap (lam x. RTSingle x) (rtConstructAnd andFs x result.value) in
            let res = RTOr
              { others = mapOption mkResult results
              , singles = []
              , selfCost = 0.0
              , construct = lam constraint. lam child. child
              , constraint = x.constraint
              , approx = x.approx
              , relevantHere = x.relevantHere
              , relevantAbove = x.relevantAbove
              , ident = None ()
              , history = HStep {label = "collapse-parent", prev = x.history}
              } in
            (None (), res)
          else
            let children = zipWith (lam old. lam new. {scale = old.scale, val = new.1}) x.children children in
            (None (), RTAnd {x with children = children})
        end
    in (work tree).1

type RTExtSol
con RTExtAnd : [RTExtSol] -> RTExtSol
con RTExtOr : {idx : Int, sub : RTExtSol} -> RTExtSol
con RTExtSingle : () -> RTExtSol
type RTSolveExternallyBaseInterface env relevant constraint var val ident =
  { constraintAnd : constraint -> constraint -> Option constraint
  , filterConstraint : relevant -> constraint -> constraint
  , filterApprox : relevant -> var -> Bool
  , unionRelevant : relevant -> relevant -> relevant
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , constraintEq : constraint -> constraint -> Bool
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
type RTSolveExternallyWorkInterface constraint acc query =
  { and : acc -> constraint -> Float -> [{scale : Float, val : query}] -> (acc, query)
  , or : acc -> constraint -> Float -> [query] -> (acc, query)
  , single : acc -> constraint -> Float -> (acc, query)
  , emptyAcc : acc
  }
let rtSolveExternally : all env. all relevant. all constraint. all var. all val. all a. all acc. all query. all ident.
  RTSolveExternallyBaseInterface env relevant constraint var val ident
  -> RTSolveExternallyWorkInterface constraint acc query
  -> RepTree relevant constraint var val ident a
  -> (acc, query, RTExtSol -> RTSingleRec a constraint var val relevant ident)
  = lam base. lam fs. lam tree.
    type Never in
    type Single a = RTSingleRec a constraint var val relevant ident in
    type Tree a = RepTree relevant constraint var val ident a in
    recursive let work
      : all a. acc -> Tree a -> (acc, (query, RTExtSol -> Single a))
      = lam acc. lam tree. switch tree
        case RTSingle x then
          match fs.single acc x.constraint x.cost with (acc, query) in
          (acc, (query, lam. x))
        case RTOr x then
          let x : RTOrRec Never a constraint var val relevant ident = x in
          let orFs =
            { constraintAnd = base.constraintAnd
            , filterConstraint = base.filterConstraint
            , filterApprox = base.filterApprox
            , unionRelevant = base.unionRelevant
            , mergeIdent = base.mergeIdent
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "external-or"
            } in
          match mapAccumL work acc (concat (map (lam x. RTSingle x) x.singles) x.others) with (acc, pairs) in
          match unzip pairs with (queries, mkFns) in
          match fs.or acc x.constraint x.selfCost queries with (acc, query) in
          let mk = lam sol.
            match sol with RTExtOr sol then
              let sub = (get mkFns sol.idx) sol.sub in
              match rtConstructOr orFs x sub with Some ret
              then ret
              else error "Compiler error: failed a constraintAnd for RTOr"
            else error "Compiler error: got a non-RTExtOr for an RTOr" in
          (acc, (query, mk))
        case RTAnd x then
          let x : RTAndRec Never a constraint var val relevant ident = x in
          let andFs =
            { constraintAnd = base.constraintAnd
            , filterConstraint = base.filterConstraint
            , filterApprox = base.filterApprox
            , preComputedConstraint = None ()
            , preComputedApprox = None ()
            , historyLabel = "external-and"
            , constraintEq = base.constraintEq
            , debugInterface = base.debugInterface
            , debugEnv = base.debugEnv
            } in
          let f = lam acc. lam child.
            match work acc child.val with (acc, (query, mk)) in
            (acc, ({scale = child.scale, val = query}, mk)) in
          match mapAccumL f acc x.children with (acc, pairs) in
          match unzip pairs with (queries, mkFns) in
          match fs.and acc x.constraint x.selfCost queries with (acc, query) in
          let mk = lam sol.
            match sol with RTExtAnd children then
              let children = zipWith (lam mk. lam child. mk child) mkFns children in
              match rtConstructAnd andFs x children with Some ret
              then ret
              else error "Compiler error: failed a constraintAnd for RTAnd"
            else error "Compiler error: got a nonRTExtAnd for an RTAnd" in
          (acc, (query, mk))
        end in
    match work fs.emptyAcc tree with (acc, (query, mk)) in
    (acc, query, mk)

let rtStateSpace : all relevant. all constraint. all var. all val. all a. all ident.
  RepTree relevant constraint var val ident a
  -> Int
  = lam tree.
    recursive let work = lam tree. switch tree
      case RTSingle _ then 1
      case RTAnd x then
        foldl muli 1 (map (lam c. work c.val) x.children)
      case RTOr x then
        let res = foldl addi 0 (map work x.others) in
        foldl addi res (map work (map (lam x. RTSingle x) x.singles))
      end
    in work tree

type RTEqInterface relevant constraint var val =
  { constraintEq : constraint -> constraint -> Bool
  , relevantEq : relevant -> relevant -> Bool
  }
let rtEq : all relevant. all constraint. all var. all val. all a. all ident.
  RTEqInterface relevant constraint var val
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  -> Bool
  = lam fs. lam a. lam b.
    type Approx = PureUnionFind var (Set val) in
    let approxEq : Approx -> Approx -> Bool = lam a. lam b.
      let cmp = mapGetCmpFun a in
      let pairEq = lam a. lam b.
        if not (eqi 0 (cmp a.0 b.0)) then false else
        if not (eqi a.1 b.1) then false else
        true in
      let f = lam a. lam b. pufFoldRaw
        (lam acc. lam l. lam r. if acc
         then eitherEq setEq pairEq (pufUnwrap a l) (pufUnwrap a r)
         else false)
        (lam acc. lam l. lam out. if acc
         then eitherEq setEq pairEq (pufUnwrap a l) (Left out)
         else false)
        true
        b in
      if f a b then f b a else false in
    recursive let historyEq : RTHistory -> RTHistory -> Bool = lam a. lam b. switch (a, b)
      case (HStart a, HStart b) then eqString a b
      case (HStep a, HStep b) then
        if not (eqString a.label b.label) then false else
        historyEq a.prev b.prev
      case (HAndConstruct a, HAndConstruct b) then
        if not (eqString a.label b.label) then false else
        if not (eqSeq historyEq a.children b.children) then false else
        historyEq a.prev b.prev
      case (HFlatten a, HFlatten b) then
        if not (eqString a.label b.label) then false else
        if not (eqSeq historyEq a.children b.children) then false else
        historyEq a.parent b.parent
      case (HOrConstruct a, HOrConstruct b) then
        if not (eqString a.label b.label) then false else
        if not (historyEq a.parent b.parent) then false else
        historyEq a.prev b.prev
      case _ then
        if eqi (constructorTag a) (constructorTag b)
        then error "Compiler error: missing equal case in historyEq"
        else false
      end in
    recursive
      let workSingle = lam a. lam b.
        if not (eqf a.cost b.cost) then false else
        if not (fs.relevantEq a.relevantHere b.relevantHere) then false else
        if not (fs.relevantEq a.relevantAbove b.relevantAbove) then false else
        if not (historyEq a.history b.history) then false else
        if not (approxEq a.approx b.approx) then false else
        if not (fs.constraintEq a.constraint b.constraint) then false else
        true
      let work = lam a. lam b. switch (a, b)
        case (RTSingle a, RTSingle b) then workSingle a b
        case (RTOr a, RTOr b) then
          if not (eqf a.selfCost b.selfCost) then false else
          if not (fs.relevantEq a.relevantHere b.relevantHere) then false else
          if not (fs.relevantEq a.relevantAbove b.relevantAbove) then false else
          if not (historyEq a.history b.history) then false else
          if not (approxEq a.approx b.approx) then false else
          if not (fs.constraintEq a.constraint b.constraint) then false else
          if not (eqSeq work a.others b.others) then false else
          if not (eqSeq workSingle a.singles b.singles) then false else
          true
        case (RTAnd a, RTAnd b) then
          let f = lam a. lam b.
            if not (eqf a.scale b.scale) then false else
            work a.val b.val in
          if not (eqi (constructorTag a.dep) (constructorTag b.dep)) then false else
          if not (eqf a.selfCost b.selfCost) then false else
          if not (fs.relevantEq a.relevantHere b.relevantHere) then false else
          if not (fs.relevantEq a.relevantAbove b.relevantAbove) then false else
          if not (historyEq a.history b.history) then false else
          if not (approxEq a.approx b.approx) then false else
          if not (fs.constraintEq a.constraint b.constraint) then false else
          if not (eqSeq f a.children b.children) then false else
          true
        end
    in work a b

let rtPruneRedundant : all a. all constraint. all var. all val. all relevant. all ident.
  ((constraint, Float) -> (constraint, Float) -> {lUseful : Bool, rUseful : Bool})
  -> [[RTSingleRec a constraint var val relevant ident]]
  -> [RTSingleRec a constraint var val relevant ident]
  = lam pruneRedundant. lam nonRedundantPartitions.
    type Single a = RTSingleRec a constraint var val relevant ident in
    let juggle = lam sing : Single a. (sing, (sing.constraint, sing.cost)) in
    let filterAccumL : all a. all x. all y. (a -> x -> (a, Bool)) -> a -> [x] -> (a, [x])
      = lam f.
        recursive let work = lam kept. lam acc. lam l.
          match l with [x] ++ l then
            match f acc x with (acc, keep) in
            work (if keep then snoc kept x else kept) acc l
          else (acc, kept)
        in work [] in
    recursive let work = lam pruned. lam rest.
      match rest with [new] ++ rest then
        let f = lam old. lam new. pruneRedundant old.1 new.1 in
        match filterAccumL (_pruneListElement f) pruned new with (pruned, new) in
        work (concat pruned new) rest
      else map (lam x. x.0) pruned
    in match map (map juggle) nonRedundantPartitions with [pruned] ++ rest
      then work pruned rest
      else error "Compiler error: empty list to pruneRedundant in rtPropagate"

let rtRecordSolution : all a. all constraint. all var. all val. all relevant. all ident.
  RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident (RepTreeSolution ident, a)
  = lam tree.
    type Never in
    type Single a = RTSingleRec a constraint var val relevant ident in
    type Tree a = RepTree relevant constraint var val ident a in
    type RTS = RepTreeSolution ident in
    let handleSingle : all a. Option Int -> Single a -> Single (RTS, a) = lam idx. lam x.
      let sol = RTSNode
        { ident = x.ident
        , orIdx = idx
        , children = []
        , cost = x.cost
        } in
      { value = (sol, x.value)
      , cost = x.cost
      , relevantHere = x.relevantHere
      , relevantAbove = x.relevantAbove
      , constraint = x.constraint
      , approx = x.approx
      , ident = x.ident
      , history = x.history
      } in
    recursive let work : all a. Option Int -> Tree a -> Tree (RTS, a) = lam idx. lam tree. switch tree
      case RTSingle x then RTSingle (handleSingle idx x)
      case RTOr x then
        let x : RTOrRec Never a constraint var val relevant ident = x in
        let singles = mapi (lam i. lam x. handleSingle (Some i) x) x.singles in
        let others =
          let nSingles = length singles in
          mapi (lam i. lam tree. work (Some (addi i nSingles)) tree) x.others in
        let res = RTOr
          { singles = singles
          , others = others
          , selfCost = x.selfCost
          , construct = lam c. lam o.
            (o.0, x.construct c o.1)
          , constraint = x.constraint
          , relevantHere = x.relevantHere
          , relevantAbove = x.relevantAbove
          , approx = x.approx
          , ident = x.ident
          , history = x.history
          } in
        res
      case RTAnd x then
        let x : RTAndRec Never a constraint var val relevant ident = x in
        let children = map
          (lam child. {scale = child.scale, val = work (None ()) child.val})
          x.children in
        let res = RTAnd
          { children = children
          , selfCost = x.selfCost
          , dep = x.dep
          , construct = lam constraint. lam xs.
            match unzip xs with (sols, xs) in
            let res = x.construct constraint xs in
            let sol = RTSNode
              { ident = x.ident
              , orIdx = idx
              , children = sols
              , cost = rtAndCost_ (lam x. match x with RTSNode x in x.cost) x sols
              } in
            (sol, res)
          , constraint = x.constraint
          , relevantHere = x.relevantHere
          , relevantAbove = x.relevantAbove
          , approx = x.approx
          , ident = x.ident
          , history = x.history
          } in
        res
      end
    in work (None ()) tree

type RTSFilterApproxInterface ident =
  { cmpIdent : ident -> ident -> Int
  }

let rtsFilterApprox : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTSFilterApproxInterface ident
  -> RepTreeSolution ident
  -> RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam fs. lam rts. lam tree.
    type Never in
    type Tree a = RepTree relevant constraint var val ident a in
    type And a = RTAndRec Never a constraint var val relevant ident in
    type Or a = RTOrRec Never a constraint var val relevant ident in
    type RTS = RepTreeSolution ident in
    type RMap in
    type REntry = {pat : Option ident, cont : RMap} in
    con RMap : Map Symbol REntry -> RMap in
    let unRMap : RMap -> Map Symbol REntry = lam x. match x with RMap x in x in

    let stepEntriesToMap : [REntry] -> Map Symbol REntry = lam rents.
      let addEntry = lam acc. lam x. mapUnion acc (unRMap x.cont) in
      foldl addEntry (mapEmpty _symCmp) rents in

    let dedupREntries : [REntry] -> [REntry] = lam rents.
      let m = foldl
        (lam a. lam x. mapInsertWith mapUnion x.pat (unRMap x.cont) a)
        (mapEmpty (optionCmp fs.cmpIdent))
        rents in
      mapFoldWithKey (lam a. lam ident. lam rents. snoc a {pat = ident, cont = RMap rents}) [] m
    in

    recursive let mkRMap : Map Symbol REntry -> RTS -> [REntry] = lam above. lam rts.
      let id = gensym () in
      match rts with RTSNode rts in
      let here = {pat = rts.ident, cont = RMap above} in
      if null rts.children
      then [here]
      else join (map (mkRMap (mapInsert id here (mapEmpty _symCmp))) rts.children)
    in

    recursive let filterTree
      : all a. [REntry] -> Tree a -> (Map Symbol REntry, Tree a)
      = lam rents. lam tree. switch tree
        case RTSingle _ then error "Compiler error: used rtsFilterApprox on a tree with singles"
        case RTOr x then
          let x : RTOrRec Never a constraint var val relevant ident = x in
          (if null x.singles then () else
           error "Compiler error: used rtsFilterApprox on a tree with singles");
          let others = map (filterTree rents) x.others in
          match partition (lam x. mapIsEmpty x.0) others with (misses, matches) in
          match matches with [(m, o)] ++ matches then
            match unzip matches with (maps, others) in
            (foldl mapUnion m maps, RTOr {x with others = cons o others})
          else (mapEmpty _symCmp, RTOr {x with others = map (lam x. x.1) misses})
        case RTAnd x then
          let x : RTAndRec Never a constraint var val relevant ident = x in
          match unzip (map (lam child. filterTree rents child.val) x.children) with (maps, children) in
          let rents =
            match maps with [m] ++ maps then
              let points = foldl (mapIntersectWith (lam a. lam. a)) m maps in
              mapFoldWithKey (lam a. lam. lam rent. snoc a rent) [] points
            else rents in
          let rents = filter (lam r. eqi 0 (optionCmp fs.cmpIdent r.pat x.ident)) rents in
          let children = zipWith (lam prev. lam new. {prev with val = new}) x.children children in
          (stepEntriesToMap rents, RTAnd {x with children = children})
        end
    in

    (filterTree (dedupREntries (mkRMap (mapEmpty _symCmp) rts)) tree).1
    -- (filterTree (mkRMap (None ()) rts) tree).1

let rtsToJson : all env. all ident. (env -> ident -> (env, JsonValue)) -> env -> RepTreeSolution ident -> (env, JsonValue)
  = lam identJson. lam env. lam rts.
    recursive let work = lam env. lam rts.
      match rts with RTSNode x in
      match optionMapAccum identJson env x.ident with (env, ident) in
      match mapAccumL work env x.children with (env, children) in
      let res = JsonObject (mapFromSeq cmpString
        [ ("ident", optionGetOr (JsonNull ()) ident)
        , ("orIdx", optionMapOr (JsonNull ()) (lam x. JsonInt x) x.orIdx)
        , ("children", JsonArray children)
        , ("cost", JsonFloat x.cost)
        ]) in
      (env, res)
    in work env rts

let rtsFromJson : all env. all ident. (env -> JsonValue -> Option (env, ident)) -> env -> JsonValue -> Option (env, RepTreeSolution ident)
  = lam identJson. lam env. lam json.
    let nullable : all x. (env -> JsonValue -> Option (env, x)) -> env -> JsonValue -> Option (env, Option x)
      = lam f. lam env. lam json.
        match json with JsonNull _ then Some (env, None ()) else
        optionMap (lam x. (x.0, Some x.1)) (f env json) in
    let getInt : env -> JsonValue -> Option (env, Int)
      = lam env. lam json.
        match json with JsonInt i then Some (env, i)
        else None () in
    recursive let work = lam env. lam json.
      match json with JsonObject x then
        match (mapLookup "ident" x, mapLookup "orIdx" x, mapLookup "children" x, mapLookup "cost" x)
        with (Some ident, Some orIdx, Some (JsonArray children), Some (JsonFloat cost)) then
          match nullable identJson env ident with Some (env, ident) then
            match optionMapAccumLM work env children with Some (env, children) then
              match nullable getInt env orIdx with Some (env, orIdx) then
                let res = RTSNode
                  { ident = ident
                  , orIdx = orIdx
                  , children = children
                  , cost = cost
                  } in
                Some (env, res)
              else None ()
            else None ()
          else None ()
        else None ()
      else None ()
    in work env json

type RTPStepKind
con RTPSOr : () -> RTPStepKind
con RTPSAnd : () -> RTPStepKind

type RTPosition ident
con RTPNil : all ident. () -> RTPosition ident
con RTPIdx : all ident. (RTPosition ident, RTPStepKind, Int) -> RTPosition ident
con RTPIdent : all ident. (RTPosition ident, Option ident) -> RTPosition ident

type RTFailure constraint var val ident =
  { pos : RTPosition ident
  , above : Option (constraint, PureUnionFind var (Set val))
  , here : (constraint, PureUnionFind var (Set val))
  }

let rtpToJson : all env. all ident. (env -> ident -> (env, JsonValue)) -> env -> RTPosition ident -> (env, JsonValue)
  = lam identJson. lam env. lam rtp.
    recursive let work = lam env. lam rtp. switch rtp
      case RTPNil _ then (env, [])
      case RTPIdx (prev, kind, idx) then
        match work env prev with (env, prev) in
        let kind = switch kind
          case RTPSAnd _ then "and "
          case RTPSOr _ then "or "
          end in
        (env, snoc prev (JsonString (concat kind (int2string idx))))
      case RTPIdent (prev, ident) then
        match work env prev with (env, prev) in
        match optionMapOr (env, JsonNull ()) (identJson env) ident with (env, res) in
        (env, snoc prev res)
      end in
    match work env rtp with (env, rtp) in
    (env, JsonArray rtp)

let rtfToJson : all env. all relevant. all constraint. all var. all val. all ident. RTDebugInterface env relevant constraint var val ident -> env -> RTFailure constraint var val ident -> (env, JsonValue)
  = lam fs. lam env. lam failure.
    let optToJson = lam f. lam env. lam x. optionMapOr (env, JsonNull ()) (f env) x in
    let pairToJson = lam env. lam pair.
      match fs.constraintJson env pair.0 with (env, constraint) in
      match _rtApproxJson fs env pair.1 with (env, approx) in
      let res = JsonObject (mapFromSeq cmpString
        [ ("constraint", constraint)
        , ("approx", approx)
        ]) in
      (env, res) in
    match rtpToJson fs.identJson env failure.pos with (env, pos) in
    match optToJson pairToJson env failure.above with (env, above) in
    match pairToJson env failure.here with (env, here) in
    let res = JsonObject (mapFromSeq cmpString
      [ ("pos", pos)
      , ("above", above)
      , ("here", here)
      ]) in
    (env, res)

type RTPropagateInterface env relevant constraint var val ident =
  { constraintAnd : constraint -> constraint -> Option {lChanged : Bool, rChanged : Bool, res : constraint}
  , filterApprox : relevant -> var -> Bool
  , filterConstraint : relevant -> constraint -> constraint
  , unionRelevant : relevant -> relevant -> relevant
  , pruneRedundant : Option ((constraint, Float) -> (constraint, Float) -> {lUseful : Bool, rUseful : Bool})
  , mergeIdent : {parent : Option ident, child : Option ident} -> Option ident
  , constraintEq : constraint -> constraint -> Bool
  , recordFailures : Bool
  , debugInterface : RTDebugInterface env relevant constraint var val ident
  , debugEnv : env
  }
let rtPropagate : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTPropagateInterface env relevant constraint var val ident
  -> RepTree relevant constraint var val ident a
  -> ([RTFailure constraint var val ident], Option (RepTree relevant constraint var val ident a))
  = lam fs. lam tree.
    type Never in
    type Never2 in
    type Approx = PureUnionFind var (Set val) in
    type Single a = RTSingleRec a constraint var val relevant ident in
    type Status in
    con Unchanged : () -> Status in
    con ChangedUnresolved : Approx -> Status in
    con ChangedResolved : (constraint, Approx) -> Status in
    let filterApprox = lam relevant. lam puf.
      pufFilterFunction (lam pair. fs.filterApprox relevant pair.0) puf in
    let constrainFs =
      { constraintAnd = fs.constraintAnd
      , filterConstraint = fs.filterConstraint
      , filterApprox = fs.filterApprox
      } in
    let constrain
      : relevant -> Option (constraint, Approx) -> constraint -> Approx -> Option {changed : Bool, approx : Approx, constraint : constraint}
      = lam relevant. lam fromAbove. lam hConstraint. lam hApprox.
        match fromAbove with Some above then
          let res = rtConstrainShallow constrainFs {above = above, here = (hConstraint, hApprox), relevantHere = relevant} in
          match res with Some res then
            Some {changed = res.0, constraint = res.1 .0, approx = res.1 .1}
          else
            let f =
              { pos = RTPNil ()
              , above = fromAbove
              , here = (hConstraint, hApprox)
              } in
            None ()
        else Some {changed = false, constraint = hConstraint, approx = hApprox} in
    let pruneRedundant : all a. [[Single a]] -> [Single a] = match fs.pruneRedundant with Some f
      then lam x. rtPruneRedundant f x
      else join in
    let failures : Ref [RTFailure constraint var val ident] = ref [] in
    let workSingle
      : all a. RTPosition ident -> Option (constraint, Approx) -> Single a -> Option (Status, Single a)
      = lam pos. lam fromAbove. lam x.
        match constrain x.relevantHere fromAbove x.constraint x.approx with Some res then
          let status = if res.changed
            then ChangedResolved (res.constraint, res.approx)
            else Unchanged () in
          let res = {x with constraint = res.constraint, approx = res.approx} in
          Some (status, res)
        else
          (if fs.recordFailures then
            let failure =
              { pos = RTPIdent (pos, x.ident)
              , above = fromAbove
              , here = (x.constraint, x.approx)
              } in
            modref failures (snoc (deref failures) failure)
           else ());
          None () in
    recursive
      let workD : all a.
        RTPosition ident
        -> Bool
        -> Option (constraint, Approx)
        -> RepTree relevant constraint var val ident a
        -> Option (Status, RepTree relevant constraint var val ident a)
        = lam pos. lam forceDepth. lam fromAbove. lam tree.
          if fs.recordFailures then
            -- NOTE(vipa, 2024-03-25): This currently records every
            -- point where we return `None`, even if the `None` is
            -- trivially because a child was `None`, i.e., the current
            -- point was not the cause.
            let pos = RTPIdent (pos, rtGetIdent tree) in
            let res = work pos forceDepth fromAbove tree in
            (if optionIsNone res then
              let failure =
                { pos = pos
                , above = fromAbove
                , here = (rtGetConstraint tree, rtGetApprox tree)
                } in
              modref failures (snoc (deref failures) failure)
             else ());
            res
          else work pos forceDepth fromAbove tree
      let work : all a.
        RTPosition ident
        -> Bool
        -> Option (constraint, Approx)
        -> RepTree relevant constraint var val ident a
        -> Option (Status, RepTree relevant constraint var val ident a)
        = lam pos. lam forceDepth. lam fromAbove. lam tree. switch tree
          case RTSingle x then optionMap (lam x. (x.0, RTSingle x.1)) (workSingle pos fromAbove x)
          -- TODO(vipa, 2024-01-14): This is incorrect for some reason,
          -- and I can't figure out why. It skips constraints somehow,
          -- so the solution might segfault.
          -- case RTAnd (x & {children = [child]}) then
          --   let fixedConstruct : [Never] -> a = x.construct in
          --   match constrainFromAbove fromAbove (Some x.relevantHere) x.constraint x.approx with Some res then
          --     let newTree = rtMap (lam c. fixedConstruct [c]) child.val in
          --     let newTree = rtScale child.scale newTree in
          --     let newTree = rtMapRelevantHere (fs.unionRelevant x.relevantHere) newTree in
          --     let newTree = rtSetRelevantAbove x.relevantAbove newTree in
          --     work forceDepth (Some (res.constraint, res.approx)) newTree
          --   else None ()
          case RTAnd x then
            let x : RTAndRec Never a constraint var val relevant ident = x in
            let constrain = constrain x.relevantHere in
            match constrain fromAbove x.constraint x.approx with Some res then
              let propagateDown = if forceDepth then true else res.changed in
              recursive let inner
                : Bool -> {changed : Bool, constraint : constraint, approx : Approx} -> [Unknown] -> Unknown
                = lam forceDepth. lam acc. lam children.
                  let f = lam acc. lam childIdx. lam child.
                    let pos = RTPIdx (pos, RTPSAnd (), childIdx) in
                    match workD pos forceDepth (Some (acc.constraint, acc.approx)) child.val with Some (status, val) then
                      let acc = switch status
                        case Unchanged _ then Some acc
                        case ChangedUnresolved a then
                          match constrain (Some (x.constraint, a)) acc.constraint acc.approx with Some res then
                            Some {acc with approx = res.approx, constraint = res.constraint, changed = or acc.changed res.changed}
                          else None ()
                        case ChangedResolved a then
                          match constrain (Some a) acc.constraint acc.approx with Some res then
                            Some
                            { acc with changed = if acc.changed then true else res.changed
                            , constraint = res.constraint
                            , approx = res.approx
                            }
                          else None ()
                        end in
                      optionMap (lam acc. (acc, {child with val = val})) acc
                    else None () in
                  match optionMapiAccumLM f {acc with changed = false} children with Some (newAcc, children) then
                    if newAcc.changed
                    then inner false newAcc children
                    else Some ({newAcc with changed = acc.changed}, children)
                  else None ()
              in
              match
                if propagateDown then
                  inner forceDepth {changed = res.changed, constraint = res.constraint, approx = res.approx} x.children
                else Some ({changed = false, constraint = res.constraint, approx = res.approx}, x.children)
              with Some (acc, children) then
                match optionMapM (lam child. rtAsSingle child.val) children with Some values then
                  let newFs =
                    { constraintAnd = lam a. lam b. optionMap (lam x. x.res) (fs.constraintAnd a b)
                    , filterConstraint = fs.filterConstraint
                    , filterApprox = fs.filterApprox
                    , preComputedConstraint = Some acc.constraint
                    , preComputedApprox = Some acc.approx
                    , historyLabel = "propagate-trivial-and"
                    , constraintEq = fs.constraintEq
                    , debugInterface = fs.debugInterface
                    , debugEnv = fs.debugEnv
                    } in
                  let f = lam r.
                    let status = ChangedResolved (r.constraint, r.approx) in
                    (status, RTSingle r) in
                  optionMap f (rtConstructAnd newFs x values)
                else
                  let status = if acc.changed
                    then ChangedResolved (acc.constraint, acc.approx)
                    else Unchanged () in
                  let res = RTAnd {x with constraint = acc.constraint, approx = acc.approx, children = children} in
                  Some (status, res)
              else None ()
            else None ()
          case RTOr x then
            let x : RTOrRec Never a constraint var val relevant ident = x in
            let constrain = constrain x.relevantHere in
            let orFs =
              { constraintAnd = lam a. lam b. optionMap (lam x. x.res) (fs.constraintAnd a b)
              , filterConstraint = fs.filterConstraint
              , filterApprox = fs.filterApprox
              , unionRelevant = fs.unionRelevant
              , mergeIdent = fs.mergeIdent
              , preComputedConstraint = None ()
              , preComputedApprox = None ()
              , historyLabel = "propagate-trivial-or"
              } in
            match constrain fromAbove x.constraint x.approx with Some res then
              let propagateDown = if forceDepth then true else res.changed in
              if propagateDown then
                let singles = mapiOption
                  (lam i. workSingle (RTPIdx (pos, RTPSOr (), i)) (Some (res.constraint, res.approx)))
                  x.singles in
                let off = length x.singles in
                let others = mapiOption
                  (lam i. workD (RTPIdx (pos, RTPSOr (), addi i off)) forceDepth (Some (res.constraint, res.approx)))
                  x.others in
                switch (singles , others)
                case ([], []) then None ()
                case ([(status, res)], []) then
                  optionMap (lam x. (status, RTSingle x)) (rtConstructOr orFs x res)
                case ([], [(status, res)]) then
                  optionMap (lam x. (status, x)) (rtConstructOrTree orFs x res)
                case (singlePairs, otherPairs) then
                  let changed =
                    if res.changed then true else
                    if neqi (addi (length x.others) (length x.singles)) (addi (length otherPairs) (length singlePairs)) then true else
                    if not (forAll (lam pair. match pair.0 with Unchanged _ then true else false) singlePairs) then true else
                    not (forAll (lam pair. match pair.0 with Unchanged _ then true else false) otherPairs) in
                  let filterSingle : all x. Single x -> Single x = lam x.
                    { x with constraint = fs.filterConstraint x.relevantAbove x.constraint
                    , approx = filterApprox x.relevantAbove x.approx
                    } in
                  let fixChild = lam pair. switch pair.1
                    case RTSingle x then This [ filterSingle x ]
                    case tree & RTOr or then
                      let or : RTOrRec Never2 Never constraint var val relevant ident = or in
                      let orFs = {orFs with historyLabel = "propagate-or-flatten"} in
                      let singles = map filterSingle or.singles in
                      let singles = if null singles then [] else pruneRedundant (map (lam x. [x]) singles) in
                      let singles = mapOption (rtConstructOr orFs or) singles in
                      let others = mapOption (rtConstructOrTree orFs or) or.others in
                      These (singles, others)
                    case x then That [x]
                    end in
                  match thesePartitionHereThere (map fixChild otherPairs) with (newSingles, others) in
                  let others = join others in
                  let singles = pruneRedundant (cons (map (lam x. x.1) singlePairs) newSingles) in
                  match _computeAltApprox res.approx (concat (map (lam x. RTSingle x) singles) others) with Some approx then
                    -- NOTE(vipa, 2024-01-14): Prune redundant can cause
                    -- the situation where there's just a single left,
                    -- even though there were multiple earlier, so we
                    -- check that here
                    match (singles, others) with ([sing], []) then
                      let status = ChangedResolved (sing.constraint, sing.approx) in
                      optionMap (lam x. (status, RTSingle x)) (rtConstructOr orFs x sing)
                    else
                      let status = if changed
                        then ChangedUnresolved (approx)
                        else Unchanged () in
                      let res = RTOr {x with constraint = res.constraint, approx = approx, singles = singles, others = others} in
                      Some (status, res)
                  else None ()
                end
              else Some (Unchanged (), RTOr {x with constraint = res.constraint, approx = res.approx})
            else None ()
          end
    in
    let res = optionMap (lam x. x.1) (workD (RTPNil ()) true (None ()) tree) in
    (deref failures, res)

let rtHomogenizeTop : all env. all relevant. all constraint. all var. all val. all a. all ident.
  (val -> val -> Int)
  -> RepTree relevant constraint var val ident a
  -> [RepTree relevant constraint var val ident a]
  = lam cmpVal. lam tree.
    let approx = rtGetApprox tree in
    let vals = pufFoldRaw
      (lam a. lam. lam. a)
      (lam a. lam k. lam vals. setUnion a vals)
      (setEmpty cmpVal)
      approx in
    let vals = setToSeq vals in
    let stepWith = lam prev. lam val.
      let singleton = setInsert val (setEmpty cmpVal) in
      let f = lam v. if setMem val v then singleton else v in
      pufMapOut f prev in
    recursive let stepAll = lam seen. lam toStep.
      let needMore = pufFoldRaw
        (lam a. lam. lam. a)
        (lam a. lam. lam vals. if a then a else gti (setSize vals) 1)
        false in
      match partition needMore toStep with (needMore, enough) in
      match needMore with [] then enough else
      let res = seqLiftA2 stepWith needMore vals in
      -- NOTE(vipa, 2024-01-25): Since all approxes come from the same
      -- one, and the only change we've made has been to map `out`s, we
      -- know that they are physically equal exactly if they are equal,
      -- thus this is a valid way to deduplicate them.
      let res = setOfSeq (pufPhysicalCmp setCmp) res in
      let res = setSubtract res seen in
      let seen = setUnion seen res in
      concat enough (stepAll seen (setToSeq res)) in
    let approxes = stepAll (setEmpty (pufPhysicalCmp setCmp)) [approx] in
    map (lam approx. rtSetApprox approx tree) approxes

type RTMaterializeHomogeneousInterface env relevant constraint var val ident =
  { propagateInterface : RTPropagateInterface env relevant constraint var val ident
  , constraintAnd : constraint -> constraint -> Option constraint
  , cmpVal : val -> val -> Int
  }

let rtMaterializeHomogeneous : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RTMaterializeHomogeneousInterface env relevant constraint var val ident
  -> RepTree relevant constraint var val ident a
  -> Option (RTSingleRec a constraint var val relevant ident)
  = lam fs. lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    type Tree a = RepTree relevant constraint var val ident a in
    type Single a = RTSingleRec a constraint var val relevant ident in
    let pruneRedundant = match fs.propagateInterface.pruneRedundant with Some f
      then rtPruneRedundant f
      else join in
    let cmpf = lam a. lam b. if ltf a b then negi 1 else if gtf a b then 1 else 0 in
    let orFs =
      { constraintAnd = fs.constraintAnd
      , filterConstraint = fs.propagateInterface.filterConstraint
      , filterApprox = fs.propagateInterface.filterApprox
      , unionRelevant = fs.propagateInterface.unionRelevant
      , mergeIdent = fs.propagateInterface.mergeIdent
      , preComputedConstraint = None ()
      , preComputedApprox = None ()
      , historyLabel = "homogeneous-or"
      } in
    let andFs =
      { constraintAnd = fs.constraintAnd
      , filterConstraint = fs.propagateInterface.filterConstraint
      , filterApprox = fs.propagateInterface.filterApprox
      , preComputedConstraint = None ()
      , preComputedApprox = None ()
      , historyLabel = "homogeneous-and"
      , constraintEq = fs.propagateInterface.constraintEq
      , debugInterface = fs.propagateInterface.debugInterface
      , debugEnv = fs.propagateInterface.debugEnv
      } in
    recursive
      let descend : all a. Tree a -> [Single a] = lam tree.
        let approx = rtGetApprox tree in
        let approxHasUnfixedVars = pufFoldRaw
          (lam a. lam. lam. a)
          (lam a. lam. lam v. if a then true else gti (setSize v) 1)
          false
          approx in
        if approxHasUnfixedVars
        then pickApprox approx tree
        else switch tree
          case RTSingle x then [x]
          case RTOr x then
            let x : RTOrRec Never a constraint var val relevant ident = x in
            let others = join (map descend x.others) in
            let res = pruneRedundant (cons x.singles (map (lam x. [x]) others)) in
            mapOption (rtConstructOr orFs x) res
          case RTAnd x then
            let x : RTAndRec Never a constraint var val relevant ident = x in
            let children = map
              (lam child. lazy (lam. descend child.val))
              x.children in
            let start =
              { constraint = x.constraint
              , approx = x.approx
              , value = []
              } in
            let results = rtCartProd fs.constraintAnd [start] children in
            let mkResult = lam result.
              let andFs =
                { andFs with preComputedConstraint = Some result.constraint
                , preComputedApprox = Some result.approx
                } in
              rtConstructAnd andFs x result.value in
            mapOption mkResult results
          end
      let pickApprox : all a. Approx -> Tree a -> [Single a] = lam approx. lam tree.
        let mkTup = lam vals.
          if eqi 1 (setSize vals)
          then mapMap (lam. (1, 1)) vals
          else mapMap (lam. (0, 1)) vals in
        let addTup = lam a. lam b.
          (addi a.0 b.0, addi a.1 b.1) in
        let cmpTup = lam a. lam b.
          let res = subi a.0 b.0 in
          if neqi res 0 then res else
          subi a.1 b.1 in
        let valsWithCount = pufFold
          (lam a. lam. lam. a)
          (lam a. lam. lam vals.
            mapUnionWith addTup (mkTup vals) a)
          (mapEmpty fs.cmpVal)
          approx in
        let valsInOrder =
          -- NOTE(vipa, 2024-01-22): Reverse order, i.e., highest
          -- count first
          let x = sort (lam a. lam b. cmpTup b.1 a.1) (mapBindings valsWithCount) in
          map (lam x. x.0) x in
        let homogeneousApprox =
          let empty = setEmpty fs.cmpVal in
          let pickVal = lam prev.
            let v = find (lam v. setMem v prev) valsInOrder in
            optionMapOr empty (lam v. setInsert v empty) v in
          pufMapOut pickVal approx in
        let constrainedTree = rtPropagate fs.propagateInterface
          (rtSetApprox homogeneousApprox tree) in
        match constrainedTree with (_, Some constrainedTree)
        then descend constrainedTree
        else []
    in
    let solutions = descend tree in
    min (lam a. lam b. cmpf a.cost b.cost) solutions

let rtFilterReprs : all env. all relevant. all constraint. all var. all val. all a. all ident.
  RepTree relevant constraint var val ident a
  -> RepTree relevant constraint var val ident a
  = lam tree.
    type Never in
    type Approx = PureUnionFind var (Set val) in
    type Tree a = RepTree relevant constraint var val ident a in
    type Single a = RTSingleRec a constraint var val relevant ident in
    recursive let work
      : all a. Tree a -> (Option Approx, Tree a)
      = lam tree. switch tree
        case RTSingle x then
          (Some x.approx, tree)
        case RTOr x then
          let others = map (lam x. (work x).1) x.others in
          if null x.others then
            match x.singles with [sing] ++ sings then
              let f = lam acc. lam sing.
                if ltf acc.cost sing.cost then acc else
                if gtf acc.cost sing.cost then {cost = sing.cost, cheapest = [sing.approx]} else
                {acc with cheapest = snoc acc.cheapest sing.approx} in
              let cheapest = (foldl f {cost = sing.cost, cheapest = [sing.approx]} sings).cheapest in
              match _computeAltApproxDirect x.approx cheapest with Some approx
              then (Some approx, tree)
              else (Some x.approx, tree)
            else (None (), tree)
          else (None (), RTOr {x with others = others})
        case RTAnd x then
          let updateChild = lam child.
            match work child.val with (approx, val) in
            (approx, {child with val = val}) in
          match unzip (map updateChild x.children) with (approxes, children) in
          match optionMapM (lam x. x) approxes with Some approxes then
            let approx = _computeAltApproxDirect x.approx approxes in
            let approx = match approx with Some approx then approx
              else warnSingle [] "AltApprox in FilterReprs failed"; x.approx in
            (None (), RTAnd {x with children = children, approx = approx})
          else (None (), RTAnd {x with children = children})
        end
    in (work tree).1


type SolForError
con SFEHere : {here : Info, needed : use Ast in Type, got : use Ast in Type} -> SolForError
con SFEBelow : {opUses : [{call : Info, name : Name, below : SolForError}], here : Info} -> SolForError
con SFEOr : [SolForError] -> SolForError

lang NonMemoTreeBuilder = RepTypesShallowSolverInterface + UnifyPure + RepTypesHelpers + PrettyPrint + Cmp + Generalize + VarAccessHelpers + LocallyNamelessStuff + WildToMeta
  -- Global
  syn SolverGlobal a = | SGContent ()
  sem initSolverGlobal = | _ -> SGContent ()

  -- Branch
  type SBContent a =
    { implsPerOp : Map Name (Set (OpImpl a))
    , nameless : NamelessState
    }
  syn SolverBranch a = | SBContent (SBContent a)
  sem initSolverBranch = | global -> SBContent
    { implsPerOp = mapEmpty nameCmp
    , nameless =
      { metas = []
      , vars = []
      , reprs = []
      }
    }

  type SolContentRec a =
    { scaledTotalCost : OpCost
    , uni : Unification
    , impl : OpImpl a
    , highestImpl : ImplId
    , ty : Type
    , subSols : [SolContent a]
    }
  syn SolContent a = | SolContent (SolContentRec a)
  syn SolverSolution a = | SSContent (SolContent a)

  type Relevant = VarMap Int  -- NOTE(vipa, 2024-01-21): The meta-level/repr-scope of the var
  type Constraint = Unification
  type Var = Symbol
  type Val = Name
  -- NOTE(vipa, 2024-03-21): We work with strings directly (well,
  -- SIDs) instead on names to be stable across compiler runs
  type NodeIdent =
    { name : SID
    -- NOTE(vipa, 2024-03-21): A bag of opUses
    , opUses : Map SID Int
    -- NOTE(vipa, 2024-03-21): A sequence of explicit repr
    -- assignments, in order. Order assumed to be a tad more stable
    -- and meaningful, since the type doesn't change as easily
    , reprSubsts : [SID]
    }
  sem nodeIdentJson : all env. env -> NodeIdent -> (env, JsonValue)
  sem nodeIdentJson env = | ident ->
    let fromSid = lam sid. JsonString (sidToString sid) in
    let opUses = mapFoldWithKey
      (lam acc. lam sid. lam count. concat acc (make count (fromSid sid)))
      []
      ident.opUses in
    let res = JsonObject (mapFromSeq cmpString
      [ ("name", JsonString (sidToString ident.name))
      , ("opUses", JsonArray opUses)
      , ("reprs", JsonArray (map fromSid ident.reprSubsts))
      ]) in
    (env, res)
  sem nodeIdentFromJson : all env. env -> JsonValue -> Option (env, NodeIdent)
  sem nodeIdentFromJson env = | json ->
    match json with JsonObject m then
      match (mapLookup "name" m, mapLookup "opUses" m, mapLookup "reprs" m)
      with (Some (JsonString name), Some (JsonArray opUses), Some (JsonArray reprSubsts)) then
        let asString = lam x. match x with JsonString x then Some x else None () in
        match (optionMapM asString opUses, optionMapM asString reprSubsts)
        with (Some opUses, Some reprSubsts) then
          let addUse = lam acc. lam opUse. mapInsertWith addi (stringToSid opUse) 1 acc in
          let ident =
            { name = stringToSid name
            , opUses = foldl addUse (mapEmpty cmpSID) opUses
            , reprSubsts = map stringToSid reprSubsts
            } in
          Some (env, ident)
        else None ()
      else None ()
    else None ()

  -- Top Query
  type RTree a = RepTree Relevant Constraint Var Val NodeIdent (SolContent a)
  type STQContent a = [{scale : OpCost, val : RTree a}]
  syn SolverTopQuery a = | STQContent (STQContent a)
  sem initSolverTopQuery = | global ->
    STQContent []

  sem addImpl global branch = | impl ->
    match branch with SBContent branch in
    let branch =
      let set = setInsert impl (setEmpty cmpOpImpl) in
      {branch with implsPerOp = mapInsertWith setUnion impl.op set branch.implsPerOp} in
    SBContent branch

  sem addOpUse debug global branch query = | opUse ->
    match branch with SBContent branch in
    match query with STQContent query in
    switch solFor (setEmpty cmpOpPair) branch opUse
    case (branch, Left err) then
      recursive let removeAliases = lam ty.
        match ty with TyAlias x
        then removeAliases x.content
        else smap_Type_Type removeAliases ty in
      recursive let constructTree = lam indent. lam err. switch err
        case SFEHere x then join
          [ indent, "- Type mismatch: ", info2str x.here, "\n"
          , indent, "  (needed ", type2str (removeAliases x.needed), ")\n"
          , indent, "  (got ", type2str (removeAliases x.got), ")\n"
          ]
        case SFEBelow x then
          let iindent = snoc indent ' ' in
          let iiindent = snoc iindent ' ' in
          let showOpUse = lam opUse. join
            [ iindent, "- ", nameGetStr opUse.name, " ", info2str opUse.call, "\n"
            , constructTree iiindent opUse.below
            ] in
          let msg = join
            [ indent, "- ", info2str x.here, ":\n"
            , join (map showOpUse x.opUses)
            ] in
          msg
        case SFEOr errs then
          join (map (constructTree indent) errs)
        end in
      recursive let constructTrace = lam acc. lam err. switch err
        case SFEHere x then snoc acc (x.here, "Type does not fit.")
        case SFEBelow {opUses = [first] ++ _} then
          constructTrace (snoc acc (first.call, "Because of this operation:")) first.below
        case SFEOr [x] then
          constructTrace acc x
        case SFEOr [] then
          snoc acc (NoInfo (), "No implementations available.")
        case SFEOr _ then
          let msg = join ["Multiple implementations available, but none were valid.\n", constructTree "" err] in
          snoc acc (NoInfo (), msg)
        end
      in errorMulti (constructTrace [(opUse.info, "This operation has no implementation")] err) "Could not find implementations, even when ignoring constraints from other operation uses."
    case (branch, Right res) then
      (SBContent branch, STQContent (snoc query {scale = opUse.scaling, val = res}))
    end

  sem debugSolution global = | sols ->
    let sum = foldl addf 0.0 (map (lam x. match x with SSContent (SolContent x) in x.scaledTotalCost) sols) in
    recursive let work = lam indent. lam sol.
      match sol with SolContent sol in
      let op = nameGetStr sol.impl.op in
      let scaledCost = float2string sol.scaledTotalCost in
      let info = info2str sol.impl.info in
      match unificationToDebug (concat indent "| ") pprintEnvEmpty sol.uni with (env, uni) in
      let msg = join
        [ indent, op, "(scaled cost: ", scaledCost, ", info: ", info, ")\n"
        , uni, "\n"
        , join (map (lam x. work (concat indent "  ") x) sol.subSols)
        ] in
      msg
    in join
      [ "\n# Solution cost tree (total: ", float2string sum, "):\n"
      , join (map (lam s. match s with SSContent x in work "" x) sols)
      ]

  sem concretizeSolution global = | SSContent (SolContent x) ->
    (x.impl.token, x.highestImpl, map (lam x. SSContent x) x.subSols)

  sem cmpSolution a = | b ->
    match (a, b) with (SSContent a, SSContent b) in
    recursive let work = lam a. lam b.
      match (a, b) with (SolContent a, SolContent b) in
      let res = subi a.impl.implId b.impl.implId in
      if neqi 0 res then res else
      seqCmp work a.subSols b.subSols
    in work a b

  sem solFor : all a. Set (Name, Type) -> SBContent a -> TmOpVarRec -> (SBContent a, Either SolForError (RTree a))
  sem solFor seen branch = | opUse ->
    -- NOTE(vipa, 2024-01-13): Check that we're not recursing to a
    -- previously seen type
    let nl = mkLocallyNameless branch.nameless opUse.ty in
    let branch = {branch with nameless = nl.state} in
    let opPair = (opUse.ident, nl.res) in
    if setMem opPair seen then (branch, Left (SFEOr [])) else  -- Early exit
    let seen = setInsert opPair seen in

    -- NOTE(vipa, 2024-01-13): Construct sub-trees for each impl in
    -- scope for the op
    let impls = optionMapOr [] setToSeq (mapLookup opUse.ident branch.implsPerOp) in
    match mapAccumL (perImpl seen opUse.ty) branch impls with (branch, trees) in
    match eitherPartition trees with (fails, trees) in
    if null trees then (branch, Left (SFEOr fails)) else  -- Early exit

    -- NOTE(vipa, 2024-01-13): Build the "or" node of those
    -- alternatives
    match _computeAltApprox (pufEmpty _symCmp) trees with Some approx then
      let relevant = foldl1 varMapUnion (map rtGetRelevantAbove trees) in
      let res = RTOr
        { others = trees
        , singles = []
        , selfCost = 0.0
        , construct = lam. lam x. x
        , constraint = emptyUnification ()
        , relevantAbove = relevant
        , relevantHere = relevant
        , approx = approx
        , ident = None ()
        , history = HStart (concat (nameGetStr opUse.ident) "-or")
        } in
      (branch, Right res)
    else (branch, Left (SFEOr []))

  sem perImpl : all a. Set (Name, Type) -> Type -> SBContent a -> OpImpl a -> (SBContent a, Either SolForError (RTree a))
  sem perImpl seen ty branch = | impl ->
    -- NOTE(vipa, 2024-01-21): Isolate this impl instance from all
    -- others by creating new repr- and meta-vars for each such var
    -- that is only local, i.e., has a level equal or higher to the
    -- impls's level
    let specType = impl.specType in
    let opUses = impl.opUses in
    let uni = impl.uni in
    let refEnv = ref pprintEnvEmpty in
    let implFilter = {metaLevel = impl.metaLevel, scope = impl.reprScope} in
    let locals =
      let res = varMapEmpty in
      let res = getVarsInType implFilter res specType in
      foldl (lam acc. lam opUse. getVarsInType implFilter acc opUse.ty) res opUses in
    let subst =
      { metas = mapMapWithKey (lam k. lam lvl. (nameSetNewSym k, lvl)) locals.metas
      , reprs = mapMap (lam scope. (gensym (), scope)) locals.reprs
      } in
    let specType = substUniVars subst specType in
    let opUses = map (lam opUse. {opUse with ty = substUniVars subst opUse.ty}) opUses in
    let uni = substUniVarsInUni subst uni in
    (if mapIsEmpty uni.types then () else
     error "Sanity check failed: the uni in an impl should start without type unifications, it should only have repr unifications and substitutions.");

    let varsInTy = getVarsInType {metaLevel = negi 1, scope = negi 1} varMapEmpty ty in

    -- NOTE(vipa, 2024-01-21): Instantiate, transform TyWild to
    -- meta-vars in the requested type, unify.
    match wildToMeta impl.metaLevel (setEmpty nameCmp) ty with (newMetas, ty) in
    match instAndSubst (infoTy specType) impl.metaLevel specType
      with (specType, instSubst) in
    let specNoSubst = removeReprSubsts specType in
    match unifyPure uni specNoSubst ty with Some uni then
      -- NOTE(vipa, 2024-01-21): Figure out which vars can be made
      -- equal simply via substitution (`simplSubst`) rather than
      -- keeping an entry in the `uni`, under the assumption that only
      -- the given set *must* remain as distinct vars.
      let reprExternallyVisible = lam pair.
        if lti pair.1 impl.reprScope then true else varMapHasRepr pair.0 varsInTy in
      let metaExternallyVisible = lam pair.
        if lti pair.1 impl.metaLevel then true else varMapHasMeta pair.0 varsInTy in
      match simplifyUniWithKeep reprExternallyVisible metaExternallyVisible uni with (uni, simplSubst) in

      -- NOTE(vipa, 2024-01-13): Make types consistent with the
      -- instantiation, then the uni simplification, then with the
      -- unification
      let updateOpUseType = lam opUse.
        let ty = substituteVars opUse.info instSubst opUse.ty in
        let ty = substUniVars simplSubst ty in
        let ty = pureApplyUniToType uni ty in
        {opUse with ty = ty} in
      let opUses = map updateOpUseType opUses in

      match mapAccumL (solFor seen) branch opUses with (branch, subTrees) in
      match optionMapM (lam x. eitherGetRight x) subTrees with Some subTrees then
        let approx = pufFoldRaw
          (lam acc. lam l. lam r.
            (pufUnify (lam. error "Compiler error when computing approx (unify)") l r acc).puf)
          (lam acc. lam l. lam out.
            let out = setInsert out (setEmpty nameCmp) in
            (pufSetOut (lam. error "Compiler error when computing approx (setout)") l out acc).puf)
          (pufEmpty _symCmp)
          uni.reprs in
        let approx = foldl _intersectApproxFromBelow approx subTrees in
        if _approxHasEmptyDomain approx then (branch, Left (SFEHere {here = impl.info, needed = ty, got = specNoSubst})) else -- Early exit

        -- NOTE(vipa, 2024-01-21): A var is relevant here if it's
        -- relevant below (i.e., in `relevantAbove` of a child) or
        -- changed in this impl, i.e., is assigned in the `uni`
        let relevantHere =
          let below = foldl varMapUnion varMapEmpty (map rtGetRelevantAbove subTrees) in
          let reprsHere = pufFoldRaw
            (lam a. lam l. lam r. mapInsert l.0 l.1 (mapInsert r.0 r.1 a))
            (lam a. lam l. lam. mapInsert l.0 l.1 a)
            (mapEmpty _symCmp)
            uni.reprs in
          let metasHere = pufFoldRaw
            (lam a. lam l. lam r. mapInsert l.0 l.1 (mapInsert r.0 r.1 a))
            (lam a. lam l. lam. mapInsert l.0 l.1 a)
            (mapEmpty nameCmp)
            uni.types in
          varMapUnion below {reprs = reprsHere, metas = metasHere} in
        -- NOTE(vipa, 2024-01-21): A var is relevant above if it is
        -- relevant here and is externally visible
        let relevantAbove =
          { reprs = mapFromSeq _symCmp (filter reprExternallyVisible (mapBindings relevantHere.reprs))
          , metas = mapFromSeq nameCmp (filter metaExternallyVisible (mapBindings relevantHere.metas))
          } in
        let res = RTAnd
          { children =
            zipWith (lam opUse. lam tree. {scale = opUse.scaling , val = tree}) opUses subTrees
          , dep = Dep ()
          , selfCost = impl.selfCost
          , construct = lam uni. lam subs.
            let applyScale = lam opUse. lam sol.
              match sol with SolContent sol in
              SolContent {sol with scaledTotalCost = mulf opUse.scaling sol.scaledTotalCost} in
            let subs = zipWith applyScale opUses subs in
            let totalCost = foldl (lam a. lam x. match x with SolContent x in addf a x.scaledTotalCost)
              impl.selfCost subs in
            let highestImpl = foldl (lam a. lam x. match x with SolContent x in maxi a x.highestImpl)
              impl.implId subs in
            let res = SolContent
              { scaledTotalCost = totalCost
              , uni = uni
              , impl = impl
              , highestImpl = highestImpl
              , ty = specType
              , subSols = subs
              } in
            res
          , constraint = uni
          , relevantHere = relevantHere
          , relevantAbove = relevantAbove
          , approx = approx
          , ident = Some
            { name = stringToSid (nameGetStr impl.op)
            , opUses = foldl
              (lam a. lam opUse. mapInsertWith addi (stringToSid (nameGetStr opUse.ident)) 1 a)
              (mapEmpty cmpSID)
              impl.opUses
            , reprSubsts =
              recursive let work = lam acc. lam ty.
                let acc = match unwrapType ty with TySubst x
                  then snoc acc (stringToSid (nameGetStr x.subst))
                  else acc in
                sfold_Type_Type work acc ty
              in work [] impl.originalSpecType
            }
          , history = HStart (concat (nameGetStr impl.op) "-impl")
          } in
        (branch, Right res)
      else
        let f = lam opUse. lam either. optionMap
          (lam x. {call = opUse.info, below = x, name = opUse.ident})
          (eitherGetLeft either) in
        (branch, Left (SFEBelow {opUses = mapOption (lam x. x) (zipWith f opUses subTrees), here = impl.info}))
    else (branch, Left (SFEHere {here = impl.info, needed = ty, got = specNoSubst}))

  -- NOTE(vipa, 2023-11-07): This typically assumes that the types
  -- have a representation that is equal if the two types are
  -- alpha-equivalent.
  sem cmpOpPair : (Name, Type) -> (Name, Type) -> Int
  sem cmpOpPair l = | r ->
    let res = nameCmp l.0 r.0 in
    if neqi 0 res then res else
    let res = cmpType l.1 r.1 in
    res
end

lang TreeSolverBase = NonMemoTreeBuilder
  type TSTree a = RepTree Relevant Constraint Var Val NodeIdent a
  type TSSingle a = RTSingleRec a Constraint Var Val Relevant NodeIdent
  type RTS = RepTreeSolution NodeIdent

  sem solveWork : all a. Bool -> Option RTS -> TSTree a -> a
  sem solveWorkAll : all a. Bool -> TSTree a -> [a]

  sem topSolve debug file global = | STQContent query ->
    let top = RTAnd
      { children = query
      , selfCost = 0.0
      , dep = Dep ()
      , construct = lam. lam x. map (lam x. SSContent x) x
      , constraint = emptyUnification ()
      , relevantHere = foldl varMapUnion varMapEmpty (map (lam x. rtGetRelevantAbove x.val) query)
      , relevantAbove = varMapEmpty
      , approx = foldl _intersectApproxFromBelow (pufEmpty _symCmp) (map (lam x. x.val) query)
      , ident = None ()
      , history = HStart "root"
      } in
    match file with Some file then
      let rts =
        if fileExists file then
          switch jsonParse (readFile file)
          case Left json then
            optionMap (lam x. x.1) (rtsFromJson nodeIdentFromJson () json)
          case Right err then
            warnSingle [] err;
            None ()
          end
        else None () in
      let saveSol = lam res.
        match res with (rts, sol) in
        writeFile file (json2string (rtsToJson nodeIdentJson () rts).1);
        sol in
      saveSol (solveWork debug rts (rtRecordSolution top))
    else solveWork debug (None ()) top
  sem topSolveAll debug global = | STQContent query ->
    let top = RTAnd
      { children = query
      , selfCost = 0.0
      , dep = Dep ()
      , construct = lam. lam x. map (lam x. SSContent x) x
      , constraint = emptyUnification ()
      , relevantHere = foldl varMapUnion varMapEmpty (map (lam x. rtGetRelevantAbove x.val) query)
      , relevantAbove = varMapEmpty
      , approx = foldl _intersectApproxFromBelow (pufEmpty _symCmp) (map (lam x. x.val) query)
      , ident = None ()
      , history = HStart "root"
      } in
    solveWorkAll debug top

  sem mkEqInterface : () -> RTEqInterface Relevant Constraint Var Val
  sem mkEqInterface = | _ ->
    { constraintEq = lam a. lam b. if uniImplies a b then uniImplies b a else false
    , relevantEq = varMapEq (lam. lam. true)
    }

  sem mkPropagateInterface : () -> RTPropagateInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkPropagateInterface = | _ ->
    { constraintAnd = lam l. lam r.
      match mergeUnifications l r with Some res then Some
        -- NOTE(vipa, 2023-12-12): We know (by construction) that
        -- res implies both l and r (because `mergeUnifications` is
        -- a logical 'and') so we don't need to check that here
        { lChanged = not (uniImplies l res)
        , rChanged = not (uniImplies r res)
        , res = res
        }
      else None ()
    , unionRelevant = varMapUnion
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , constraintEq = lam a. lam b. if uniImplies a b then uniImplies b a else false
    , debugEnv = pprintEnvEmpty
    , debugInterface = mkDebugInterface ()
    , mergeIdent = lam x. optionOr x.parent x.child
    , recordFailures = false
    , pruneRedundant =
      let f = lam l. lam r.
        let lFitsWhereRCouldBe = lazy (lam. uniImplies r.0 l.0) in
        let rFitsWhereLCouldBe = lazy (lam. uniImplies l.0 r.0) in
        let lUsefulHelper = lam l. lam r. lam lFits. lam rFits.
          -- NOTE(vipa, 2024-01-14): Strictly cheaper is always useful
          if ltf l.1 r.1 then true else
          -- NOTE(vipa, 2024-01-14): Otherwise it's only useful if it's provably more flexible
          not (lazyForce rFits) in
        let rUseful = lUsefulHelper r l rFitsWhereLCouldBe lFitsWhereRCouldBe in
        -- NOTE(vipa, 2024-01-14): At least one must be useful, thus
        -- we default to `l` if `r` fails to be useful on its own
        if not rUseful then { lUseful = true, rUseful = false } else
        let lUseful = lUsefulHelper l r lFitsWhereRCouldBe rFitsWhereLCouldBe in
        { lUseful = lUseful, rUseful = rUseful }
      in Some f
    }

  sem mkDebugInterface : () -> RTDebugInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkDebugInterface = | _ ->
    { constraintJson = lam env. lam uni.
      match unificationToDebug "" env uni with (env, uni) in
      (env, JsonString uni)
    , varJson = lam env. lam sym. (env, JsonString (int2string (sym2hash sym)))
    , valJson = lam env. lam ident.
      match pprintVarName env ident with (env, ident) in
      (env, JsonString ident)
    , relevantJson = lam env. lam varmap.
      match mapAccumL pprintVarName env (mapKeys varmap.metas) with (env, metas) in
      let reprs = map (lam x. int2string (sym2hash x)) (mapKeys varmap.reprs) in
      let res = JsonObject (mapFromSeq cmpString
        [ ("metas", JsonArray (map (lam x. JsonString x) metas))
        , ("reprs", JsonArray (map (lam x. JsonString x) reprs))
        ]) in
      (env, res)
    , identJson = nodeIdentJson
    }

  sem mkCollapseLeavesInterface : () -> RTCollapseLeavesInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkCollapseLeavesInterface = | _ ->
    { constraintAnd = mergeUnifications
    , unionRelevant = varMapUnion
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , constraintEq = lam a. lam b. if uniImplies a b then uniImplies b a else false
    , mergeIdent = lam x. optionOr x.parent x.child
    , debugEnv = pprintEnvEmpty
    , debugInterface = mkDebugInterface ()
    }

  sem mkFlattenInterface : () -> RTFlattenInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkFlattenInterface = | _ ->
    { constraintAnd = mergeUnifications
    , unionRelevant = varMapUnion
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , debugEnv = pprintEnvEmpty
    , debugInterface = mkDebugInterface ()
    }

  sem mkFilterApproxInterface : () -> RTSFilterApproxInterface NodeIdent
  sem mkFilterApproxInterface = | _ ->
    { cmpIdent = lam a. lam b.
      let res = cmpSID a.name b.name in
      if neqi res 0 then res else
      let res = mapCmp subi a.opUses b.opUses in
      if neqi res 0 then res else
      let res = seqCmp cmpSID a.reprSubsts b.reprSubsts in
      res
    }

  sem mkMaterializeHomogeneousInterface : () -> RTMaterializeHomogeneousInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkMaterializeHomogeneousInterface = | _ ->
    { constraintAnd = mergeUnifications
    , cmpVal = nameCmp
    , propagateInterface = mkPropagateInterface ()
    }

  sem mkMaterializeStatelessInterface : () -> RTMaterializeStatelessInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkMaterializeStatelessInterface = | _ ->
    { constraintAnd = mergeUnifications
    , constraintEq = lam a. lam b. if uniImplies a b then uniImplies b a else false
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , unionRelevant = varMapUnion
    , constraintEmpty = emptyUnification ()
    , mergeIdent = lam x. optionOr x.parent x.child
    , debugEnv = pprintEnvEmpty
    , debugInterface = mkDebugInterface ()
    }

  sem mkMaterializeLazyInterface : () -> RTMaterializeLazyInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkMaterializeLazyInterface = | _ ->
    { constraintAnd = mergeUnifications
    , unionRelevant = varMapUnion
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , pruneRedundant = lam l. lam r.
      let lFits = uniImplies r l in
      let rUseful = not lFits in
      if not rUseful then { lUseful = true, rUseful = false } else
      let rFits = uniImplies l r in
      { lUseful = not rFits
      , rUseful = rUseful
      }
    , constraintEq = lam a. lam b. if uniImplies a b then uniImplies b a else false
    , mergeIdent = lam x. optionOr x.parent x.child
    , debugEnv = pprintEnvEmpty
    , debugInterface = mkDebugInterface ()
    }

  sem mkMaterializeConsistentInterface : () -> RTMaterializeConsistentInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkMaterializeConsistentInterface = | _ ->
    { partitionConsistentConstraints =
      let f : all x. [(x, Constraint)] -> [([x], Constraint)] = lam pairs.
        recursive let addToFirst : [([x], Constraint)] -> (x, Constraint) -> [([x], Constraint)]
          = lam partitions. lam pair.
            match partitions with [part] ++ partitions then
              match mergeUnifications part.1 pair.1 with Some uni
              then cons (snoc part.0 pair.0, uni) partitions
              else cons part (addToFirst partitions pair)
            else [([pair.0], pair.1)] in
        foldl addToFirst [] pairs
      in #frozen"f"
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , unionRelevant = varMapUnion
    , constraintAnd = mergeUnifications
    , constraintImplies = uniImplies
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , constraintEq = lam a. lam b. if uniImplies a b then uniImplies b a else false
    , mergeIdent = lam x. optionOr x.parent x.child
    , debugInterface = mkDebugInterface ()
    , debugEnv = pprintEnvEmpty
    }

  sem mkSolveExternallyBaseInterface : () -> RTSolveExternallyBaseInterface PprintEnv Relevant Constraint Var Val NodeIdent
  sem mkSolveExternallyBaseInterface = | _ ->
    { constraintAnd = mergeUnifications
    , unionRelevant = varMapUnion
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , constraintEq = lam a. lam b. if uniImplies a b then uniImplies b a else false
    , mergeIdent = lam x. optionOr x.parent x.child
    , debugEnv = pprintEnvEmpty
    , debugInterface = mkDebugInterface ()
    }

  sem mkPartitionInternalInterface : () -> RTPartitionInternalInterface Relevant Constraint Var Val
  sem mkPartitionInternalInterface = | _ ->
    { varsToRelevant = lam vars.
      { reprs = mapFromSeq _symCmp (map (lam x. (x, negi 1)) vars)
      , metas = mapEmpty nameCmp
      }
    , emptyRelevant = varMapEmpty
    , subtractRelevant = varMapDifference
    , intersectRelevant = varMapIntersect
    , normalizeRelevantToConstraint = lam uni. lam varmap.
      { reprs = mapFoldWithKey
        (lam acc. lam r. lam i.
          match pufUnwrapN uni.reprs (r, i) with (r, i) in
          mapInsert r i acc)
        (mapEmpty _symCmp)
        varmap.reprs
      , metas = mapFoldWithKey
        (lam acc. lam m. lam i.
          match pufUnwrapN uni.types (m, i) with (m, i) in
          mapInsert m i acc)
        (mapEmpty nameCmp)
        varmap.metas
      }
    , filterConstraint = lam varmap. lam uni. filterUnificationFunction
      (lam pair. varMapHasRepr pair.0 varmap)
      (lam pair. varMapHasMeta pair.0 varmap)
      uni
    , filterApprox = lam varmap. lam sym. varMapHasRepr sym varmap
    , fixedInConstraint = lam uni.
      -- NOTE(vipa, 2024-01-15): A repr-var is fully fixed as soon as
      -- it has an `out` in a `uni`, since it can only be a single
      -- named repr.
      let reprs = pufFold
        (lam a. lam. lam. a)
        (lam a. lam l. lam. mapInsert l.0 l.1 a)
        (mapEmpty _symCmp)
        uni.reprs in
      -- NOTE(vipa, 2024-01-15): A meta-var is fixed if it points to a
      -- type and all (repr and meta) vars in that type are fully
      -- fixed.
      -- let metas = pufFold
      --   (lam a. lam. lam. a)
      --   (lam a. lam l. lam ty.)
      --   (setEmpty nameCmp)
      --   uni.types in
      let metas = mapEmpty nameCmp in
      { reprs = reprs
      , metas = metas
      }
    , unionRelevant = varMapUnion
    , partitionRelevant =
      let eitherCmp = lam l. lam r. lam a. lam b.
        let res = subi (constructorTag a) (constructorTag b) in
        if neqi 0 res then res else
        switch (a, b)
        case (Left a, Left b) then l a b
        case (Right a, Right b) then r a b
        end in
      let f : all x. [(x, Relevant)] -> [[x]] = lam inputs.
        let merge = lam a. lam b. ((), setUnion a b) in
        let processInput = lam accPair. lam i. lam pair.
          match accPair with (puf, lonely) in
          let varmap = pair.1 in
          let reprs = mapKeys (varmap.reprs) in
          let reprs = map (lam x. Left x) reprs in
          let metas = mapKeys (varmap.metas) in
          let metas = map (lam x. Right x) metas in
          match concat reprs metas with [center] ++ rest then
            let puf = foldl (lam puf. lam x. (pufUnify merge (center, 0) (x, 0) puf).puf) puf rest in
            ((pufSetOut merge (center, 0) (setInsert i (setEmpty subi)) puf).puf, lonely)
          else (puf, snoc lonely [(get inputs i).0]) in
        match foldli processInput (pufEmpty (eitherCmp _symCmp nameCmp), []) inputs
          with (partitionedIdxes, lonely) in
        let partitionedIdxes = pufFoldRaw
          (lam a. lam. lam. a)
          (lam a. lam. lam set. snoc a (map (lam i. (get inputs i).0) (setToSeq set)))
          []
          partitionedIdxes in
        concat partitionedIdxes lonely
      in #frozen"f"
    }
end

lang TreeSolverGreedy = TreeSolverBase
  sem solveWork debug prev = | top ->
    let propagateInterface = mkPropagateInterface () in
    let debugInterface = mkDebugInterface () in
    let materializeLazyInterface = mkMaterializeLazyInterface () in
    let partitionInternalInterface = mkPartitionInternalInterface () in
    match rtPropagate propagateInterface top with (_, Some top) then
      -- let top = rtPartitionInternalComponents partitionInternalInterface top in
      let stream = rtMaterializeLazyRecursive materializeLazyInterface top in
      match lazyStreamUncons stream with Some (res, _) then res else
      errorSingle [] "Could not find a consistent assignment of impls across the program"
    else errorSingle [] "Could not find a consistent assignment of impls across the program"
end

lang TreeSolverGuided = TreeSolverBase
  sem solveWork debug prev = | top ->
    let propagateInterface = mkPropagateInterface () in
    let partitionInternalInterface = mkPartitionInternalInterface () in
    let materializeConsistentInterface = mkMaterializeConsistentInterface () in
    match rtPropagate propagateInterface top with (_, Some top) then
      let top = rtPartitionInternalComponents partitionInternalInterface top in
      match rtPropagate propagateInterface top with (_, Some top) then
        match rtMaterializeConsistent materializeConsistentInterface top with Some res then
          res.value
        else errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)"
      else errorSingle [] "Could not find a consistent assignment of impls across the program"
    else errorSingle [] "Could not find a consistent assignment of impls across the program"
end
lang Z3Stuff = TreeSolverBase + MExprAst
  type Z3State =
    { vars : VarMap ()
    , env : PprintEnv
    , reprs : Set Name
    , tyCons : Set Name
    , labels : Set SID
    }
  syn Ast =
  | AAnd [Ast]
  | AOr [Ast]
  | AEq (Ast, Ast)
  | AAdd [Ast]
  | AMul [Ast]
  | ALit String
  | ALet (String, Ast, Ast)
  | AMatch (String, [(String, Ast)], Option Ast)
  | AMatchI (String, [(Int, Ast)], Ast)

  sem getReprVar : Z3State -> Symbol -> (Z3State, String)
  sem getReprVar state = | sym ->
    let vars = {state.vars with reprs = setInsert sym state.vars.reprs} in
    match pprintEnvGetStr state.env ("rv_", sym) with (env, str) in
    ({state with vars = vars, env = env}, str)

  sem getMetaVar : Z3State -> Name -> (Z3State, String)
  sem getMetaVar state = | name ->
    let vars = {state.vars with metas = setInsert name state.vars.metas} in
    match pprintEnvGetStr state.env name with (env, str) in
    ({state with vars = vars, env = env}, concat "m_" str)

  sem getRepr : Z3State -> Name -> (Z3State, String)
  sem getRepr state = | name ->
    let reprs = setInsert name state.reprs in
    match pprintEnvGetStr state.env name with (env, str) in
    ({state with reprs = reprs, env = env}, concat "r_" str)

  sem getTyCon : Z3State -> Name -> (Z3State, String)
  sem getTyCon state = | name ->
    let tyCons = setInsert name state.tyCons in
    match pprintEnvGetStr state.env name with (env, str) in
    ({state with tyCons = tyCons, env = env}, concat "c_" str)

  sem getLabel : Z3State -> SID -> (Z3State, String)
  sem getLabel state = | sid ->
    let labels = setInsert sid state.labels in
    ({state with labels = labels}, concat "l_" (sidToString sid))

  sem tyToZ3 : [Name] -> Z3State -> Type -> (Z3State, String)
  sem tyToZ3 boundTyVars state =
  | ty -> errorSingle [infoTy ty] "Missing case in tyToZ3"
  | TyBool _ -> (state, "boolTy")
  | TyInt _ -> (state, "intTy")
  | TyFloat _ -> (state, "floatTy")
  | TyChar _ -> (state, "charTy")
  | TyArrow x ->
    match tyToZ3 boundTyVars state x.from with (state, from) in
    match tyToZ3 boundTyVars state x.to with (state, to) in
    (state, join ["(funTy ", from, " ", to, ")"])
  | TySeq x ->
    match tyToZ3 boundTyVars state x.ty with (state, ty) in
    (state, join ["(seqTy ", ty, ")"])
  | TyRecord x ->
    match mapMapAccum (lam a. lam. lam v. tyToZ3 boundTyVars a v) state x.fields with (state, fields) in
    match unzip (mapBindings fields) with (labels, types) in
    match mapAccumL getLabel state labels with (state, labels) in
    let inUnit = lam x. join ["(seq.unit ", x, ")"] in
    let asSeq = lam ty. lam xs. match xs with []
      then join ["(as seq.empty (Seq ", ty, "))"]
      else join ["(seq.++ ", strJoin " " (map inUnit xs), ")"] in
    (state, join ["(recordTy ", asSeq "Label" labels, " ", asSeq "Ty" types, ")"])
  | TyCon x ->
    match getTyCon state x.ident with (state, tycon) in
    (state, join ["(conTy ", tycon, ")"])
  | TyVar x ->
    match index (nameEq x.ident) boundTyVars with Some idx then
      (state, join ["(boundTyVar ", int2string idx, ")"])
    else
      -- NOTE(vipa, 2024-01-18): Tyvars that are rigid (i.e., not
      -- bound with an `all` inside the current type) are
      -- indistinguishable from type constructors for the current
      -- purposes, thus they are encoded the same
      match getTyCon state x.ident with (state, tycon) in
      (state, join ["(conTy ", tycon, ")"])
  | TyAll x ->
    let boundTyVars = cons x.ident boundTyVars in
    match tyToZ3 boundTyVars state x.ty with (state, ty) in
    (state, join ["(forallTy ", ty, ")"])
  | TyApp x ->
    match tyToZ3 boundTyVars state x.lhs with (state, lhs) in
    match tyToZ3 boundTyVars state x.rhs with (state, rhs) in
    (state, join ["(appTy ", lhs, " ", rhs, ")"])
  | TyAlias x -> tyToZ3 boundTyVars state x.content
  | ty & TyMetaVar _ -> switch unwrapType ty
    case TyMetaVar x then
      match deref x.contents with Unbound u then
        getMetaVar state u.ident
      else error "Compiler error: unwrapType didn't unwrap a TyMetaVar"
    case ty then
      tyToZ3 boundTyVars state ty
    end
  | TyRepr x ->
    match deref (botRepr x.repr) with BotRepr u then
      match tyToZ3 boundTyVars state x.arg with (state, arg) in
      match getReprVar state u.sym with (state, sym) in
      (state, join ["(reprTy ", sym, " ", arg, ")"])
    else error "Compiler error: found a repr without an initialized repr var"
  | TyWild _ ->
    printError "Warning: tyToZ3 found a TyWild, should not be possible";
    (state, "wildTy")

  sem uniToZ3 : Z3State -> Unification -> (Z3State, [Ast])
  sem uniToZ3 state = | uni ->
    let f = lam getVar. lam getOut. lam state. lam equalities. lam puf. pufFoldRaw
      (lam acc. lam l. lam r.
        let st = acc.0 in
        match getVar st l.0 with (st, l) in
        match getVar st r.0 with (st, r) in
        (st, snoc acc.1 (AEq (ALit l, ALit r))))
      (lam acc. lam l. lam out.
        let st = acc.0 in
        match getVar st l.0 with (st, l) in
        match getOut st out with (st, out) in
        (st, snoc acc.1 (AEq (ALit l, ALit out))))
      (state, equalities)
      puf in
    let equalities = [] in
    match f getReprVar getRepr state equalities uni.reprs with (state, equalities) in
    match f getMetaVar (tyToZ3 []) state equalities uni.types with (state, equalities) in
    (state, equalities)

  sem pprintZ3Helper : String -> String -> [Ast] -> String
  sem pprintZ3Helper indent label = | children ->
    let f = lam x. match x with ALit str then Some str else None () in
    match optionMapM f children with Some simples then
      join ["(", label, " ", strJoin " " simples, ")"]
    else
      let indent = concat indent " " in
      join ["(", label, join (map (lam c. join ["\n", indent, pprintZ3Ast indent c]) children), ")"]

  sem pprintZ3Ast : String -> Ast -> String
  sem pprintZ3Ast indent =
  | AAnd xs -> pprintZ3Helper indent "and" xs
  | AOr xs -> pprintZ3Helper indent "or" xs
  | AEq (l, r) -> pprintZ3Helper indent "=" [l, r]
  | AAdd xs -> pprintZ3Helper indent "+" xs
  | AMul xs -> pprintZ3Helper indent "*" xs
  | ALit str -> str
  | ALet (label, body, inexpr) ->
    let indent = concat indent " " in
    join
    [ "(let ((", label, " ", pprintZ3Ast indent body, "))\n"
    , indent, pprintZ3Ast indent inexpr, ")"
    ]
  | AMatch (scrut, arms, default) ->
    let indent = concat indent " " in
    let iindent = concat indent " " in
    let iindent = concat iindent " " in
    let arms = match default with Some default
      then snoc arms ("_", default)
      else arms in
    let f = lam arm. switch arm
      case (pat, ALit str) then join ["(", pat, " ", str, ")"]
      case (pat, body) then join ["(", pat, "\n", iindent, pprintZ3Ast iindent body, ")"]
      end in
    join [ "(match ", scrut, "\n", indent, "(", strJoin (concat "\n" iindent) (map f arms), "))"]
  | AMatchI (scrut, arms, default) ->
    let iindent = concat indent " " in
    let f = lam arm. lam acc.
      match arm with (idx, body) in
      join ["(ite (= ", scrut, " ", int2string idx, ")\n", iindent, pprintZ3Ast iindent body, "\n", indent, acc, ")"] in
    foldr f (pprintZ3Ast iindent default) arms

  sem parseZ3Output : String -> Option RTExtSol
  sem parseZ3Output =
  | _ -> None ()
  | "sat\n\"" ++ str ++ "\"\n" ->
    recursive let ltrim = lam str.
      switch str
      case "" then str
      case " " ++ str then ltrim str
      case str then str
      end in
    let partitionWhile : all a. (a -> Bool) -> [a] -> ([a], [a]) = lam pred. lam seq.
      match index (lam x. not (pred x)) seq with Some idx
      then splitAt seq idx
      else (seq, []) in
    let repeatUntilNone : all a. all x. (x -> Option (a, x)) -> x -> ([a], x) = lam f.
      recursive let work = lam acc. lam x.
        match f x with Some (a, x) then
          work (snoc acc a) x
        else (acc, x)
      in work [] in
    recursive let parseOne = lam str.
      switch ltrim str
      case "(and " ++ str then
        match repeatUntilNone parseOne str with (children, str) in
        match ltrim str with ")" ++ str in
        Some (RTExtAnd children, str)
      case "(or " ++ str then
        match partitionWhile isDigit str with (digits, str) in
        let str = ltrim str in
        match parseOne str with Some (child, str) then
          match ltrim str with ")" ++ str in
          Some (RTExtOr {idx = string2int digits, sub = child}, str)
        else None ()
      case "single" ++ str then
        Some (RTExtSingle (), str)
      case _ then
        None ()
      end in
    match parseOne str with Some (rt, str)
    then if null str then Some rt else error (concat "Extra stuff left in str: " str)
    else None ()

  sem solveWithZ3 : all a. TSTree a -> Option (TSSingle a)
  sem solveWithZ3 = | tree ->
    let solveExternallyBaseInterface = mkSolveExternallyBaseInterface () in
    let prelude = strJoin "\n"
      [ "(declare-datatypes ((Sol 0))"
      , "  (((solAnd (solChildren (Seq Sol)))"
      , "    (solOr (solIndex Int) (solChild Sol))"
      , "    solSingle)))"
      , ""
      , "(define-funs-rec"
      , "  ((pp-sol ((sol Sol)) String)"
      , "   (recur-child ((sol Sol)) String)"
      , "   (concat ((a String) (b String)) String))"
      , "  ((match sol"
      , "    (((solAnd children)"
      , "      (let ((subs (seq.map recur-child children)))"
      , "        (str.++ \"(and\" (seq.foldl concat \"\" subs) \")\")))"
      , "     ((solOr idx child)"
      , "      (str.++ \"(or \" (int.to.str idx) \" \" (pp-sol child) \")\"))"
      , "     (solSingle"
      , "      \"single\")))"
      , "   (str.++ \" \" (pp-sol sol))"
      , "   (str.++ a b)))"
      ] in
    let midlude = strJoin "\n"
      [ "(declare-datatypes ((Ty 0))"
      , "  (((appTy (fTy Ty) (argTy Ty))"
      , "    boolTy intTy floatTy charTy wildTy ostringTy olistTy"
      , "    (opaqueTy (opaque String))"
      , "    (seqTy (elemTy Ty))"
      , "    (conTy (const ConstTy))"
      , "    (reprTy (rep RepTy) (repArgTy Ty))"
      , "    (forallTy (quantTy Ty))"
      , "    (boundTyVar (debruijn Int))"
      , "    (recordTy (fieldLabels (Seq Label)) (fieldTypes (Seq Ty)))"
      , "    (funTy (fromTy Ty) (toTy Ty)))))"
      ] in
    type Query = {costExpr : Ast, boolExpr : Ast} in
    let interface =
      -- NOTE(vipa, 2024-01-18): All expressions assume that the
      -- solution to examine is bound to `sol`
      { and =
        let f : Z3State -> Unification -> OpCost -> [{scale : OpCost, val : Query}] -> (Z3State, Query)
          = lam st. lam uni. lam cost. lam children.
            let childToCost = lam idx. lam child. ALet
              ( "sol"
              , ALit (join ["(seq.nth ss ", int2string idx, ")"])
              , AMul [ALit (float2string child.scale), child.val.costExpr]
              ) in
            let costExpr = AMatch
              ( "sol"
              , [("(solAnd ss)" , AAdd (cons (ALit (float2string cost)) (mapi childToCost children)))]
              , Some (ALit "999999999999.9")
              ) in
            let childToBool = lam idx. lam child. ALet
              ( "sol"
              , ALit (join ["(seq.nth ss ", int2string idx, ")"])
              , child.val.boolExpr
              ) in
            match uniToZ3 st uni with (st, predicates) in
            let lenEq = AEq (ALit "(seq.len ss)", ALit (int2string (length children))) in
            let boolExpr = AMatch
              ( "sol"
              , [("(solAnd ss)", AAnd (join [[lenEq], predicates, mapi childToBool children]))]
              , Some (ALit "false")
              ) in
            (st, {costExpr = costExpr, boolExpr = boolExpr})
        in f
      , or =
        let f : Z3State -> Unification -> OpCost -> [Query] -> (Z3State, Query)
          = lam st. lam uni. lam cost. lam alts.
            let altToCost = lam idx. lam alt.
              (idx, alt.costExpr) in
            let costExpr =
              let matchIdx = AMatchI ("idx", mapi altToCost alts, ALit "999999999999.9") in
              let matchShape = AMatch ("sol", [("(solOr idx sol)", matchIdx)], Some (ALit "999999999999.9")) in
              AAdd [ALit (float2string cost), matchShape] in
            let altToBool = lam idx. lam alt. (idx, alt.boolExpr) in
            let boolExpr =
              AMatch ("sol", [("(solOr idx sol)", AMatchI ("idx", mapi altToBool alts, ALit "false"))], Some (ALit "false")) in
            match uniToZ3 st uni with (st, predicates) in
            let boolExpr = AAnd (snoc predicates boolExpr) in
            (st, {costExpr = costExpr, boolExpr = boolExpr})
        in f
      , single =
        let f : Z3State -> Unification -> OpCost -> (Z3State, Query)
          = lam st. lam uni. lam cost.
            let costExpr = ALit (float2string cost) in
            match uniToZ3 st uni with (st, predicates) in
            let boolExpr = AAnd (cons (ALit "(= sol solSingle)") predicates) in
            (st, {costExpr = costExpr, boolExpr = boolExpr})
        in f
      , emptyAcc =
        { vars = varMapEmpty
        , env = pprintEnvEmpty
        , reprs = setEmpty nameCmp
        , tyCons = setEmpty nameCmp
        , labels = setEmpty cmpSID
        }
      } in
    match rtSolveExternally solveExternallyBaseInterface interface tree with (state, query, mk) in
    match mapAccumL getTyCon state (setToSeq state.tyCons) with (state, tyCons) in
    let tyCons = strJoin "\n"
      [ "(declare-datatypes ()"
      , "  ((ConstTy ", if null tyCons then "cx" else strJoin " " tyCons, ")))"
      ] in

    match mapAccumL getRepr state (setToSeq state.reprs) with (state, reprs) in
    let reprs = strJoin "\n"
      [ "(declare-datatypes ()"
      , "  ((RepTy ", if null reprs then "rx" else strJoin " " reprs, ")))"
      ] in

    match mapAccumL getLabel state (setToSeq state.labels) with (state, labels) in
    let labels = strJoin "\n"
      [ "(declare-datatypes ()"
      , "  ((Label ", if null labels then "lx" else strJoin " " labels, ")))"
      ] in

    match mapAccumL getMetaVar state (setToSeq state.vars.metas) with (state, metaVars) in
    let mkMetaVarDecl = lam var. join ["(declare-const ", var, " Ty)"] in
    let metaVars = strJoin "\n" (map mkMetaVarDecl metaVars) in

    match mapAccumL getReprVar state (setToSeq state.vars.reprs) with (state, reprVars) in
    let mkReprVarDecl = lam var. join ["(declare-const ", var, " RepTy)"] in
    let reprVars = strJoin "\n" (map mkReprVarDecl reprVars) in

    let boolExpr = pprintZ3Ast "" query.boolExpr in
    let assertion = join ["(assert ", boolExpr, ")"] in

    let costExpr = pprintZ3Ast "" query.costExpr in
    let objective = join ["(minimize ", costExpr, ")"] in

    let program = strJoin "\n\n"
      [ prelude
      , tyCons, reprs, labels
      , midlude
      , metaVars, reprVars
      , "(declare-const sol Sol)"
      , assertion, objective
      , "(check-sat)"
      , "(eval (pp-sol sol))"
      ] in

    -- printLn "# Input model:";
    -- printLn program;
    let res = sysRunCommand ["z3", "-smt2", "-in"] program "." in
    -- printLn "# Output:";
    -- printLn res.stdout;
    -- printLn "# Error:";
    -- printLn res.stderr;
    -- printLn (join ["# Exit code: ", int2string res.returncode]);
    optionMap mk (parseZ3Output res.stdout)
end

lang ComposableSolver = TreeSolverBase + Z3Stuff
  syn StepStatus a =
  | StepDone (TSSingle a)
  | StepStep (TSTree a)
  | StepFail ()
  type Step a = TSTree a -> StepStatus a

  type CSSteps =
    { getDone : all a. StepStatus a -> Option (TSSingle a)

    , debug : all a. String -> Step a
    , warn : all a. [Info] -> String -> Step a

    , seq : all a. Step a -> Step a -> Step a
    , chain : all a. [Step a] -> Step a
    , bestDoneOf : all a. [Step a] -> Step a
    , sizeBranches : all a. [(Int, Step a)] -> Step a -> Step a
    , sizeBranch : all a. {threshold : Int, small : Step a, big : Step a} -> Step a
    , fix : all a. Step a -> Step a

    , checkDone : all a. Step a
    , perIndep : all a. (all x. Step x) -> Step a
    , perIndepPar : all a. Int -> (all x. Step x) -> Step a
    , pickBestOr : all a. Step a
    , try : all a. Step a -> Step a -> Step a

    , collapseLeaves : all a. Step a
    , partitionIndep : all a. Step a
    , flattenAnds : all a. Step a
    , onTopHomogeneousAlts : all a. Step a -> Step a
    , fail : all a. Bool -> Step a
    , propagate : all a. Step a

    , oneHomogeneous : all a. Step a
    , consistent : all a. Step a
    , lazy : all a. Step a
    , enumBest : all a. Option Int -> Step a
    , z3 : all a. Step a

    , filterApprox : all a. RTS -> Step a
    }

  sem mkCSSteps : Bool -> CSSteps
  sem mkCSSteps = | debug ->
    let cmpf = lam a. lam b. if ltf a b then negi 1 else if gtf a b then 1 else 0 in
    let propagateInterface = {mkPropagateInterface () with recordFailures = debug} in
    let debugInterface = mkDebugInterface () in
    let collapseLeavesInterface = mkCollapseLeavesInterface () in
    let partitionInternalInterface = mkPartitionInternalInterface () in
    let flattenInterface = mkFlattenInterface () in
    let filterApproxInterface = mkFilterApproxInterface () in
    let materializeHomogeneousInterface = mkMaterializeHomogeneousInterface () in
    let materializeConsistentInterface = mkMaterializeConsistentInterface () in
    let materializeLazyInterface = mkMaterializeLazyInterface () in
    let materializeStatelessInterface = mkMaterializeStatelessInterface () in
    let seq : all a. Step a -> Step a -> Step a = lam l. lam r.
      let f : Step a = lam tree.
        switch l tree
        case res & (StepDone _ | StepFail _) then res
        case StepStep tree then r tree
        end in
      f in
    { getDone =
      let getDone : all a. StepStatus a -> Option (TSSingle a) = lam x.
        match x with StepDone x then Some x else None () in
      #frozen"getDone"
    , fix =
      let fix : all a. Step a -> Step a = lam step.
        recursive let f : Step a = lam tree.
          let res = step tree in
          match res with StepStep tree then f tree else res in
        f in
      #frozen"fix"
    , seq = #frozen"seq"
    , chain =
      let chain : all a. [Step a] -> Step a = lam fs.
        match fs with fs ++ [last]
        then foldr seq last fs
        else error "Compiler error: empty list in chain" in
      #frozen"chain"
    , bestDoneOf =
      let bestDoneOf : all a. [Step a] -> Step a = lam fs. lam tree.
        let inner = lam f. match f tree with StepDone sing
          then Some sing
          else None () in
        match minIdx (lam a. lam b. cmpf a.cost b.cost) (mapOption inner fs)
        with Some (_, sing) then StepDone sing
        else StepFail () in
      #frozen"bestDoneOf"
    , sizeBranches =
      let sizeBranches : all a. [(Int, Step a)] -> Step a -> Step a = lam smaller. lam default.
        let smaller = sort (lam a. lam b. subi a.0 b.0) smaller in
        match smaller with _ ++ [(upper, _)] then
          let f = lam tree.
            let size = rtBoundedSize upper tree in
            let pair = optionBind size (lam size. find (lam pair. lti size pair.0) smaller) in
            optionMapOrElse (lam. default tree) (lam pair. pair.1 tree) pair
          in f
        else default in
      #frozen"sizeBranches"
    , sizeBranch =
      let sizeBranch : all a. {threshold : Int, small : Step a, big : Step a} -> Step a = lam opts. lam tree.
        if optionIsSome (rtBoundedSize opts.threshold tree)
        then opts.small tree
        else opts.big tree in
      #frozen"sizeBranch"
    , pickBestOr =
      let pickBestOr : all a. Step a = lam tree. match tree with RTOr (x & {others = []})
        then match min (lam a. lam b. cmpf a.cost b.cost) x.singles with Some sing
          then StepDone sing
          else StepFail ()
        else StepStep tree in
      #frozen"pickBestOr"
    , checkDone =
      let checkDone : all a. Step a = lam tree. match tree with RTSingle sing
        then StepDone sing
        else StepStep tree in
      #frozen"checkDone"
    , perIndep =
      let perIndep : all a. (all x. Step x) -> Step a = lam f. lam tree.
        match tree with RTAnd (x & {dep = InDep _}) then
          let runInner = lam child. switch f child.val
            case StepDone sing then Some {child with val = RTSingle sing}
            case StepStep tree then Some {child with val = tree}
            case StepFail _ then None ()
            end in
          match optionMapM runInner x.children with Some children
          then StepStep (RTAnd {x with children = children})
          else StepFail ()
        else f tree in
      #frozen"perIndep"
    , perIndepPar =
      let perIndep : all a. Int -> (all x. Step x) -> Step a = lam count. lam f. lam tree.
        match tree with RTAnd (x & {dep = InDep _}) then
          let pool = threadPoolCreate count in
          let runInner = lam child. switch f child.val
            case StepDone sing then Some {child with val = RTSingle sing}
            case StepStep tree then Some {child with val = tree}
            case StepFail _ then None ()
            end in
          let resses = pmap pool count runInner x.children in
          threadPoolTearDown pool;
          match optionMapM (lam x. x) resses with Some children
          then StepStep (RTAnd {x with children = children})
          else StepFail ()
        else f tree in
      #frozen"perIndep"
    , propagate =
      let propagate : all a. Step a = lam tree.
        match rtPropagate propagateInterface tree with (failures, res) in
        match res with Some tree
        then StepStep tree
        else
          (if debug then
            printLn (json2string (JsonString "AUTO: propagate failure"));
            let failures = mapAccumL (rtfToJson debugInterface) pprintEnvEmpty failures in
            printLn (json2string (JsonArray failures.1))
           else ());
          StepFail () in
      #frozen"propagate"
    , debug =
      let debug : all a. String -> Step a = lam label. lam tree.
        (if debug then
          printLn (json2string (JsonString label));
          printLn (json2string (rtDebugJson debugInterface pprintEnvEmpty tree).1)
         else ());
        StepStep tree in
      #frozen"debug"
    , collapseLeaves =
      let collapseLeaves : all a. Step a = lam tree.
        StepStep (rtCollapseLeaves collapseLeavesInterface tree) in
      #frozen"collapseLeaves"
    , partitionIndep =
      let partitionIndep : all a. Step a = lam tree.
        StepStep (rtPartitionIndependent partitionInternalInterface tree) in
      #frozen"partitionIndep"
    , flattenAnds =
      let flattenAnds : all a. Step a = lam tree.
        StepStep (rtFlatten flattenInterface tree) in
      #frozen"flattenAnds"
    , oneHomogeneous =
      let oneHomogeneous : all a. Step a = lam tree.
        match rtMaterializeHomogeneous materializeHomogeneousInterface tree
        with Some sing then StepDone sing
        else StepFail () in
      #frozen"oneHomogeneous"
    , onTopHomogeneousAlts =
      let onTopHomogeneousAlts : all a. Step a -> Step a = lam step. lam tree.
        let res = rtHomogenizeTop nameCmp tree in
        let res = mapOption (lam x. match step x with StepDone sing then Some sing else None ()) res in
        match min (lam a. lam b. cmpf a.cost b.cost) res
        with Some sing then StepDone sing
        else StepFail () in
      #frozen"onTopHomogeneousAlts"
    , consistent =
      let consistent : all a. Step a = lam tree.
        match rtMaterializeConsistent materializeConsistentInterface tree
        with Some sing then StepDone sing
        else StepFail () in
      #frozen"consistent"
    , fail =
      let fail : all a. Bool -> Step a = lam complete. lam.
        if complete
        then errorSingle [] "Could not find a consistent assignment of impls across the program"
        else errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)" in
      #frozen"fail"
    , filterApprox =
      let f : all a. RTS -> Step a = lam rts. lam tree.
        StepStep (rtsFilterApprox filterApproxInterface rts tree) in
      #frozen"f"
    , try =
      let f : all a. Step a -> Step a -> Step a = lam a. lam b. lam tree.
        let res = a tree in
        match res with StepFail _ then b tree else res in
      #frozen"f"
    , warn =
      let f : all a. [Info] -> String -> Step a = lam infos. lam msg. lam tree.
        warnSingle infos msg;
        StepStep tree in
      #frozen"f"
    , lazy =
      let f : all a. Step a = lam tree.
        match lazyStreamUncons (rtMaterializeLazyRecursive materializeLazyInterface tree)
        with Some (sing, _) then StepDone sing
        else StepFail () in
      #frozen"f"
    , z3 =
      let f : all a. Step a = lam tree.
        match solveWithZ3 tree with Some sing
        then StepDone sing
        else StepFail () in
      #frozen"f"
    , enumBest =
      let f : all a. Option Int -> Step a = lam limit. lam tree.
        let it = rtMaterializeStateless materializeStatelessInterface tree in
        let it = optionMapOr it (lam limit. iterTake limit it) limit in
        match iterMin (lam a. lam b. cmpf a.cost b.cost) it
        with Some sing then StepDone sing
        else StepFail () in
      #frozen"f"
    }
end

lang TreeSolverPartIndep = ComposableSolver
  sem solveWork debug prev = | top ->
    let s = mkCSSteps debug in
    let bottomUp = lam x. s.fix (s.chain
      [ s.collapseLeaves
      , s.propagate
      , s.debug "bu-step"
      , s.checkDone
      , s.pickBestOr
      ]) x in
    -- let largeSolver = lam tree. s.try
    --   (s.bestDoneOf
    --     [ s.consistent
    --     , s.onTopHomogeneousAlts (s.seq s.propagate (s.sizeBranches
    --       [ (100000, bottomUp)
    --       ]
    --       (s.seq (s.debug "homogeneous top") s.oneHomogeneous)))
    --     ])
    --   (s.enumBest (Some 1))
    --   tree in
    let largeSolver = lam tree. s.try
      ( s.onTopHomogeneousAlts (s.seq s.propagate (s.sizeBranches
        [ (100000, bottomUp)
        ]
        (s.seq (s.debug "homogeneous top") s.oneHomogeneous)))
      )
      (s.enumBest (Some 1))
      tree in
    let inner = lam tree. s.chain
      [ s.debug "pre-homogeneous"
      , s.sizeBranches [(100000, bottomUp)] largeSolver
      , s.debug "post-homogeneous"
      , s.propagate
      , s.debug "post-inner-propagate"
      ] tree in
    let fastSolve = s.chain
      [ s.debug "start"
      , s.propagate
      , s.debug "post-propagate"
      , s.flattenAnds
      , s.debug "post-flatten"
      , s.partitionIndep
      , s.debug "post-partition-indep"
      , s.perIndep #frozen"inner"
      , s.debug "post-per-indep"
      , s.propagate
      , s.debug "post-final-propagate"
      , s.checkDone
      , s.fail false
      ] in
    let solve = match prev with Some prev
      then s.try
        (s.seq (s.filterApprox prev) fastSolve)
        (s.seq (s.warn [] "Could not reuse previous solution, falling back to a re-solve.") fastSolve)
      else fastSolve in
    match s.getDone (solve top) with Some s then s.value else
    errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)"
end

lang TreeSolverEnum = ComposableSolver
  sem solveWork debug prev = | top ->
    let s = mkCSSteps debug in
    let materializeStatelessInterface = mkMaterializeStatelessInterface () in
    let bottomUp = lam x. s.fix (s.chain
      [ s.collapseLeaves
      , s.propagate
      , s.debug "bu-step"
      , s.checkDone
      , s.pickBestOr
      ]) x in
    let customIndep : all a. Step a = lam tree.
      match tree with RTAnd (x & {dep = InDep _}) then
        let startTime = wallTimeMs () in
        let mkThing = lam child.
          match iterUncons (rtMaterializeStateless materializeStatelessInterface child) with Some (sing, next) then
            let r = ref sing in
            let step = lam new.
              if ltf new.cost (deref r).cost
              then modref r new
              else () in
            Some (r, iterMap step next)
          else None () in
        let runInner : Unknown -> Option (Ref (TSSingle Unknown), Iter ())= lam child.
          if optionIsSome (rtBoundedSize 100000 child.val)
          then match bottomUp child.val with StepDone sing
            then Some (ref sing, iterEmpty)
            else None ()
          else mkThing child.val in
        match optionMap unzip (optionMapM runInner x.children) with Some (best, steppers) then
          let stepOne = lam stepper.
            if gtf (subf (wallTimeMs ()) startTime) 60000.0 then None () else
            match iterUncons stepper with Some (_, stepper)
            then Some stepper
            else None () in
          recursive let work = lam steppers.
            match steppers with [] then () else
            work (mapOption stepOne steppers) in
          work steppers;
          let reconstruct = lam new. lam old. {scale = old.scale, val = RTSingle (deref new)} in
          StepStep (RTAnd {x with children = zipWith reconstruct best x.children})
        else StepFail ()
      else StepStep tree in
    let fastSolve = s.chain
      [ s.debug "start"
      , s.propagate
      , s.debug "post-propagate"
      , s.flattenAnds
      , s.partitionIndep
      , s.debug "post-partition-indep"
      , customIndep
      , s.debug "post-per-indep"
      , s.propagate
      , s.debug "post-final-propagate"
      , s.checkDone
      , s.fail false
      ] in
    let solve = match prev with Some prev
      then s.try
        (s.seq (s.filterApprox prev) fastSolve)
        (s.seq (s.warn [] "Could not reuse previous solution, falling back to a re-solve.") fastSolve)
      else fastSolve in
    match s.getDone (solve top) with Some s then s.value else
    errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)"
end

lang TreeSolverFast = ComposableSolver
  sem solveWork debug prev = | top ->
    let s = mkCSSteps debug in
    let materializeStatelessInterface = mkMaterializeStatelessInterface () in
    let bottomUp = lam x. s.fix (s.chain
      [ s.collapseLeaves
      , s.propagate
      , s.debug "bu-step"
      , s.checkDone
      , s.pickBestOr
      ]) x in
    let customIndep : all a. Step a = lam tree.
      match tree with RTAnd (x & {dep = InDep _}) then
        let startTime = wallTimeMs () in
        let mkThing = lam child.
          match iterUncons (rtMaterializeStateless materializeStatelessInterface child) with Some (sing, next) then
            let r = ref sing in
            let step = lam new.
              if ltf new.cost (deref r).cost
              then modref r new
              else () in
            Some (r, iterMap step next)
          else None () in
        let runInner = lam child.
          if optionIsSome (rtBoundedSize 100000 child.val)
          then s.getDone (bottomUp child.val)
          else match iterUncons (rtMaterializeStateless materializeStatelessInterface child.val)
            with Some (sing, _) then Some sing
            else None () in
        match optionMapM runInner x.children with Some sings then
          let reconstruct = lam new. lam old. {scale = old.scale, val = RTSingle new} in
          StepStep (RTAnd {x with children = zipWith reconstruct sings x.children})
        else StepFail ()
      else StepStep tree in
    let fastSolve = s.chain
      [ s.debug "start"
      , s.propagate
      , s.debug "post-propagate"
      , s.flattenAnds
      , s.partitionIndep
      , s.debug "post-partition-indep"
      , customIndep
      , s.debug "post-per-indep"
      , s.propagate
      , s.debug "post-final-propagate"
      , s.checkDone
      , s.fail false
      ] in
    let solve = match prev with Some prev
      then s.try
        (s.seq (s.filterApprox prev) fastSolve)
        (s.seq (s.warn [] "Could not reuse previous solution, falling back to a re-solve.") fastSolve)
      else fastSolve in
    match s.getDone (solve top) with Some s then s.value else
    errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)"
end

lang TreeSolverZ3 = ComposableSolver
  sem solveWork debug prev = | top ->
    let s = mkCSSteps debug in
    let inner = lam tree. s.seq (s.debug "pre indep-branch") s.z3 tree in
    let solve = s.chain
      [ s.debug "start"
      , s.propagate
      , s.debug "post-propagate"
      , s.flattenAnds
      , s.partitionIndep
      , s.debug "post-partition-indep"
      , s.perIndepPar 8 #frozen"inner"
      , s.debug "post-per-indep"
      , s.propagate
      , s.debug "post-final-propagate"
      , s.checkDone
      , s.fail true
      ] in
    let solve = match prev with Some prev
      then s.try
        (s.seq (s.filterApprox prev) solve)
        (s.seq (s.warn [] "Could not reuse previous solution, falling back to a re-solve.") solve)
      else solve in
    match s.getDone (solve top) with Some s then s.value else
    errorSingle [] "Could not find a consistent assignment of impls across the program"
end

lang TreeSolverBottomUp = ComposableSolver
  sem solveWork debug prev = | top ->
    let s = mkCSSteps debug in
    let bottomUp = lam x. s.fix (s.chain
      [ s.collapseLeaves
      , s.propagate
      , s.debug "bu-step"
      , s.checkDone
      , s.pickBestOr
      ]) x in
    let solve = s.chain
      [ s.debug "start"
      , s.propagate
      , s.debug "post-propagate"
      , s.flattenAnds
      , s.partitionIndep
      , s.debug "post-partition-indep"
      , s.perIndep #frozen"bottomUp"
      , s.debug "post-per-indep"
      , s.propagate
      , s.debug "post-final-propagate"
      , s.checkDone
      , s.fail true
      ] in
    let solve = match prev with Some prev
      then s.try
        (s.seq (s.filterApprox prev) solve)
        (s.seq (s.warn [] "Could not reuse previous solution, falling back to a re-solve.") solve)
      else solve in
    match s.getDone (solve top) with Some s then s.value else
    errorSingle [] "Could not find a consistent assignment of impls across the program"

  sem solveWorkAll debug = | top ->
    let propagateInterface =
      { mkPropagateInterface ()
        with pruneRedundant = None ()
      } in
    let debugInterface = mkDebugInterface () in
    let collapseLeavesInterface = mkCollapseLeavesInterface () in
    let partitionInternalInterface = mkPartitionInternalInterface () in
    recursive
      let start = lam top.
        (if debug then
          printLn (json2string (rtDebugJson debugInterface pprintEnvEmpty top).1)
         else ());
        match rtPropagate propagateInterface top with (_, Some top) then
          (if debug then
            printLn (json2string (rtDebugJson debugInterface pprintEnvEmpty top).1)
           else ());
          -- checkDone (rtPartitionInternalComponents partitionInternalInterface top)
          checkDone top
        else None ()
      let propagate = lam top.
        match rtPropagate propagateInterface top with (_, Some top) then
          checkDone top
        else None ()
      let checkDone = lam top.
        (if debug then
          printLn (json2string (rtDebugJson debugInterface pprintEnvEmpty top).1)
         else ());
        switch top
        case RTSingle x then
          Some [x.value]
        case RTOr {singles = ss, others = []} then
          Some (map (lam s. s.value) ss)
        case _ then
          collapseLeaves top
        end
      let collapseLeaves = lam top.
        propagate (rtCollapseLeaves collapseLeavesInterface top)
    in match start top with Some res then res else
      errorSingle [] "Could not find a consistent assignment of impls across the program"
end

lang TreeSolverGreedy = ComposableSolver
  sem solveWork debug prev = | top ->
    let s = mkCSSteps debug in
    let inner = s.lazy in
    let solve = s.chain
      [ s.debug "start"
      , s.propagate
      , s.debug "post-propagate"
      , s.flattenAnds
      , s.partitionIndep
      , s.debug "post-partition-indep"
      , s.perIndep #frozen"inner"
      , s.debug "post-per-indep"
      , s.propagate
      , s.debug "post-final-propagate"
      , s.checkDone
      , s.fail false
      ] in
    let solve = match prev with Some prev
      then s.try
        (s.seq (s.filterApprox prev) solve)
        (s.seq (s.warn [] "Could not reuse previous solution, falling back to a re-solve.") solve)
      else solve in
    match s.getDone (solve top) with Some s then s.value else
    errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)"
end

lang TreeSolverFilterByBest = TreeSolverBase
  sem solveWork debug prev = | top ->
    let propagateInterface = mkPropagateInterface () in
    let debugInterface = mkDebugInterface () in
    let collapseLeavesInterface = mkCollapseLeavesInterface () in

    type StepStatus in
    con StepDone : a -> StepStatus in
    con StepStep : TSTree a -> StepStatus in
    con StepFail : () -> StepStatus in
    type Step = TSTree a -> StepStatus in

    let fix : Step -> Step = lam step.
      recursive let f : Step = lam tree.
        let res = step tree in
        match res with StepStep tree then f tree else res in
      f in
    let seq : Step -> Step -> Step = lam l. lam r.
      let f : Step = lam tree. switch l tree
        case res & (StepDone _ | StepFail _) then res
        case StepStep tree then r tree
        end in
      f in
    let chain : [Step] -> Step = lam fs.
      match fs with fs ++ [last]
      then foldr seq last fs
      else error "Compiler error: empty list in chain" in

    let checkDone : Step = lam tree. match tree with RTSingle sing
      then StepDone sing.value
      else StepStep tree in
    let propagate : Step = lam tree.
      match rtPropagate propagateInterface tree with (_, Some tree)
      then StepStep tree
      else StepFail () in
    let debug : Step = lam tree.
      (if debug then
        printLn (json2string (rtDebugJson debugInterface pprintEnvEmpty tree).1)
       else ());
      StepStep tree in
    let collapseLeaves : Step = lam tree.
      StepStep (rtCollapseLeaves collapseLeavesInterface tree) in
    let filterBestReprs : Step = lam tree.
      StepStep (rtFilterReprs tree) in

    let solve = fix (chain [propagate, debug, checkDone, filterBestReprs, debug, collapseLeaves]) in
    switch solve top
    case StepDone x then x
    case StepFail () then errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)"
    case StepStep _ then error "Compiler error: got a StepStep out of `repeat`."
    end
end

lang TreeSolverHomogeneous = TreeSolverBase
  sem solveWork debug prev = | top ->
    let propagateInterface = mkPropagateInterface () in
    let partitionInternalInterface = mkPartitionInternalInterface () in
    let materializeConsistentInterface = mkMaterializeConsistentInterface () in
    let materializeHomogeneousInterface = mkMaterializeHomogeneousInterface () in
    match rtPropagate propagateInterface top with (_, Some top) then
      let top = rtPartitionInternalComponents partitionInternalInterface top in
      match rtPropagate propagateInterface top with (_, Some top) then
        match rtMaterializeHomogeneous materializeHomogeneousInterface top with Some res then
          res.value
        else errorSingle [] "Could not find a consistent assignment of impls across the program (though it may have been missed)"
      else errorSingle [] "Could not find a consistent assignment of impls across the program"
    else errorSingle [] "Could not find a consistent assignment of impls across the program"
end

lang TreeSolverMixed = TreeSolverBase
  sem solveWork debug prev = | top ->
    let propagateInterface = mkPropagateInterface () in
    let partitionInternalInterface = mkPartitionInternalInterface () in
    let materializeConsistentInterface = mkMaterializeConsistentInterface () in
    let materializeHomogeneousInterface = mkMaterializeHomogeneousInterface () in
    let debugInterface = mkDebugInterface () in
    let cmpf = lam a. lam b. if ltf a b then negi 1 else if gtf a b then 1 else 0 in
    type Tree = RepTree Relevant Constraint Var Val NodeIdent a in
    type Res = RTSingleRec a Constraint Var Val Relevant NodeIdent in

    (if debug then
      match rtDebugJson debugInterface pprintEnvEmpty top with (env, debug) in
      printLn (json2string debug)
     else ());

    match rtPropagate propagateInterface top with (_, Some top) then
      let top = rtPartitionInternalComponents partitionInternalInterface top in
      match rtPropagate propagateInterface top with (_, Some top) then
        let terminatingSolvers : [Tree -> Option Res] =
          [ rtMaterializeHomogeneous materializeHomogeneousInterface
          , rtMaterializeConsistent materializeConsistentInterface
          ] in
        let steppingSolvers : [Tree -> [Tree]] =
          [ lam top : Tree.
            let res = rtHomogenizeTop nameCmp top in
            let res = mapOption (lam x. (rtPropagate propagateInterface x).1) res in
            res
          ] in
        let sols = mapOption (lam f. f top) terminatingSolvers in
        let steppedTrees = join (map (lam f. f top) steppingSolvers) in
        let moreSols = filterOption (seqLiftA2 (lam f. lam tree. f tree) terminatingSolvers steppedTrees) in
        let sol = min (lam a. lam b. cmpf a.cost b.cost) (concat sols moreSols) in
        match sol with Some sol then sol.value else
        errorSingle [] "Could not find a consistent assignment of impls across the program, but it might have been missed"
      else errorSingle [] "Could not find a consistent assignment of impls across the program"
    else errorSingle [] "Could not find a consistent assignment of impls across the program"
end

lang TreeSolverExplore = TreeSolverBase
  sem solveWork debug prev = | top ->
    let propagateInterface = mkPropagateInterface () in
    let partitionInternalInterface = mkPartitionInternalInterface () in
    let eqInterface = mkEqInterface () in
    let collapseLeavesInterface = mkCollapseLeavesInterface () in
    let debugInterface = mkDebugInterface () in

    let propagate = lam x. (rtPropagate propagateInterface x).1 in
    let partitionInternal = rtPartitionInternalComponents partitionInternalInterface in
    let eq = rtEq eqInterface in
    let collapse = rtCollapseLeaves collapseLeavesInterface in
    let debug = lam top. printLn (json2string (rtDebugJson debugInterface pprintEnvEmpty top).1) in

    debug top;

    recursive let checkSubsetOfAbove = lam above. lam tree. switch tree
      case RTSingle x then
        match above with Some above then
          varMapSubset x.relevantAbove above
        else true
      case RTAnd x then
        let isSubset = match above with Some above
          then varMapSubset x.relevantAbove above
          else true in
        if isSubset then
          let badChildren = mapOption
            (lam c. if checkSubsetOfAbove (Some x.relevantHere) c.val then None () else Some c.val)
            x.children in
          for_ badChildren (lam child.
            debug tree;
            debug child);
          true
        else false
      case RTOr x then
        let isSubset = match above with Some above
          then varMapSubset x.relevantAbove above
          else true in
        if isSubset then
          let badChildren = mapOption
            (lam c. if checkSubsetOfAbove (Some x.relevantHere) c then None () else Some c)
            (concat (map (lam x. RTSingle x) x.singles) x.others) in
          for_ badChildren (lam child.
            debug tree;
            debug child;
            error "There are bad children");
          true
        else false
      end in

    let dumpIfFail = lam propLabel. lam stateLabel. lam cond. lam pairs.
      (if not cond then
        printLn (join ["\"FAIL ", propLabel, " ", stateLabel, "\""]);
        let f = lam pair.
          printLn (join ["\"", pair.0, "\""]);
          optionMapOr () debug pair.1 in
        for_ pairs f
       else ());
       cond in
    let propagateIdempotent = lam label. lam tree.
      let one = propagate tree in
      let two = optionBind one propagate in
      dumpIfFail "propagateIdempotent" label
        (optionEq eq one two)
        [("tree", Some tree), ("one", one), ("two", two)] in
    let partitionInternalIdempotent = lam label. lam tree.
      let one = partitionInternal tree in
      let two = partitionInternal one in
      dumpIfFail "partitionInternalIdempotent" label
        (eq one two)
        [("tree", Some tree), ("one", Some one), ("two", Some two)] in
    let partitionMaintainsStateSpace = lam label. lam tree.
      let next = partitionInternal tree in
      dumpIfFail "partitionMaintainsStateSpace" label
        (eqi (rtStateSpace tree) (rtStateSpace next))
        [("tree", Some tree), ("one", Some tree), ("two", Some next)] in
    let collapseNoPropagateSameStateSpace = lam label. lam tree.
      let next = collapse tree in
      dumpIfFail "collapseNoPropagateSameStateSpace" label
        (eqi (rtStateSpace tree) (rtStateSpace next))
        [("tree", Some tree), ("one", Some tree), ("two", Some next)] in
    let collapsePropagateSmallerStateSpace = lam label. lam tree.
      let next = propagate (collapse tree) in
      let nextSize = optionMapOr 0 rtStateSpace next in
      dumpIfFail "collapsePropagateSmallerStateSpace" label
        (lti nextSize (rtStateSpace tree))
        [("tree", Some tree), ("tree", Some tree), ("next", next)] in
    let relevantSetsConsistent = lam label. lam tree.
      dumpIfFail "relevantSetsConsistent" label
        (checkSubsetOfAbove (None ()) tree)
        [("tree", Some tree)] in

    -- let propagate = ("propagate", lam top. rtPropagate propagateInterface top) in
    -- let partition = ("partition", lam top. Some (rtPartitionInternalComponents partitionInternalInterface top)) in
    -- let applySeq = lam top. lam fs.
    --   let f = lam top. lam f.
    --     match f.1 top with Some top
    --     then printLn (join ["  post-", f.0, ": ", int2string (rtStateSpace top)]); Some top
    --     else printLn (join ["  post-", f.0, ": 0"]); None () in
    --   printLn (join ["Sequence start: ", int2string (rtStateSpace top)]);
    --   optionFoldlM f top fs in
    -- applySeq top [propagate, propagate, propagate];
    -- applySeq top [propagate, partition, propagate, partition];
    -- applySeq top [partition, partition];
    -- applySeq top [partition, propagate, propagate];

    let properties =
      [ ("propagateIdempotent", propagateIdempotent)
      , ("partitionInternalIdempotent", partitionInternalIdempotent)
      , ("partitionMaintainsStateSpace", partitionMaintainsStateSpace)
      , ("collapseNoPropagateSameStateSpace", collapseNoPropagateSameStateSpace)
      , ("collapsePropagateSmallerStateSpace", collapsePropagateSmallerStateSpace)
      , ("relevantSetsConsistent", relevantSetsConsistent)
      ] in
    let actions =
      [ ("propagate", propagate)
      , ("partitionInternal", lam x. Some (partitionInternal x))
      , ("collapse", lam x. Some (collapse x))
      ] in
    recursive let applyActions = lam inputs. lam actions. lam maxSteps.
      if leqi maxSteps 0 then inputs else
      let f = lam input. lam action. optionMap (lam tree. (join [input.0, "-", action.0], tree)) (action.1 input.1) in
      let next = seqLiftA2 f inputs actions in
      let next = filterOption next in
      concat inputs (applyActions next actions (subi maxSteps 1)) in

    let states = applyActions [("start", top)] actions 3 in
    for_ properties (lam prop. for_ states (lam st. prop.1 st.0 st.1; ()));

    error "TODOexploreEnd"
end

lang SATishSolver = RepTypesShallowSolverInterface + UnifyPure + RepTypesHelpers + PrettyPrint + Cmp + Generalize + VarAccessHelpers + LocallyNamelessStuff + SolTreeSolver + WildToMeta
  type ProcOpImpl a  =
    { implId : ImplId
    , op : Name
    , opUses : [{idxes : Set Int, opUse : TmOpVarRec}]
    , selfCost : OpCost
    , uni : Unification
    , specType : Type
    , reprScope : Int
    , metaLevel : Int
    , info : Info
    -- NOTE(vipa, 2023-07-06): A token used by the surrounding system
    -- to carry data required to reconstruct a solved AST.
    , token : a
    }
  type SolContentRec a =
    { token : a
    , cost : OpCost
    , impl : ProcOpImpl a
    , highestImpl : ImplId
    , subSols : [{idxes : Set Int, scale : OpCost, sol : SolContent a}]
    }
  syn SolContent a = | SolContent (SolContentRec a)
  type Constraint a =
    -- NOTE(vipa, 2023-12-12): 'None' means the full set
    { unfixedReprs : Map Symbol (Option (Set Name))
    -- NOTE(vipa, 2023-12-12): This will be 'None' if it's the union
    -- of multiple alts, i.e., we don't propagate equality constraints
    -- on reprs, or *any* constraints on types until we've fixed a
    -- single solution
    , fixedUni : Option Unification
    }
  type ChildInfo a =
    { name : Name
    , info : Info
    }
  type QueryItem a =
    { scale : OpCost
    , child: SolTreeInput (Constraint a) (ChildInfo a) (SolContent a)
    }

  type SBContent a =
    { implsPerOp : Map Name (Set (ProcOpImpl a))
    , memo : Map (Name, Type) {reprLevels : Map Symbol Int, tree : SolTreeInput (Constraint a) (ChildInfo a) (SolContent a)}
    , nameless : NamelessState
    }

  syn SolverGlobal a = | SGContent ()
  syn SolverBranch a = | SBContent (SBContent a)
  syn SolverSolution a = | SSContent (SolContent a)

  syn SolverTopQuery a = | STQContent [QueryItem a]

  sem initSolverGlobal = | _ -> SGContent ()
  sem initSolverBranch = | _ -> SBContent
    { implsPerOp = mapEmpty nameCmp
    , memo = mapEmpty cmpOpPair
    , nameless =
      { metas = []
      , vars = []
      , reprs = []
      }
    }
  sem initSolverTopQuery = | _ -> STQContent []

  -- NOTE(vipa, 2023-11-07): This typically assumes that the types
  -- have a representation that is equal if the two types are
  -- alpha-equivalent.
  sem cmpOpPair : (Name, Type) -> (Name, Type) -> Int
  sem cmpOpPair l = | r ->
    let res = nameCmp l.0 r.0 in
    if neqi 0 res then res else
    let res = cmpType l.1 r.1 in
    res

  sem cmpSolution a = | b ->
    recursive let work : all x. all y. {idxes : x, scale : y, sol : Unknown} -> {idxes : x, scale : y, sol : Unknown} -> Int = lam a. lam b.
      match (a, b) with ({sol = SolContent a}, {sol = SolContent b}) in
      let res = subi a.impl.implId b.impl.implId in
      if neqi 0 res then res else
      let res = seqCmp work a.subSols b.subSols in
      res in
    match (a, b) with (SSContent a, SSContent b) in
    work {idxes = (), scale = (), sol = a} {idxes = (), scale = (), sol = b}

  sem concretizeSolution global =
  | SSContent (SolContent x) ->
    let subSols = foldl
      (lam acc. lam sub. setFold (lam acc. lam idx. mapInsert idx (SSContent sub.sol) acc) acc sub.idxes)
      (mapEmpty subi)
      x.subSols in
    (x.token, x.highestImpl, mapValues subSols)

  sem addImpl global branch = | impl ->
    match branch with SBContent branch in

    let idxedOpUses = mapi (lam i. lam opUse. {idxes = setInsert i (setEmpty subi), opUse = opUse}) impl.opUses in
    let procImpl =
      { implId = impl.implId
      , op = impl.op
      , opUses = idxedOpUses
      , selfCost = impl.selfCost
      , uni = impl.uni
      , specType = impl.specType
      , reprScope = impl.reprScope
      , metaLevel = impl.metaLevel
      , info = impl.info
      , token = impl.token
      } in

    let branch =
      { branch with
        implsPerOp = mapInsertWith setUnion
          impl.op
          (setInsert procImpl (setEmpty (lam a. lam b. subi a.implId b.implId)))
          branch.implsPerOp
      -- OPT(vipa, 2023-11-07): Better memoization cache invalidation,
      -- or incremental computation that never needs to invalidate
      , memo = mapEmpty cmpOpPair
      } in
    SBContent branch

  sem debugBranchState global = | SBContent branch ->
    printLn "debugBranchState"

  sem debugSolution global = | solutions ->
    printLn "\n# Solution cost tree:";
    recursive let work = lam indent. lam solWithMeta.
      match solWithMeta.sol with SolContent x in
      -- TODO(vipa, 2023-11-28): This will print things in a strange
      -- order, and de-duped, which might not be desirable
      join
        [ indent, nameGetStr x.impl.op, " (cost: ", float2string x.cost
        , ", scaling: ", float2string solWithMeta.scale, ", info: ", info2str x.impl.info
        , ")\n"
        , join (map (lam x. work (concat indent "  ") x) x.subSols)
        ]
    in
    let solutions = map
      (lam x. match x with SSContent x in work "" {idxes = setEmpty subi, scale = 1.0, sol = x})
      solutions in
    join
      [ "\n# Solution cost tree:\n"
      , join solutions
      ]

  sem topSolve debug file global = | STQContent topTrees ->
    let constraintOr = lam a. lam b.
      { unfixedReprs = mapUnionWith (optionZipWith setUnion) a.unfixedReprs b.unfixedReprs
      , fixedUni = None ()
      } in
    let constraintEq = lam a. lam b.
      if mapEq (optionEq setEq) a.unfixedReprs b.unfixedReprs
      then optionEq (lam a. lam b. if uniImplies a b then uniImplies b a else false) a.fixedUni b.fixedUni
      else false in
    let constrain = lam input.
      -- NOTE(vipa, 2023-12-12): Try to extract information about
      -- what has changed when it changes, to avoid extraneous
      -- checks afterwards. Currently easiest to do with (local)
      -- side-effects.
      let parentChanged = ref false in
      let childChanged = ref false in
      let foundEmptyRepr = ref false in
      let intersect = lam parent. lam child. switch (parent, child)
        case (Some parent, Some child) then
          let res = setIntersect parent child in
          if setIsEmpty res then
            modref foundEmptyRepr true;
            None ()
          else
            (if lti (setSize res) (setSize parent) then
              modref parentChanged true
             else ());
            (if lti (setSize res) (setSize child) then
              modref childChanged true
             else ());
            Some res
        case (None _, Some x) then
          modref parentChanged true;
          Some x
        case (Some x, None _) then
          modref childChanged true;
          Some x
        case (None _, None _) then
          None ()
        end in
      let unfixedReprs = mapUnionWith intersect input.parent.unfixedReprs input.child.unfixedReprs in
      if deref foundEmptyRepr then None () else -- NOTE(vipa, 2023-12-12): Early exit

      -- NOTE(vipa, 2023-12-12): The code above detects changes in
      -- shared reprs, but changes can also come from unshared
      -- reprs, these we detect here
      (if deref parentChanged then () else
        modref parentChanged (neqi (mapSize input.parent.unfixedReprs) (mapSize unfixedReprs))
      );
      (if deref childChanged then () else
        modref childChanged (neqi (mapSize input.child.unfixedReprs) (mapSize unfixedReprs))
      );

      match
        match (input.parent.fixedUni, input.child.fixedUni) with (Some par, Some chi) then
          let newUni = mergeUnifications par chi in
          let parentChanged =
            if deref parentChanged then true else
            -- NOTE(vipa, 2023-12-12): We know (by construction) that
            -- newUni implies par (because `mergeUnifications` is a
            -- logical 'and') so we don't need to check that here
            not (optionMapOr true (uniImplies par) newUni) in
          let childChanged =
            if deref childChanged then true else
            -- NOTE(vipa, 2023-12-12): We know (by construction) that
            -- newUni implies chi (because `mergeUnifications` is a
            -- logical 'and') so we don't need to check that here
            not (optionMapOr true (uniImplies chi) newUni) in
          (optionIsSome newUni, newUni, parentChanged, childChanged)
        else
          (true, optionOr input.parent.fixedUni input.child.fixedUni, deref parentChanged, deref childChanged)
      with (success, fixedUni, parentChanged, childChanged) in

      if success then Some
        { parentChanged = parentChanged
        , childChanged = childChanged
        , res = { unfixedReprs = unfixedReprs, fixedUni = fixedUni }
        }
      else None () in
    let split
      : all x. Constraint a
      -> [{spaceSize : Int, maxCost : OpCost, minCost : OpCost, token : x}]
      -> Option ([[x]], [Constraint a])
      = lam constraint. lam components.
        let eitherCmp = lam l. lam r. lam a. lam b.
          let res = subi (constructorTag a) (constructorTag b) in
          if neqi 0 res then res else
          switch (a, b)
          case (Left a, Left b) then l a b
          case (Right a, Right b) then r a b
          end in
        let puf : PureUnionFind (Either Symbol Name) (Set Int) = pufEmpty (eitherCmp _symCmp nameCmp) in
        let setChoices = lam sym. lam choices.
          match choices with Some alts then
            if gti (setSize alts) 1 then Some (sym, alts) else None ()
          else None () in
        let f = lam acc. lam reprsym. lam alts.
          optionOrElse (lam. setChoices reprsym alts) acc in
        match mapFoldWithKey f (None ()) constraint.unfixedReprs with Some (reprsym, alts) then
          let mkConstraint = lam alt.
            -- TODO(vipa, 2023-12-15): Currently ignoring fixedUni,
            -- with the hope that the constraint propagates properly
            -- to there later.
            { unfixedReprs = mapInsert reprsym (Some (setInsert alt (setEmpty nameCmp))) constraint.unfixedReprs
            , fixedUni = constraint.fixedUni
            } in
          -- NOTE(vipa, 2023-12-15): Not partitioning for now, though
          -- it's probably a good thing to do later
          Some ([map (lam x. x.token) components], map mkConstraint (setToSeq alts))
        else None () in
    let pprintChildInfo = lam indent. lam env. lam chinfo.
      match pprintVarName env chinfo.name with (env, name) in
      let res = join [ indent, name, " ", info2str chinfo.info ] in
      (env, res) in
    let pprintConstraint = lam indent. lam env. lam constraint.
      let unfixed = mapBindings constraint.unfixedReprs in
      let pprintUnfixed = lam binding.
        let set = optionMapOr "Any" (lam set. join ["{", strJoin ", " (map nameGetStr (setToSeq set)), "}"]) binding.1 in
        join [indent, int2string (sym2hash binding.0), " \\in ", set, "\n"] in
      match optionMapAccum (unificationToDebug indent) env constraint.fixedUni with (env, uni) in
      let uni = optionGetOr "" uni in
      (env, join (snoc (map pprintUnfixed unfixed) uni)) in
    let mergeAndFindIncompat : [Constraint a] -> Either (Map Int (Set Int)) (Constraint a) = lam constraints.
      let res = optionFoldlM
        (lam uni. lam c. optionBind c.fixedUni (mergeUnifications uni))
        (emptyUnification ())
        constraints in
      match res with Some res
      then Right {unfixedReprs = mapEmpty _symCmp, fixedUni = Some res}
      else
        let singleton = lam k. lam v. mapInsert k v (mapEmpty nameCmp) in
        let collectIdxes = lam acc. lam idx. lam constraint.
          match constraint.fixedUni with Some uni then
            pufFold
              (lam a. lam. lam. a)
              (lam acc. lam pair. lam repr. mapInsertWith (mapUnionWith concat) pair.0 (singleton repr [idx]) acc)
              acc
              uni.reprs
          else acc in
        let potentialConflicts = foldli collectIdxes
          (mapEmpty _symCmp)
          constraints in
        let collectConflicts = lam acc. lam entry.
          let mapWithOthers : all a. all b. ([a] -> a -> [a] -> b) -> [a] -> [b] = lam f. lam xs.
            mapi (lam i. lam x. f (splitAt xs i).0 x (splitAt xs (addi i 1)).1) xs in
          if gti (mapSize entry) 1 then
            let partitions = map (setOfSeq subi) (mapValues entry) in
            let fillNeededSteps = lam pre. lam here. lam post.
              let val = foldl setUnion (foldl setUnion (setEmpty subi) pre) post in
              mapMap (lam. val) here in
            foldl (mapUnionWith setUnion) acc (mapWithOthers fillNeededSteps partitions)
          else acc in
        let conflicts = mapFoldWithKey
          (lam acc. lam. lam entry. collectConflicts acc entry)
          (mapEmpty subi)
          potentialConflicts in
        Left conflicts in
    let interface : SolInterface (Constraint a) (ChildInfo a) PprintEnv =
      { approxOr = constraintOr
      , eq = constraintEq
      , constrainFromAbove = lam input.
        let res = constrain {parent = input.parent, child = input.here} in
        let env = pprintEnvEmpty in
        match mapAccumL (pprintChildInfo "") env input.path with (env, path) in
        let path = join["[", strJoin ", " path, "]"] in
        printLn (join ["=== constrainFromAbove ", if optionIsSome res then "success " else "fail ", path, ":"]);
        match pprintConstraint "| " env input.parent with (env, parent) in
        match pprintConstraint "| " env input.here with (env, here) in
        printLn parent;
        printLn here;
        (match res with Some res then
          printLn (pprintConstraint "| " env res.res).1
         else ());
        optionMap (lam res. {parentChanged = res.parentChanged, hereChanged = res.childChanged, res = res.res}) res
      , constrainFromBelow = lam input.
        let res = constrain {parent = input.here, child = input.child} in
        let env = pprintEnvEmpty in
        match mapAccumL (pprintChildInfo "") env input.path with (env, path) in
        let path = join["[", strJoin ", " path, "]"] in
        printLn (join ["=== constrainFromBelow ", if optionIsSome res then "success " else "fail ", path, ":"]);
        match pprintConstraint "| " env input.here with (env, here) in
        match pprintConstraint "| " env input.child with (env, child) in
        printLn here;
        printLn child;
        (match res with Some res then
          printLn (pprintConstraint "| " env res.res).1
         else ());
        optionMap (lam res. {hereChanged = res.parentChanged, childChanged = res.childChanged, res = res.res}) res
      , split = #frozen"split"
      , pprintConstraint = pprintConstraint
      , pprintChildInfo = pprintChildInfo
      , mergeAndFindIncompat = mergeAndFindIncompat
      } in
    let top = STIAndDep
      { components = topTrees
      , cost = 0.0
      , childInfo = {name = nameNoSym "<program>", info = NoInfo ()}
      , construct = lam x. x
      , constraint =
        { unfixedReprs = mapEmpty _symCmp
        , fixedUni = Some (emptyUnification ())
        }
      } in
    match solTreeMinimumSolution debug interface pprintEnvEmpty top with Some sol
    then map (lam x. SSContent x) sol
    else error "Could not find a consistent assignment of operation implementations for the program."

  sem addOpUse debug global branch query = | opUse ->
    match branch with SBContent branch in
    match query with STQContent query in
    match buildQueryItem branch opUse.scaling opUse.ident opUse.ty with (branch, itemWithMeta) in
    (SBContent branch, STQContent (snoc query itemWithMeta.item))

  sem buildQueryItem
    : all a. SBContent a
    -> OpCost
    -> Name
    -> Type
    -> (SBContent a, {reprLevels : Map Symbol Int, item : QueryItem a})
  sem buildQueryItem branch scale op = | ty ->
    match mkLocallyNameless branch.nameless ty with nl & {res = ty} in
    let branch = {branch with nameless = nl.state} in
    match
      match mapLookup (op, ty) branch.memo with Some subWithMeta
      then (branch, subWithMeta)
      else
        let emptyWithMeta =
          { reprLevels = mapEmpty _symCmp
          , tree = STIOr {alternatives = []}
          } in
        let branch = {branch with memo = mapInsert (op, ty) emptyWithMeta branch.memo} in
        match buildQueryItemWork branch op ty with (branch, subWithMeta) in
        let branch = {branch with memo = mapInsert (op, ty) subWithMeta branch.memo} in
        (branch, subWithMeta)
    with (branch, subWithMeta) in
    let rewriteConstraint = lam mapping. lam constraint.
      -- TODO(vipa, 2023-12-18): This likely clobbers some variables
      -- for the same reason we change how things work in the NOTE
      -- comment below with the same date.
      let fixedUni = optionBind constraint.fixedUni (applyLocallyNamelessMappingUni mapping) in
      let uniFailed = if optionIsSome constraint.fixedUni
        then optionIsNone fixedUni
        else false in
      if uniFailed then None () else  -- NOTE(vipa, 2023-12-13): Early return

      let translateRepr = lam acc. lam k. lam v.
        -- NOTE(vipa, 2023-12-18): If an unrewritten binding conflicts
        -- with a rewritten binding we prefer the rewritten one,
        -- because the unrewritten one must be irrelevant to the child
        -- we're interacting with now
        match mapLookup k mapping.repr with Some (k, _) then
          mapInsert k v acc
        else mapInsertWith (lam x. lam. x) k v acc in
      let unfixedReprs = mapFoldWithKey translateRepr (mapEmpty _symCmp) constraint.unfixedReprs in
      Some
      { unfixedReprs = unfixedReprs
      , fixedUni = fixedUni
      } in
    let tree = match subWithMeta.tree with STIOr {alternatives = []}
      then subWithMeta.tree
      else STIConstraintTransform
        { child = subWithMeta.tree
        , fromAbove = lam x.
          printLn "Constraint transform using this mapping:";
          let printMap = lam pk. lam pv. lam env. lam m.
            let pairs = mapAccumL
              (lam env. lam pair.
                match pk env pair.0 with (env, k) in
                match pv env pair.1 with (env, v) in
                (env, join [k, " -> ", v, "\n"]))
              env
              (mapBindings m) in
            match pairs with (env, pairs) in
            printLn (join pairs);
            env in
          let pprintSymPair = lam e. lam pair.
            (e, join [int2string (sym2hash pair.0), "#", int2string pair.1]) in
          let env = printMap pprintVarName pprintVarName pprintEnvEmpty nl.forward.var in
          let env = printMap (lam e. lam s. (e, int2string (sym2hash s))) pprintSymPair env nl.forward.repr in
          let env = printMap pprintVarName (lam e. lam n. pprintVarName e n.0) env nl.forward.meta in
          let res = rewriteConstraint nl.forward x in
          (if optionIsNone res then
            printLn "Failed via constraint transform fromAbove (nl)"
           else ());
          res
        , fromBelow = lam x.
          let res = rewriteConstraint nl.backward x in
          (if optionIsNone res then
            printLn "Failed via constraint transform fromBelow (nl)"
           else ());
          res
        } in
    let item =
      { child = tree
      , scale = scale
      } in
    let translateReprLevelUp = lam acc. lam k. lam v.
      let pair = mapLookupOr (k, v) k nl.backward.repr in
      mapInsert pair.0 pair.1 acc in
    let reprLevels = mapFoldWithKey translateReprLevelUp
      (mapEmpty _symCmp)
      subWithMeta.reprLevels in
    (branch, {reprLevels = reprLevels, item = item})

  sem buildQueryItemWork : all a. SBContent a -> Name -> Type -> (SBContent a, {reprLevels : Map Symbol Int, tree : SolTreeInput (Constraint a) (ChildInfo a) (SolContent a)})
  sem buildQueryItemWork branch op = | ty ->
    let perUseInImpl = lam subst. lam uni. lam acc. lam idxedOpUse.
      match acc with (branch, reprLevels) in
      let opUse = idxedOpUse.opUse in
      let ty = pureApplyUniToType uni (substituteVars opUse.info subst opUse.ty) in
      match buildQueryItem branch opUse.scaling opUse.ident ty
        with (branch, itemWithMeta) in
      match itemWithMeta.item.child with STIOr {alternatives = []} then ((branch, reprLevels), None ()) else
      let reprLevels = mapUnion reprLevels itemWithMeta.reprLevels in
      ( (branch, reprLevels)
      , Some
        { child = solTreeMap (lam sol. {idxes = idxedOpUse.idxes, sol = sol}) itemWithMeta.item.child
        , scale = itemWithMeta.item.scale
        }
      )
    in

    let uniToReprInfo : Unification -> (Map Symbol Int, Map Symbol (Option (Set Name)))
      = lam uni.
        let reprLevels = pufFold
          (lam acc. lam r1. lam r2.
            let acc = mapInsert r1.0 r1.1 acc in
            mapInsert r2.0 r2.1 acc)
          (lam acc. lam r. lam repr.
            mapInsert r.0 r.1 acc)
          (mapEmpty _symCmp)
          uni.reprs in
        let unfixedReprs = pufFold
          (lam acc. lam r1. lam r2.
            let acc = mapInsert r1.0 (None ()) acc in
            mapInsert r2.0 (None ()) acc)
          (lam acc. lam r. lam repr.
            mapInsert r.0 (Some (setInsert repr (setEmpty nameCmp))) acc)
          (mapEmpty _symCmp)
          uni.reprs in
        (reprLevels, unfixedReprs) in

    let perImpl : SBContent a -> ProcOpImpl a -> (SBContent a, Option (Map Symbol Int, SolTreeInput (Constraint a) (ChildInfo a) (SolContent a)))
      = lam branch. lam impl.
        let ty = (wildToMeta impl.metaLevel (setEmpty nameCmp) ty).1 in
        match instAndSubst (infoTy impl.specType) impl.metaLevel impl.specType
          with (specType, subst) in
        match unifyPure impl.uni (removeReprSubsts specType) ty with Some uni then
          match uniToReprInfo uni with (reprLevels, unfixedReprs) in
          match mapAccumL (perUseInImpl subst uni) (branch, reprLevels) impl.opUses with ((branch, reprLevels), subTrees) in
          match optionMapM (lam x. x) subTrees with Some subTrees then
            let tree = STIAndDep
              { components = subTrees
              , cost = impl.selfCost
              , childInfo = {name = impl.op, info = impl.info}
              , construct = lam subSols. SolContent
                { token = impl.token
                , cost =
                  let addCost = lam acc. lam idxedOpUse. lam idxedSol.
                    match idxedSol.sol with SolContent x in
                    addf acc (mulf idxedOpUse.opUse.scaling x.cost) in
                  foldl2 addCost impl.selfCost impl.opUses subSols
                , impl = impl
                , highestImpl =
                  let getMaxId = lam acc. lam idxedSol.
                    match idxedSol.sol with SolContent x in
                    maxi acc x.highestImpl in
                  foldl getMaxId impl.implId subSols
                , subSols =
                  let addScale = lam idxedOpUse. lam idxedSol.
                    { idxes = idxedSol.idxes
                    , scale = idxedOpUse.opUse.scaling
                    , sol = idxedSol.sol
                    } in
                  zipWith addScale impl.opUses subSols
                }
              , constraint =
                { unfixedReprs = unfixedReprs
                , fixedUni = Some uni
                }
              } in
            -- NOTE(vipa, 2023-12-13): Filter constraints by which ones
            -- are relevant in the child/parent.
            let reprLevelsToKeep = mapFilter (lam scope. lti scope impl.reprScope) reprLevels in
            let uniFilter =
              { reprs = {scope = impl.reprScope, syms = setEmpty _symCmp}
              , types = {level = impl.metaLevel, names = setEmpty nameCmp}
              } in
            let tree = STIConstraintTransform
              { child = tree
              , fromBelow = lam constraint. Some
                { unfixedReprs = mapIntersectWith (lam a. lam. a) constraint.unfixedReprs reprLevelsToKeep
                , fixedUni = optionMap (filterUnification uniFilter) constraint.fixedUni
                }
              , fromAbove = lam constraint. Some
                { unfixedReprs = mapIntersectWith (lam a. lam. a) constraint.unfixedReprs reprLevels
                -- TODO(vipa, 2023-12-13): I don't have an easy way to
                -- filter this properly, so I'm returning a less
                -- restrictive `uni` for now, namely the one that makes
                -- no restrictions whatsoever (which is expressed with
                -- `None` in this case).
                , fixedUni = None ()
                }
              } in
            (branch, Some (reprLevelsToKeep, tree))
          else (branch, None ())
        else (branch, None ()) in

    let possibleImpls = optionMapOr [] setToSeq (mapLookup op branch.implsPerOp) in
    match mapAccumL perImpl branch possibleImpls with (branch, impls) in
    match mapAccumL (lam acc. lam pair. (mapUnion acc pair.0, pair.1)) (mapEmpty _symCmp) (filterOption impls)
      with (reprLevels, impls) in
    (branch, {reprLevels = reprLevels, tree = STIOr {alternatives = impls}})
end

lang LazyTopDownSolver = RepTypesShallowSolverInterface + UnifyPure + RepTypesHelpers + PrettyPrint + Cmp + Generalize + VarAccessHelpers + LocallyNamelessStuff + WildToMeta
  type ProcOpImpl a  =
    { implId : ImplId
    , op : Name
    , opUses : [{idxes : Set Int, opUse : TmOpVarRec}]
    , selfCost : OpCost
    , uni : Unification
    , specType : Type
    , reprScope : Int
    , metaLevel : Int
    , info : Info
    -- NOTE(vipa, 2023-07-06): A token used by the surrounding system
    -- to carry data required to reconstruct a solved AST.
    , token : a
    }
  type SolContentRec a =
    { token : a
    , cost : OpCost
    , scale : OpCost
    , uni : Unification
    , impl : ProcOpImpl a
    , highestImpl : ImplId
    , ty : Type
    , subSols : [{idxes : Set Int, sol : SolContent a}]
    }
  syn SolContent a = | SolContent (SolContentRec a)

  type SBContent a =
    { implsPerOp : Map Name (Set (ProcOpImpl a))
    , memo : Map (Name, Type) (LStream (SolContentRec a))
    , nameless : NamelessState
    }

  syn SolverGlobal a = | SGContent ()
  syn SolverBranch a = | SBContent (SBContent a)
  syn SolverSolution a = | SSContent (SolContent a)
  syn SolverTopQuery a = | STQContent [Choices a]

  sem initSolverGlobal = | _ -> SGContent ()
  sem initSolverBranch = | _ -> SBContent
    { implsPerOp = mapEmpty nameCmp
    , memo = mapEmpty cmpOpPair
    , nameless =
      { metas = []
      , vars = []
      , reprs = []
      }
    }
  sem initSolverTopQuery = | _ -> STQContent []

  -- NOTE(vipa, 2023-11-07): This typically assumes that the types
  -- have a representation that is equal if the two types are
  -- alpha-equivalent.
  sem cmpOpPair : (Name, Type) -> (Name, Type) -> Int
  sem cmpOpPair l = | r ->
    let res = nameCmp l.0 r.0 in
    if neqi 0 res then res else
    let res = cmpType l.1 r.1 in
    res

  sem cmpSolution a = | b ->
    recursive let work : all x. {idxes : x, sol : Unknown} -> {idxes : x, sol : Unknown} -> Int = lam a. lam b.
      match (a, b) with ({sol = SolContent a}, {sol = SolContent b}) in
      let res = subi a.impl.implId b.impl.implId in
      if neqi 0 res then res else
      let res = seqCmp work a.subSols b.subSols in
      res in
    match (a, b) with (SSContent a, SSContent b) in
    work {idxes = (), sol = a} {idxes = (), sol = b}

  sem concretizeSolution global =
  | SSContent (SolContent x) ->
    let subSols = foldl
      (lam acc. lam sub. setFold (lam acc. lam idx. mapInsert idx (SSContent sub.sol) acc) acc sub.idxes)
      (mapEmpty subi)
      x.subSols in
    (x.token, x.highestImpl, mapValues subSols)

  sem addImpl global branch = | impl ->
    match branch with SBContent branch in

    let idxedOpUses = mapi (lam i. lam opUse. {idxes = setInsert i (setEmpty subi), opUse = opUse}) impl.opUses in
    let procImpl =
      { implId = impl.implId
      , op = impl.op
      , opUses = idxedOpUses
      , selfCost = impl.selfCost
      , uni = impl.uni
      , specType = impl.specType
      , reprScope = impl.reprScope
      , metaLevel = impl.metaLevel
      , info = impl.info
      , token = impl.token
      } in

    let branch =
      { branch with
        implsPerOp = mapInsertWith setUnion
          impl.op
          (setInsert procImpl (setEmpty (lam a. lam b. subi a.implId b.implId)))
          branch.implsPerOp
      -- OPT(vipa, 2023-11-07): Better memoization cache invalidation,
      -- or incremental computation that never needs to invalidate
      , memo = mapEmpty cmpOpPair
      } in
    SBContent branch

  sem debugBranchState global = | SBContent branch ->
    printLn "debugBranchState"

  sem debugSolution global = | solutions ->
    recursive let work = lam indent. lam sol.
      match sol with SolContent x in
      -- TODO(vipa, 2023-11-28): This will print things in a strange
      -- order, and de-duped, which might not be desirable
      join
        [ indent, nameGetStr x.impl.op, " (cost: ", float2string x.cost
        , ", scaling: ", float2string x.scale, ", info: ", info2str x.impl.info
        , ")\n"
        , join (map (lam x. work (concat indent "  ") x.sol) x.subSols)
        ]
    in join
      [ "\n# Solution cost tree:\n"
      , join (map (lam x. match x with SSContent x in work "" x) solutions)
      ]

  sem topSolve debug file global = | STQContent choices ->
    let sols = exploreSolutions 0.0 (emptyUnification ()) choices in
    match lazyStreamUncons sols with Some (sol, _) then
      let sols = foldl
        (lam acc. lam sub.
          setFold (lam acc. lam idx. mapInsert idx (SSContent (SolContent sub.sol)) acc) acc sub.idxes)
        (mapEmpty subi)
        sol.sols in
      mapValues sols
    else errorSingle [] "Could not pick implementations for all operations."

  sem addOpUse debug global branch query = | opUse ->
    match branch with SBContent branch in
    match query with STQContent query in
    match solutionsFor branch opUse.ident opUse.ty with (branch, stream) in
    let query = snoc query {idxes = setInsert (length query) (setEmpty subi), scaling = opUse.scaling, sols = stream} in
    (SBContent branch, STQContent query)

  sem solutionsFor : all a. SBContent a -> Name -> Type -> (SBContent a, LStream (SolContentRec a))
  sem solutionsFor branch op = | ty ->
    let nl = mkLocallyNameless branch.nameless ty in
    let ty = nl.res in
    let branch = {branch with nameless = nl.state} in
    match
      match mapLookup (op, ty) branch.memo with Some sols then
        (branch, sols)
      else
        let branch = {branch with memo = mapInsert (op, ty) (lazyStreamEmpty ()) branch.memo} in
        match solutionsForWork branch op ty with (branch, sols) in
        let branch = {branch with memo = mapInsert (op, ty) sols branch.memo} in
        (branch, sols)
    with (branch, sols) in
    let revSol = lam sol.
      match applyLocallyNamelessMappingUni nl.backward sol.uni with Some uni
      then Some
        { sol with uni = uni
        , ty = applyLocallyNamelessMappingTy nl.backward sol.ty
        }
      else None () in
    (branch, lazyStreamMapOption revSol sols)

  sem cmpSolCost : all a. SolContentRec a -> SolContentRec a -> Int
  sem cmpSolCost a = | b ->
    if ltf a.cost b.cost then negi 1 else
    if gtf a.cost b.cost then 1 else
    0

  type Choices a = {idxes : Set Int, scaling : OpCost, sols : LStream (SolContentRec a)}
  type SolBase a = {cost : OpCost, uni : Unification, sols : [{idxes : Set Int, sol : SolContentRec a}]}

  sem solutionsForWork
    : all a. SBContent a
    -> Name
    -> Type
    -> (SBContent a, LStream (SolContentRec a))
  sem solutionsForWork branch op = | ty ->
    let perUseInImpl = lam subst. lam uni. lam branch. lam idxedOpUse.
      let opUse = idxedOpUse.opUse in
      let ty = pureApplyUniToType uni (substituteVars opUse.info subst opUse.ty) in
      match solutionsFor branch opUse.ident ty
        with (branch, here) in
      (branch, {idxes = idxedOpUse.idxes, scaling = opUse.scaling, sols = here}) in

    let finalizeSolBase : ProcOpImpl a -> SolBase a -> SolContentRec a
      = lam impl. lam sol.
      { token = impl.token
      , cost = sol.cost
      , scale = 1.0
      , uni = filterUnification
        { types = {level = impl.metaLevel, names = setEmpty nameCmp}
        , reprs = {scope = impl.reprScope, syms = setEmpty _symCmp}
        }
        sol.uni
      , impl = impl
      , highestImpl = foldl
        (lam acc. lam x. if geqi acc x.sol.highestImpl then acc else x.sol.highestImpl)
        impl.implId
        sol.sols
      , ty = ty
      , subSols = map (lam x. {idxes = x.idxes, sol = SolContent x.sol}) sol.sols
      }
    in

    let perImpl : SBContent a -> ProcOpImpl a -> (SBContent a, LStream (SolContentRec a))
      = lam branch. lam impl.
        let ty = (wildToMeta impl.metaLevel (setEmpty nameCmp) ty).1 in
        match instAndSubst (infoTy impl.specType) impl.metaLevel impl.specType
          with (specType, subst) in
        match unifyPure impl.uni (removeReprSubsts specType) ty with Some uni then
          match mapAccumL (perUseInImpl subst uni) branch impl.opUses with (branch, subSols) in
          (branch, lazyStreamMap (finalizeSolBase impl) (exploreSolutions impl.selfCost uni subSols))
        else (branch, lazyStreamEmpty ()) in

    let filterShadow : [Unification] -> SolContentRec a -> ([Unification], Bool)
      = lam prev. lam new.
        recursive let work = lam acc. lam rest.
          match rest with [old] ++ rest then
            let oldFitsWhereNewCouldBe = uniImplies new.uni old in
            if oldFitsWhereNewCouldBe then (prev, false) else
            let newFitsWhereOldCouldBe = uniImplies old new.uni in
            if newFitsWhereOldCouldBe
            then work acc rest
            else work (snoc acc old) rest
          else (snoc acc new.uni, true)
        in work [] prev in

    let impls = optionMapOr [] setToSeq (mapLookup op branch.implsPerOp) in
    match mapAccumL perImpl branch impls with (branch, impls) in
    let sols = lazyStreamMergeMin cmpSolCost impls in
    let sols = lazyStreamStatefulFilter filterShadow [] sols in
    (branch, sols)

  sem exploreSolutions : all a. OpCost -> Unification -> [Choices a] -> LStream (SolBase a)
  sem exploreSolutions baseCost baseUni = | choices ->
    let idxes = map (lam x. x.idxes) choices in
    -- NOTE(vipa, 2023-12-01): The index chosen for this potential
    -- solution for each choice (i.e., how many times we've stepped in
    -- the respective streams).
    type ComboId = [Int] in
    type PotentialSolution =
      { cost : OpCost
      , combo : ComboId
      , here : [SolContentRec a]
      , tails : [LStream (SolContentRec a)]
      } in
    type State =
      { queue : Heap PotentialSolution
      , consideredCombos : Set ComboId
      } in

    let cmpByCost = lam a. lam b.
      if ltf a.cost b.cost then negi 1 else
      if gtf a.cost b.cost then 1 else
      0 in
    let cmpComboId = seqCmp subi in

    let splitFirst = lam choices.
      let sols = lazyStreamMap
        (lam x.
          { x with cost = mulf choices.scaling x.cost
          , scale = mulf choices.scaling x.scale
          })
        choices.sols in
      lazyStreamUncons sols in

    let addSuccessors : PotentialSolution -> Option Int -> State -> State = lam sol. lam failIdx. lam st.
      let stepAtIdx : PotentialSolution -> Int -> Option PotentialSolution = lam sol. lam idx.
        match lazyStreamUncons (get sol.tails idx) with Some (new, tail)
        then Some
          -- TODO(vipa, 2023-12-01): Do I need to worry about float
          -- stability here? Hopefully not.
          { cost = addf (subf sol.cost (get sol.here idx).cost) new.cost
          , combo = set sol.combo idx (addi 1 (get sol.combo idx))
          , here = set sol.here idx new
          , tails = set sol.tails idx tail
          }
        else None () in
      let succ =
        match failIdx with Some failIdx then
          -- NOTE(vipa, 2023-12-06): Try to find repr conflicts, pairs
          -- of operations that trivially cannot co-exist in the same
          -- solution
          let singleton = lam k. lam v. mapInsert k v (mapEmpty nameCmp) in
          let collectIdxes = lam acc. lam idx. lam sol.
            pufFold
              (lam a. lam. lam. a)
              (lam acc. lam pair. lam repr. mapInsertWith (mapUnionWith concat) pair.0 (singleton repr [idx]) acc)
              acc
              sol.uni.reprs in
          let potentialConflicts = foldli collectIdxes
            (mapEmpty _symCmp)
            sol.here in
          let collectConflicts = lam acc. lam entry.
            let mapWithOthers : all a. all b. ([a] -> a -> [a] -> b) -> [a] -> [b] = lam f. lam xs.
              mapi (lam i. lam x. f (splitAt xs i).0 x (splitAt xs (addi i 1)).1) xs in
            if gti (mapSize entry) 1 then
              let partitions = map (setOfSeq subi) (mapValues entry) in
              let fillNeededSteps = lam pre. lam here. lam post.
                let val = foldl setUnion (foldl setUnion (setEmpty subi) pre) post in
                mapMap (lam. val) here in
              foldl (mapUnionWith setUnion) acc (mapWithOthers fillNeededSteps partitions)
            else acc in
          let conflicts = mapFoldWithKey
            (lam acc. lam. lam entry. collectConflicts acc entry)
            (mapEmpty subi)
            potentialConflicts in
          if mapIsEmpty conflicts
          -- NOTE(vipa, 2023-12-06): Couldn't find simple repr
          -- conflicts, fall back to failIdx
          then create failIdx (stepAtIdx sol)
          else mapFoldWithKey
            (lam acc. lam. lam idxesToStep. snoc acc (optionFoldlM stepAtIdx sol (setToSeq idxesToStep)))
            []
            conflicts
        else create (length sol.here) (stepAtIdx sol) in
      let checkSeen = lam seen. lam potential.
        match potential with Some potential then
          if setMem potential.combo seen
          then (seen, None ())
          else (setInsert potential.combo seen, Some potential)
        else (seen, None ()) in
      match mapAccumL checkSeen st.consideredCombos succ with (consideredCombos, succ) in
      let succ = filterOption succ in
      { queue = heapAddMany cmpByCost succ st.queue
      , consideredCombos = consideredCombos
      }
    in

    recursive let step : State -> Option (() -> State, SolBase a) = lam state.
      let foldlFailIdx : all acc. all a. (acc -> a -> Option acc) -> acc -> [a] -> Either Int acc
        = lam f. lam acc. lam l.
          recursive let work = lam acc. lam idx. lam l.
            match l with [x] ++ l then
              match f acc x with Some acc
              then work acc (addi idx 1) l
              else Left (addi idx 1)
            else Right acc
          in work acc 0 l
      in
      match heapPop cmpByCost state.queue with Some (potential, queue) then
        let state = {state with queue = queue} in
        switch foldlFailIdx (lam acc. lam x. mergeUnifications acc x.uni) baseUni potential.here
        case Right uni then
          let solBase =
            { cost = potential.cost
            , uni = uni
            , sols = zipWith (lam idxes. lam sol. {idxes = idxes, sol = sol}) idxes potential.here
            } in
          Some (lam. addSuccessors potential (None ()) state, solBase)
        case Left idx then
          step (addSuccessors potential (Some idx) state)
        end
      else None ()
    in

    match optionMapM splitFirst choices with Some zipped then
      let mkState = lam.
        match unzip zipped with (here, tails) in
        let cost = foldl (lam acc. lam x. addf acc x.cost) baseCost here in
        let combo = make (length here) 0 in
        { queue = heapSingleton {cost = cost, combo = combo, here = here, tails = tails}
        -- NOTE(vipa, 2023-12-01): We can never add the first combo
        -- again, so it's unnecessary to track that we've already seen
        -- it
        , consideredCombos = setEmpty cmpComboId
        } in
      lazyStreamLaziest step mkState
    else lazyStreamEmpty ()
end

lang MemoedTopDownSolver = RepTypesShallowSolverInterface + UnifyPure + RepTypesHelpers + PrettyPrint + Cmp + Generalize + VarAccessHelpers + LocallyNamelessStuff + WildToMeta
  -- NOTE(vipa, 2023-11-28): We pre-process impls to merge repr vars,
  -- meta vars, and opUses, split the problem into disjoint
  -- sub-problems, and re-order opUses such that we can drop internal
  -- repr vars and meta vars as soon as possible.
  syn SolveCommand =
  | AddOpVar {idxes : Set Int, opUse : TmOpVarRec}
  | FilterVars (VarMap ())
  type ProcOpImpl a  =
    { implId: ImplId
    , op : Name
    , problem : [SolveCommand]
    , selfCost : OpCost
    , uni : Unification
    , specType : Type
    , reprScope : Int
    , metaLevel : Int
    , info : Info
    -- NOTE(vipa, 2023-07-06): A token used by the surrounding system
    -- to carry data required to reconstruct a solved AST.
    , token : a
    }

  type SolContentRec a =
    { token : a
    , cost : OpCost
    , scale : OpCost
    , uni : Unification
    , impl : ProcOpImpl a
    , highestImpl : ImplId
    , ty : Type
    , subSols : [{idxes : Set Int, sol : SolContent a}]
    }
  syn SolContent a = | SolContent (SolContentRec a)

  type SBContent a =
    { implsPerOp : Map Name (Set (ProcOpImpl a))
    , memo : Map (Name, Type) [SolContent a]
    , nameless : NamelessState
    }

  syn SolverGlobal a = | SGContent ()
  syn SolverBranch a = | SBContent (SBContent a)
  syn SolverSolution a = | SSContent (SolContent a)
  syn SolverTopQuery a = | STQContent [(OpCost, [SolContent a])]

  sem initSolverGlobal = | _ -> SGContent ()
  sem initSolverBranch = | global -> SBContent
    { implsPerOp = mapEmpty nameCmp
    , memo = mapEmpty cmpOpPair
    , nameless =
      { metas = []
      , vars = []
      , reprs = []
      }
    }
  sem initSolverTopQuery = | _ -> STQContent []

  -- NOTE(vipa, 2023-11-07): This typically assumes that the types
  -- have a representation that is equal if the two types are
  -- alpha-equivalent.
  sem cmpOpPair : (Name, Type) -> (Name, Type) -> Int
  sem cmpOpPair l = | r ->
    let res = nameCmp l.0 r.0 in
    if neqi 0 res then res else
    let res = cmpType l.1 r.1 in
    res

  sem cmpSolution a = | b ->
    recursive let work : all x. {idxes : x, sol : Unknown} -> {idxes : x, sol : Unknown} -> Int = lam a. lam b.
      match (a, b) with ({sol = SolContent a}, {sol = SolContent b}) in
      let res = subi a.impl.implId b.impl.implId in
      if neqi 0 res then res else
      let res = seqCmp work a.subSols b.subSols in
      res in
    match (a, b) with (SSContent a, SSContent b) in
    work {idxes = (), sol = a} {idxes = (), sol = b}

  sem concretizeSolution global =
  | SSContent (SolContent x) ->
    let subSols = foldl
      (lam acc. lam sub. setFold (lam acc. lam idx. mapInsert idx (SSContent sub.sol) acc) acc sub.idxes)
      (mapEmpty subi)
      x.subSols in
    (x.token, x.highestImpl, mapValues subSols)

  sem debugBranchState global = | SBContent branch ->
    let perImpl = lam env. lam op. lam impls.
      match pprintVarName env op with (env, op) in
      printLn (join ["  ", op, ", letimpl count: ", int2string (setSize impls)]);
      env in
    let perSol = lam env. lam sol.
      match sol with SolContent sol in
      match unificationToDebug "     " env sol.uni with (env, uni) in
      print (join ["    cost: ", float2string sol.cost, ", uni:\n", uni]);
      env in
    let perMemo = lam env. lam pair. lam sols.
      match pprintVarName env pair.0 with (env, op) in
      match getTypeStringCode 0 env pair.1 with (env, ty) in
      printLn (join ["  ", op, " (count: ", int2string (length sols), ") : ", ty]);
      let env = foldl perSol env sols in
      env in
    let env = pprintEnvEmpty in
    printLn "\nImpl Solver debug status:\n # Impls:";
    let env = mapFoldWithKey perImpl env branch.implsPerOp in
    printLn " # Solutions:";
    let env = mapFoldWithKey perMemo env branch.memo in
    ()

  sem debugSolution global = | solutions ->
    recursive let work = lam indent. lam sol.
      match sol with SolContent x in
      -- TODO(vipa, 2023-11-28): This will print things in a strange
      -- order, and de-duped, which might not be desirable
      join
        [ indent, nameGetStr x.impl.op, " (cost: ", float2string x.cost
        , ", scaling: ", float2string x.scale, ", info: ", info2str x.impl.info
        , ")\n"
        , join (map (lam x. work (concat indent "  ") x.sol) x.subSols)
        ]
    in join
      [ "\n# Solution cost tree:\n"
      , join (map (lam x. match x with SSContent x in work "" x) solutions)
      ]

  sem addImpl global branch = | impl ->
    match branch with SBContent branch in

    let preProc = wallTimeMs () in
    let idxedOpUses = mapi (lam i. lam opUse. {idxes = setInsert i (setEmpty subi), opUse = opUse}) impl.opUses in
    let filter = {metaLevel = impl.metaLevel, scope = impl.reprScope} in
    let externalVars = getVarsInType filter varMapEmpty impl.specType in
    let countInternalVarUses = lam acc. lam idxedOpUse.
      let internal = varMapDifference (getVarsInType filter varMapEmpty idxedOpUse.opUse.ty) externalVars in
      let addOne = lam acc. lam k. lam. mapInsertWith addi k 1 acc in
      let metas = mapFoldWithKey addOne acc.metas internal.metas in
      let reprs = mapFoldWithKey addOne acc.reprs internal.reprs in
      {metas = metas, reprs = reprs} in
    -- recursive let mkCommands
    --   : [SolveCommand] -> VarMap Int -> [{idxes : Set Int, opUse : TmOpVarRec}] -> [SolveCommand]
    --   = lam acc. lam initialVars. lam rest.
    --     match rest with [] then acc else
    --     match varMapMinBy subi initialVars with Some (sOrN, _) then
    --       match partition (lam x. typeMentionsVarInVarMap (varMapSingleton sOrN ()) x.opUse.ty) rest with (mention, rest) in
    --       let acc = concat acc (map (lam x. AddOpVar x) mention) in
    --       let nextVars = varMapDifference (foldl countInternalVarUses varMapEmpty rest) externalVars in
    --       let acc = snoc acc (FilterVars (varMapMap (lam. ()) nextVars)) in
    --       mkCommands acc nextVars rest
    --     else
    --       printLn (join ["mkCommands else ", int2string (length rest)]);
    --       concat acc (map (lam x. AddOpVar x) rest)
    -- in
    let mkCommandsOld = lam idxedOpUses. snoc (map (lam x. AddOpVar x) idxedOpUses) (FilterVars varMapEmpty) in

    let procImpl =
      { implId = impl.implId
      , op = impl.op
      -- , problem = mkCommands []
      --   (varMapDifference (foldl countInternalVarUses varMapEmpty idxedOpUses) externalVars)
      --   idxedOpUses
      , problem = mkCommandsOld idxedOpUses
      , selfCost = impl.selfCost
      , uni = impl.uni
      , specType = impl.specType
      , reprScope = impl.reprScope
      , metaLevel = impl.metaLevel
      , info = impl.info
      , token = impl.token
      } in
    let postProc = wallTimeMs () in
    printLn (join ["rejuggle: ", float2string (subf postProc preProc)]);

    let branch =
      { branch with
        implsPerOp = mapInsertWith setUnion
          impl.op
          (setInsert procImpl (setEmpty (lam a. lam b. subi a.implId b.implId)))
          branch.implsPerOp
      -- OPT(vipa, 2023-11-07): Better memoization cache invalidation,
      -- or incremental computation that never needs to invalidate
      , memo = mapEmpty cmpOpPair
      } in
    SBContent branch

  sem topSolve debug file global = | STQContent opUses ->
    -- TODO(vipa, 2023-10-26): Port solveViaModel and use it here if we have a large problem
    let mergeOpt = lam prev. lam sol.
      match mergeUnifications prev.uni sol.uni with Some uni then Some
        { uni = uni
        , cost = addf prev.cost sol.cost
        , sols = snoc prev.sols sol.sol
        }
      else None () in
    let mapF = lam opUse.
      match opUse with (scaling, sols) in
      let mapF = lam sol.
        match sol with SolContent x in
        { sol = SSContent sol, uni = x.uni, cost = mulf x.cost scaling } in
      map mapF sols in
    let opUses = map mapF opUses in
    let f = lam prev. lam sols.
      filterOption (seqLiftA2 mergeOpt prev sols) in
    let sols = foldl f [{uni = emptyUnification (), cost = 0.0, sols = []}] opUses in
    match sols with [sol] ++ sols then
      (foldl (lam sol. lam sol2. if ltf sol2.cost sol.cost then sol2 else sol) sol sols).sols
    else errorSingle [] "Could not pick implementations for all operations."

  sem addOpUse debug global branch query = | opUse ->
    (if debug then
      printLn (join ["\n# Solving process", info2str opUse.info, ":"])
     else ());
    match branch with SBContent branch in
    match query with STQContent query in
    match solutionsFor (if debug then Some "" else None ()) branch opUse.ident opUse.ty with (branch, sols) in
    (if debug then
      printLn (join ["=> ", int2string (length sols), " solutions"])
     else ());
    (SBContent branch, STQContent (snoc query (opUse.scaling, sols)))

  -- NOTE(vipa, 2023-11-07): Wrapper function that handles memoization and termination
  sem solutionsFor : all a. Option String -> SBContent a -> Name -> Type -> (SBContent a, [SolContent a])
  sem solutionsFor debugIndent branch op = | ty ->
    let nl = mkLocallyNameless branch.nameless ty in
    let ty = nl.res in
    let branch = {branch with nameless = nl.state} in
    match
      match mapLookup (op, ty) branch.memo with Some sols then
        (match debugIndent with Some indent then
          printLn (join [indent, nameGetStr op, " (memo, ", int2string (length sols), " solutions)"])
         else ());
        (branch, sols)
      else
        let branch = {branch with memo = mapInsert (op, ty) [] branch.memo} in
        match solutionsForWork debugIndent branch op ty with (branch, sols) in
        let branch = {branch with memo = mapInsert (op, ty) sols branch.memo} in
        (branch, sols)
    with (branch, sols) in
    let revSol = lam sol.
      match sol with SolContent sol in
      match applyLocallyNamelessMappingUni nl.backward sol.uni with Some uni
      then Some (SolContent
        { sol with uni = uni
        , ty = applyLocallyNamelessMappingTy nl.backward sol.ty
        })
      else None () in
    (branch, mapOption revSol sols)

  -- NOTE(vipa, 2023-11-07): Function that does the actual work
  sem solutionsForWork
    : all a. Option String
    -> SBContent a
    -> Name
    -> Type
    -> (SBContent a, [SolContent a])
  sem solutionsForWork debugIndent branch op = | ty ->
    let perSolInUseInImpl = lam idxedOpUse. lam prev. lam sol.
      match sol with SolContent x in
      let mk = lam uni.
        { prev with uni = uni
        , cost = addf prev.cost (mulf idxedOpUse.opUse.scaling x.cost)
        , highestImpl = maxi prev.highestImpl x.highestImpl
        , subSols = snoc prev.subSols {idxes = idxedOpUse.idxes, sol = SolContent {x with scale = idxedOpUse.opUse.scaling}}
        } in
      let merged = mergeUnifications prev.uni x.uni in
      optionMap mk merged
    in

    let perCommandInImpl = lam filter. lam subst. lam uni. lam acc. lam command.
      if null acc.prev then acc else
      let debugIndent = optionMap (concat "  ") debugIndent in
      switch command
      case AddOpVar idxedOpUse then
        let opUse = idxedOpUse.opUse in
        let ty = pureApplyUniToType uni (substituteVars opUse.info subst opUse.ty) in
        let preSolFor = wallTimeMs () in
        match solutionsFor debugIndent acc.branch opUse.ident ty
          with (branch, here) in
        let postSolFor = wallTimeMs () in
        let curr = filterOption (seqLiftA2 (perSolInUseInImpl idxedOpUse) acc.prev here) in
        let postStep = wallTimeMs () in
        (match debugIndent with Some indent then
          printLn (join
            [ indent, "post ", nameGetStr opUse.ident
            , ", live partials: ", int2string (length acc.prev), "*", int2string (length here)
            , " -> ", int2string (length curr)
            , ", solfor: ", float2string (subf postSolFor preSolFor), "ms"
            , ", step: ", float2string (subf postStep postSolFor), "ms"
            ])
         else ());
        {branch = branch, prev = curr}
      case FilterVars vars then
        let filter =
          { types = {level = filter.level, names = vars.metas}
          , reprs = {scope = filter.scope, syms = vars.reprs}
          } in
        let prevCount = length acc.prev in
        let preTime = wallTimeMs () in
        let prev = map (lam x. {x with uni = filterUnification filter x.uni}) acc.prev in
        let prev = pruneRedundant prev in
        let postTime = wallTimeMs () in
        let postCount = length prev in
        (match debugIndent with Some indent then
          printLn (join
            [ indent, "filter and prune vars ("
            , int2string prevCount, " -> ", int2string postCount
            , ", ", float2string (subf postTime preTime), "ms)"
            ])
         else ());
        {prev = pruneRedundant prev, branch = acc.branch}
      end in

    let perImpl = lam acc : {branch : SBContent a, sols : [SolContentRec a]}. lam impl.
      let ty = (wildToMeta impl.metaLevel (setEmpty nameCmp) ty).1 in
      let debugIndent = optionMap (concat " ") debugIndent in
      (match debugIndent with Some indent then
        print (join [indent, "trying impl with ", int2string (length impl.problem), " commands"])
       else ());
      match instAndSubst (infoTy impl.specType) impl.metaLevel impl.specType
        with (specType, subst) in
      match unifyPure impl.uni (removeReprSubsts specType) ty with Some uni then
        (match debugIndent with Some _ then
          printLn ""
         else ());
        let solInit =
          { token = impl.token
          , cost = impl.selfCost
          , scale = 1.0
          , uni = uni
          , impl = impl
          , highestImpl = impl.implId
          , ty = ty
          , subSols = []
          } in
        let filterValues = {level = impl.metaLevel, scope = impl.reprScope} in
        let innerAcc = foldl (perCommandInImpl filterValues subst uni) {branch = acc.branch, prev = [solInit]} impl.problem in
        let uniFilter =
          -- NOTE(vipa, 2023-11-13): The substitution business ensures
          -- that all metas/reprs in `ty` are in a level/scope lesser
          -- than the current, i.e., we can skip computing the set of
          -- those in the signature
          { reprs =
            { scope = impl.reprScope
            , syms = setEmpty _symCmp
            }
          , types =
            { level = impl.metaLevel
            , names = setEmpty nameCmp
            }
          } in
        let finalizeSol = lam sol.
          if ltf sol.cost 0.0
          then errorSingle [sol.impl.info] "This impl gave rise to a solution with a negative cost; this is not allowed."
          else {sol with uni = filterUnification uniFilter sol.uni} in
        let newSols = map finalizeSol innerAcc.prev in
        {branch = innerAcc.branch, sols = concat acc.sols newSols}
      else
        (match debugIndent with Some indent then
          printLn " (failed first unification)"
         else ());
        acc
    in

    (match debugIndent with Some indent then
      printLn (join [indent, nameGetStr op, ":"])
     else ());
    let impls = optionMapOr [] setToSeq (mapLookup op branch.implsPerOp) in
    match foldl perImpl {branch = branch, sols = []} impls with {branch = branch, sols = sols} in
    (branch, map (lam x. SolContent x) (pruneRedundant sols))

  sem pruneRedundant : all a. [SolContentRec a] -> [SolContentRec a]
  sem pruneRedundant = | sols ->
    let filterM : all a. (a -> Option Bool) -> [a] -> Option [a] = lam f. lam xs.
      recursive let work = lam acc. lam xs.
        match xs with [x] ++ xs then
          match f x with Some keep
          then work (if keep then snoc acc x else acc) xs
          else None ()
        else Some acc
      in work [] xs in
    -- NOTE(vipa, 2023-11-07): `Some _` means add the new, `Some true`
    -- means keep the old, `Some false` means remove the old.
    let check = lam new. lam old.
      let newIsCheaper = ltf new.cost old.cost in
      -- NOTE(vipa, 2023-11-07): Since solutions are created unified
      -- with the same type we already know that both `ty`s are the
      -- same modulo assertions in their respective `uni`s, thus we
      -- skip the (unify (instantiated) (stripped)) in both "fits"
      -- predicates
      let oldFitsWhereNewCouldBe = uniImplies new.uni old.uni in
      let existenceDenied = and (not newIsCheaper) oldFitsWhereNewCouldBe in
      if existenceDenied then None () else
      let newFitsWhereOldCouldBe = uniImplies old.uni new.uni in
      let oldShouldBePruned = and newIsCheaper newFitsWhereOldCouldBe in
      Some (not oldShouldBePruned)
    in
    let addSol = lam prev. lam sol.
      optionMapOr prev (lam xs. snoc xs sol) (filterM (check sol) prev)
    in
    foldl addSol [] sols
end

lang EagerRepSolver = RepTypesShallowSolverInterface + UnifyPure + RepTypesHelpers + Generalize + PrettyPrint
  type SolId = Int
  type SolContent a =
    { token : a
    , cost : OpCost
    , uni : Unification
    , specType : Type
    , impl : OpImpl a
    , depth : Int
    , highestImpl : ImplId
    , subSols : [SolId]
    }
  type SBContent a =
    { implsPerOp : Map Name (Set (OpImpl a))
    , nextSolId : SolId
    , solsById : Map SolId (SolContent a)
    , solsByOp : Map Name (Set SolId)
    }
  syn SolverGlobal a = | SGContent ()
  syn SolverBranch a = | SBContent (SBContent a)
  syn SolverSolution a = | SSContent (SBContent a, SolId)
  syn SolverTopQuery a = | STQContent [[{sol : SolverSolution a, uni : Unification, cost : OpCost}]]

  sem initSolverGlobal = | _ -> SGContent ()
  sem initSolverBranch = | global -> SBContent
    { implsPerOp = mapEmpty nameCmp
    , nextSolId = 0
    , solsById = mapEmpty subi
    , solsByOp = mapEmpty nameCmp
    }
  sem initSolverTopQuery = | _ -> STQContent []

  sem topSolve debug file global = | STQContent opUses ->
    -- TODO(vipa, 2023-10-26): Port solveViaModel and use it here if we have a large problem
    let mergeOpt = lam prev. lam sol.
      match mergeUnifications prev.uni sol.uni with Some uni then Some
        { uni = uni
        , cost = addf prev.cost sol.cost
        , sols = snoc prev.sols sol.sol
        }
      else None () in
    let f = lam prev. lam sols.
      filterOption (seqLiftA2 mergeOpt prev sols) in
    let sols = foldl f [{uni = emptyUnification (), cost = 0.0, sols = []}] opUses in
    match sols with [sol] ++ sols then
      (foldl (lam sol. lam sol2. if ltf sol2.cost sol.cost then sol2 else sol) sol sols).sols
    else errorSingle [] "Could not pick implementations for all operations."

  sem addOpUse debug global branch query = | opUse ->
    match branch with SBContent branch in
    match query with STQContent query in
    let solIds = mapLookupOr (setEmpty subi) opUse.ident branch.solsByOp in
    let checkAndAddSolution = lam acc. lam solId.
      let content = mapFindExn solId branch.solsById in
      match unifyPure content.uni opUse.ty (inst (NoInfo ()) 0 (removeReprSubsts content.specType))
      with Some uni then snoc acc
        { sol = SSContent (branch, solId)
        , cost = content.cost
        , uni = uni
        }
      else acc in
    (SBContent branch, STQContent (snoc query (setFold checkAndAddSolution [] solIds)))

  sem concretizeSolution global =
  | SSContent (branch, solId) ->
    let content = mapFindExn solId branch.solsById in
    (content.token, content.highestImpl, map (lam solId. SSContent (branch, solId)) content.subSols)

  sem cmpSolution a = | b -> match (a, b) with (SSContent a, SSContent b) in subi a.1 b.1

  -- NOTE(vipa, 2023-10-26): This is the real work of this solver;
  -- here we record all impls available, and compute and store all
  -- optimal solutions for distinct `uni`s. Think of it like a datalog
  -- store, one table per `op`, one row per solution, where each
  -- `impl` is a rule for creating new solutions from previous ones.

  sem addImpl global branch = | opImpl ->
    let start = wallTimeMs () in
    match branch with SBContent branch in
    let branch = {branch with implsPerOp = mapInsertWith setUnion
      opImpl.op
      (setInsert opImpl (setEmpty (lam a. lam b. subi a.implId b.implId)))
      branch.implsPerOp} in

    -- NOTE(vipa, 2023-10-26): Find new solutions directly due to the
    -- new impl
    let getPossibleSolutions = lam opUse. lam.
      let solIds = optionMapOr [] setToSeq (mapLookup opUse.ident branch.solsByOp) in
      (map (lam solId. (solId, mapFindExn solId branch.solsById)) solIds, ()) in
    let newSols = mkSols opImpl getPossibleSolutions () in
    let branch = foldl (addSol opImpl.op) branch newSols in

    let duration = subf (wallTimeMs ()) start in
    printError (join ["INFO", info2str opImpl.info, ": updated reptype solution closure, took ", float2string duration, "ms\n"]);
    flushStderr ();

    SBContent branch

  sem debugBranchState global = | SBContent branch ->
    let printSolByOp = lam env. lam op. lam sols.
      let printSol = lam env. lam solid.
        let sol = mapFindExn solid branch.solsById in
        match getTypeStringCode 0 env sol.specType with (env, specType) in
        recursive let metaVarLevels = lam acc. lam ty.
          match unwrapType ty with TyMetaVar x then
            match deref x.contents with Unbound x in
            snoc acc (x.ident, x.level)
          else sfold_Type_Type metaVarLevels acc ty in
        let metas = metaVarLevels [] sol.specType in
        let pprintMeta = lam env. lam meta.
          match pprintVarName env meta.0 with (env, ident) in
          (env, join [ident, "#", int2string meta.1]) in
        match mapAccumL pprintMeta env metas with (env, metas) in
        printLn (join
          [ "  ", int2string solid, " -> highId: "
          , int2string sol.highestImpl, ", subs: "
          , strJoin " " (map int2string sol.subSols)
          , ", type: ", specType
          , ", metas: ", strJoin " " metas
          , ", metaLvl: ", int2string sol.impl.metaLevel
          , ", cost: ", float2string sol.cost
          ]);
        env in
      printLn (join [nameGetStr op, ", impls: ", int2string (setSize (mapFindExn op branch.implsPerOp)), ", sols:"]);
      setFold printSol env sols
    in
    mapFoldWithKey printSolByOp pprintEnvEmpty branch.solsByOp;
    ()

  sem mkSols : all a. all x. OpImpl a -> (TmOpVarRec -> x -> ([(SolId, SolContent a)], x)) -> x -> [SolContent a]
  sem mkSols opImpl getAlts = | x ->
    match instAndSubst (infoTy opImpl.specType) opImpl.metaLevel opImpl.specType
      with (specType, subst) in
    let emptySol =
      { token = opImpl.token
      , cost = opImpl.selfCost
      , uni = opImpl.uni
      , specType = specType
      , highestImpl = opImpl.implId
      , maxInnerCost = negf 1.0
      , depth = 0
      , subSols = []
      } in
    let mergeOpt = lam opUse. lam prev. lam pair.
      match pair with (solId, candidate) in
      let unified = unifyPure prev.uni
        (substituteVars opUse.info subst opUse.ty)
        (inst opUse.info opImpl.metaLevel (removeReprSubsts candidate.specType)) in
      let oUni = optionBind unified (mergeUnifications candidate.uni) in
      let mkNext = lam uni.
        { prev with uni = uni
        , highestImpl = maxi prev.highestImpl candidate.highestImpl
        , cost = addf prev.cost (mulf opUse.scaling candidate.cost)
        , maxInnerCost = maxf prev.maxInnerCost candidate.cost
        , depth = maxi prev.depth (addi candidate.depth 1)
        , subSols = snoc prev.subSols solId
        } in
      optionMap mkNext oUni
    in
    let f = lam acc. lam opUse.
      if null acc.0 then acc else
      match getAlts opUse acc.1 with (solOptions, newX) in
      -- TODO(vipa, 2023-11-04): This isn't a very nice way to stop
      -- things exploding, and it doesn't seem to be enough either...
      let solOptions = filter (lam sol. lti sol.1 .depth 5) solOptions in
      printLn (join ["mkSols, acc.0 len: ", int2string (length acc.0), " solOpts len: ", int2string (length solOptions)]);
      let sols = filterOption (seqLiftA2 (mergeOpt opUse) acc.0 solOptions) in
      (sols, newX) in
    printLn (join ["mkSols, opUses length: ", int2string (length opImpl.opUses)]);
    let sols = (foldl f ([emptySol], x) opImpl.opUses).0 in
    printLn (join ["mkSols, sols length: ", int2string (length sols)]);
    let checkCostIncrease = lam sol.
      if leqf sol.cost sol.maxInnerCost then
        errorSingle [opImpl.info] "The final cost of an implementation must be greater than the cost of each of its constituent operations."
      else
        let specType = pureApplyUniToType sol.uni sol.specType in
        let specType = (gen (subi opImpl.metaLevel 1) (mapEmpty nameCmp) specType).0 in
        let uniFilter =
          { reprs =
            { scope = opImpl.reprScope
            , syms = foldl
              (lam acc. lam repr. setInsert (match deref (botRepr repr) with BotRepr x in x.sym) acc)
              (setEmpty _symCmp)
              (findReprs [] specType)
            }
          , types =
            { level = opImpl.metaLevel
            -- NOTE(vipa, 2023-11-03): All metavars present in the
            -- signature that have a level >= opImpl.metaLevel have
            -- been removed through `gen`, so we don't have to keep
            -- track of any such names here, it's enough to check the
            -- level.
            , names = mapEmpty nameCmp
            }
          } in
        { token = sol.token
        , cost = sol.cost
        , uni = filterUnification uniFilter sol.uni
        , specType = specType
        , impl = opImpl
        , highestImpl = sol.highestImpl
        , depth = sol.depth
        , subSols = sol.subSols
        } in
    map checkCostIncrease sols

  sem addSol : all a. Name -> SBContent a -> SolContent a -> SBContent a
  sem addSol op branch = | sol ->
    -- NOTE(vipa, 2023-10-26): Ensure that we have a minimal-ish set
    -- of solutions; no solution may be worse than another (more
    -- restrictive `uni` and higher cost).
    let solIds = mapLookupOr (setEmpty subi) op branch.solsByOp in
    let check = lam acc : Option (Set SolId). lam solId.
      match acc with Some toPrune then
        let oldSol = mapFindExn solId branch.solsById in
        let debugStuff =
          let env = pprintEnvEmpty in
          match unificationToDebug "" env oldSol.uni with (env, oldUni) in
          match getTypeStringCode 2 env oldSol.specType with (env, oldType) in
          match unificationToDebug "" env sol.uni with (env, newUni) in
          match getTypeStringCode 2 env sol.specType with (env, newType) in
          printLn (join
            [ "addSol.check, old cost: ", float2string oldSol.cost
            , ", old type: ", oldType, "\n"
            , oldUni
            ]);
          printLn (join
            [ "addSol.check, new cost: ", float2string sol.cost
            , ", new type: ", newType, "\n"
            , newUni
            ])
        in
        let newIsCheaper = gtf oldSol.cost sol.cost in
        let mergedUni = mergeUnifications oldSol.uni sol.uni in
        let oldFitsWhereNewCouldBe =
          let postUni = optionBind mergedUni (lam uni. unifyPure uni
            (inst (NoInfo ()) 0 oldSol.specType)
            (stripTyAll sol.specType).1) in
          if optionIsSome postUni
          then uniImplies sol.uni oldSol.uni
          else false in
        let existenceDenied = and (not newIsCheaper) oldFitsWhereNewCouldBe in
        -- NOTE(vipa, 2023-10-26): It *should* be the case that
        -- `existenceDenied` implies `setIsEmpty toPrune`
        if existenceDenied then None () else
        let newFitsWhereOldCouldBe =
          let postUni = optionBind mergedUni (lam uni. unifyPure uni
            (stripTyAll oldSol.specType).1
            (inst (NoInfo ()) 0 sol.specType)) in
          if optionIsSome postUni
          then uniImplies oldSol.uni sol.uni
          else false in
        let oldShouldBePruned = and newIsCheaper newFitsWhereOldCouldBe in
        Some (if oldShouldBePruned then setInsert solId toPrune else toPrune)
      else acc in
    printLn (join ["addSol, solIds size: ", int2string (setSize solIds)]);
    match setFold check (Some (setEmpty subi)) solIds with Some toPrune then
      let newSolId = branch.nextSolId in
      let branch =
        { branch with nextSolId = addi branch.nextSolId 1
        , solsByOp = mapInsert op (setInsert newSolId (setSubtract solIds toPrune)) branch.solsByOp
        , solsById = mapInsert newSolId sol (mapDifference branch.solsById toPrune)
        } in
      -- NOTE(vipa, 2023-10-26): At this point there may be `subSols`
      -- referencing solutions not present in `solsById`. These will
      -- be replaced by some of the solutions we produce now, since
      -- `sol` is strictly better than whatever they were referencing
      -- before
      let foldImpls : all acc. (acc -> OpImpl a -> acc) -> acc -> acc = lam f. lam acc. mapFoldWithKey
        (lam acc. lam. lam impls. setFold f acc impls)
        acc
        branch.implsPerOp in
      let addSolsFromImpl = lam branch. lam impl.
        let newPatterns = tail
          -- NOTE(vipa, 2023-10-26): The first sequence in the list is
          -- the one with all false, i.e., "use only old solutions",
          -- which won't come up with anything new
          (seqMapM (lam opUse. if nameEq opUse.ident op then [false, true] else [false]) impl.opUses) in
        printLn (join ["addSol, newPatterns: ", strJoin " " (map (lam pat. map (lam x. if x then 't' else 'f') pat) newPatterns)]);
        let processPattern = lam branch. lam pattern.
          let getPossibleSolutions = lam opUse. lam pattern.
            match pattern with [useNew] ++ pattern in
            if useNew then ([(newSolId, sol)], pattern) else
            let solIds = optionMapOr [] setToSeq (mapLookup opUse.ident branch.solsByOp) in
            let pairs = map (lam solId. (solId, mapFindExn solId branch.solsById)) solIds in
            (pairs, pattern) in
          let newSols = mkSols impl getPossibleSolutions pattern in
          foldl (addSol impl.op) branch newSols in
        foldl processPattern branch newPatterns
      in
      foldImpls addSolsFromImpl branch
    else
      printLn "addSol, existence denied";
      branch
end

-- lang RepTypesSolveWithExhaustiveCP = RepTypesSolverInterface + UnifyPure + COPHighLevel + ReprSubstAst + RepTypesHelpers + Generalize
--   syn SolverState =
--   | CPState ()
--   sem initSolverState = | _ -> CPState ()

--   type CPSol a =
--     { cost : OpCost
--     , specType : Type
--     , uni : Unification
--     , innerSolutions : [OpImplSolution a]
--     , idx : Int
--     , token : a
--     }

--   syn OpImplSolutionSet a =
--   | CPSolutionSet (Promise [CPSol a])

--   syn OpImplSolution a =
--   | CPSolution (CPSol a)

--   sem cmpSolution a = | b ->
--     match (a, b) with (CPSolution a, CPSolution b) in
--     subi a.idx b.idx

--   sem solveOne st prev = | alts ->
--     match prev with Some _ then
--       errorSingle [] "[panic] The cp-based RepTypes solver currently assumes all opimpls are merged into one op-impl"
--     else
--     let promise = promiseMkThread_ (lam.
--       let f = lam alt.
--         -- NOTE(vipa, 2023-08-11): Move delayedReprUnifications to
--         -- the root unification
--         let uni = optionFoldlM
--           (lam acc. lam pair. unifyReprPure acc pair.0 pair.1)
--           (emptyUnification ())
--           alt.delayedReprUnifications in

--         -- NOTE(vipa, 2023-08-11): Pull substitutions from the
--         -- type-signature and add to uni
--         recursive let applySubsts = lam oUni. lam ty.
--           let oUni =
--             match ty with TySubst {arg = arg, subst = subst, info = info} then
--               match unwrapType arg with TyRepr {repr = r} then
--                 optionBind oUni (lam uni. unifySetReprPure uni r subst)
--               else errorSingle [info] "This substitution seems to be applied to a non-repr type"
--             else oUni in
--           match ty with TyAlias x then applySubsts oUni x.content else
--           sfold_Type_Type applySubsts oUni ty in
--         let uni = match applySubsts uni alt.specType
--           with Some x then x
--           else errorSingle [alt.info] (strJoin "\n"
--             [ "This impl makes conflicting substitutions of a repr"
--             , "and is thus never valid, regardless of what other"
--             , "implementations are available."
--             ]) in

--         -- NOTE(vipa, 2023-08-11): Collect ReprVar's and MetaVar's
--         -- that are in the type signature of the alt, which are thus
--         -- externally visible even though their reprScope might be in
--         -- the current alt or further down.
--         let uniFilter =
--           let signatureReprs : Set Symbol = foldl
--             (lam acc. lam repr. setInsert (match deref (botRepr repr) with BotRepr x in x.sym) acc)
--             (setEmpty (lam a. lam b. subi (sym2hash a) (sym2hash b)))
--             (findReprs [] alt.specType) in
--           let signatureMetas : Set Name =
--             recursive let work = lam acc. lam ty.
--               let ty = unwrapType ty in
--               match ty with TyMetaVar x then
--                 match deref x.contents with Unbound x in
--                 setInsert x.ident acc
--               else sfold_Type_Type work acc ty
--             in work (setEmpty nameCmp) alt.specType in
--           { reprs =
--             { scope = alt.reprScope
--             , syms = signatureReprs
--             }
--           , types =
--             { level = alt.metaLevel
--             , names = signatureMetas
--             }
--           } in

--         -- NOTE(vipa, 2023-08-11): Go through the opUses and filter
--         -- out alternatives that cannot be relevant for this impl
--         let f = lam idx. lam opUse.
--           let f = lam sol.
--             let solUni = unifyPure sol.uni opUse.app.ty (inst alt.info alt.metaLevel (removeReprSubsts sol.specType)) in
--             let solUni = optionAnd
--               solUni
--               (optionBind solUni (mergeUnifications uni)) in
--             optionMap
--               (lam uni. {sol with uni = uni})
--               solUni
--           in
--           let solutionSet = match opUse.solutionSet with CPSolutionSet prom in promiseForce prom in
--           { app = opUse.app
--           , solutionSet = mapOption f solutionSet
--           , idxes = setInsert idx (setEmpty subi)
--           }
--         in
--         let opUses = mapi f alt.opUses in
--         if any (lam opUse. null opUse.solutionSet) opUses then
--           -- TODO(vipa, 2023-10-10): For now we print an error/warning
--           -- when this happens, because it's likely to be unintended,
--           -- but later it might be a result of business as usual, so
--           -- that might change
--           printError (join [info2str alt.info, ": an op-use has no viable alternatives, thus this alt is dead.\n"]);
--           flushStderr ();
--           []
--         else

--         -- TODO(vipa, 2023-08-11): This is the place to insert
--         -- deduplication of opUses, by merging them and doing
--         -- `setUnion` on the `idxes` field. ReprVars that are merged
--         -- during deduplication should be unified via `uni`

--         let solutions =
--           let problem = {alt = alt, uni = uni, uniFilter = uniFilter, opUses = opUses} in
--           let size = foldl (lam acc. lam opUse. muli acc (length opUse.solutionSet)) 1 opUses in

--           -- NOTE(vipa, 2023-10-23): Always run enum, which tends to
--           -- be (much) faster, but behaves much worse in the worst
--           -- case
--           -- let startT = wallTimeMs () in
--           -- let res = solveViaEnumeration problem in
--           -- let time = subf (wallTimeMs ()) startT in
--           -- printError (join ["Alt solve complete, size, took: ", float2string time, "ms\n"]);
--           -- flushStderr ();

--           -- NOTE(vipa, 2023-10-23): Run one depending on the maximum size of the problem
--           let startT = wallTimeMs () in
--           let res = if lti size 400
--             then solveViaEnumeration problem
--             else solveViaModel problem in
--           let time = subf (wallTimeMs ()) startT in
--           printError (join ["Alt solve complete, size, took: ", float2string time, "ms\n"]);
--           flushStderr ();

--           -- NOTE(vipa, 2023-10-23): Run both, for profiling/timing information
--           -- let startT = wallTimeMs () in
--           -- let res = solveViaEnumeration problem in
--           -- let enumTime = subf (wallTimeMs ()) startT in
--           -- let startT = wallTimeMs () in
--           -- let res = solveViaModel problem in
--           -- let modelTime = subf (wallTimeMs ()) startT in
--           -- printError (join ["Alt solve complete, size: ", int2string size, ", enum took: ", float2string enumTime, "ms, model took: ", float2string modelTime, "\n"]);
--           -- flushStderr ();

--           res
--         in solutions
--       in mapi (lam idx. lam sol. {sol with idx = idx}) (join (map f alts))
--     ) in CPSolutionSet promise

--   type ReprProblem a =
--     { alt : RepTypesProblemAlt a
--     , uni : Unification
--     , uniFilter : {reprs : {scope : Int, syms : Set Symbol}, types : {level : Int, names : Set Name}}
--     , opUses : [{app: TmOpVarRec, idxes: Set Int, solutionSet: [CPSol a]}]
--     }

--   sem solveViaEnumeration : all a. ReprProblem a -> [CPSol a]
--   sem solveViaEnumeration = | problem ->
--     match problem with {alt = alt, uni = uni, uniFilter = uniFilter, opUses = opUses} in
--     printError (join ["Starting to solve exhaustively, size: ", strJoin "*" (map (lam opUse. int2string (length opUse.solutionSet)) opUses), "\n"]);
--     flushStderr ();
--     type Sol = {uni : Unification, cost : OpCost, innerSolutions : Map Int (OpImplSolution a)} in
--     let applySol : TmOpVarRec -> Set Int -> Sol -> CPSol a -> Option Sol = lam app. lam idxes. lam sol. lam new.
--       match mergeUnifications sol.uni new.uni with Some uni then Some
--         { uni = uni
--         , cost = addf sol.cost (mulf (int2float (setSize idxes)) (mulf app.scaling new.cost))
--         , innerSolutions = mapUnion sol.innerSolutions (mapMap (lam. CPSolution new) idxes)
--         }
--       else None ()
--     in
--     let sols = foldl
--       (lam acc. lam opUse. filterOption (seqLiftA2 (applySol opUse.app opUse.idxes) acc opUse.solutionSet))
--       [{uni = uni, innerSolutions = mapEmpty subi, cost = 0.0}]
--       opUses in
--     let mkCPSol = lam sol.
--       { cost = sol.cost
--       , specType = alt.specType
--       , uni = filterUnification uniFilter sol.uni
--       , innerSolutions = mapValues sol.innerSolutions
--       , idx = 0  -- NOTE(vipa, 2023-10-19): Updated later, to be unique across all alts
--       , token = alt.token
--       } in
--     let solutions = map mkCPSol sols in
--     -- TODO(vipa, 2023-10-19): Definitely want to filter out solutions
--     -- that are covered (they look the same from the outside as some
--     -- other solution, and the cost is higher)
--     (if null solutions
--      then warnSingle [alt.info] "Found no solutions for alt (exhaustive solve)."
--      else ());
--     mapi (lam i. lam sol. {sol with idx = i}) solutions

--   sem solveViaModel : all a. ReprProblem a -> [CPSol a]
--   sem solveViaModel = | problem ->
--     match problem with {alt = alt, uni = uni, uniFilter = uniFilter, opUses = opUses} in
--     printError (join ["Starting to construct model, size: ", strJoin "*" (map (lam opUse. int2string (length opUse.solutionSet)) opUses), "\n"]);
--     flushStderr ();
--     let m = newModel () in
--     let cmpSol = lam a. lam b. subi a.idx b.idx in
--     let reprTy = m.newEnumType nameCmp in
--     let getReprSymVar : Symbol -> COPExpr =
--       let reprMap : Ref (Map Symbol COPExpr) = ref (mapEmpty (lam a. lam b. subi (sym2hash a) (sym2hash b))) in
--       let newReprVar = lam sym.
--         let expr = m.var (m.newVar reprTy "repr") in
--         modref reprMap (mapInsert sym expr (deref reprMap));
--         expr in
--       lam sym. mapLookupOrElse (lam. newReprVar sym) sym (deref reprMap) in
--     let uniToPredicate = lam localUni.
--       let localReprs = localUni.reprs in
--       let reprs = uni.reprs in
--       let mkEq = lam repr.
--         let l = eitherMapRight (lam x. x.0)
--           (pufUnwrap reprs (repr, negi 1)) in
--         let r = eitherMapRight (lam x. x.0)
--           (eitherBindRight (pufUnwrap localReprs (repr, negi 1)) (pufUnwrap reprs)) in
--         if eitherEq nameEq eqsym l r then None () else
--         let toCOPExpr = eitherEither (m.enum reprTy) getReprSymVar in
--         Some (m.eq (toCOPExpr l) (toCOPExpr r)) in
--       m.andMany (mapOption mkEq (mapKeys localReprs))
--     in
--     let cost : Ref [COPExpr] = ref [m.float alt.selfCost] in
--     let addCost : COPExpr -> () = lam c. modref cost (snoc (deref cost) c) in
--     let useToVar = lam opUse.
--       let ident = opUse.app.ident in
--       let opTy = m.newEnumType cmpSol in
--       m.registerValues opTy (setOfSeq cmpSol opUse.solutionSet);
--       let var = m.newVar opTy (nameGetStr ident) in
--       -- NOTE(vipa, 2023-08-16): `uniMapToPredicate` may create
--       -- new repr-vars as a side-effect, and since elimEnum is
--       -- lazy and might run too late we pre-run it here to
--       -- ensure the reprs are created.
--       iter (lam sol. uniToPredicate sol.uni; ()) opUse.solutionSet;
--       m.newConstraint (m.elimEnum opTy (m.var var) (lam sol. uniToPredicate sol.uni));
--       addCost (m.elimEnum opTy (m.var var) (lam sol. m.float (mulf opUse.app.scaling sol.cost)));
--       (opUse.idxes, var, opTy) in
--     let vars = map useToVar opUses in
--     -- NOTE(vipa, 2023-10-10): This undoes any deduplication
--     -- done previously, using the `idxes` set.
--     let orderedVars = mapValues (foldl
--       (lam acc. lam var. mapUnion acc (mapMap (lam. var.1) var.0))
--       (mapEmpty subi)
--       vars) in
--     let cost = m.addMany (deref cost) in
--     recursive let work = lam prevSolutions.
--       if gti (length prevSolutions) 20 then
--         errorSingle [alt.info] (join ["Found a surprising number of solutions for alt (more than 20, should be reasonable later on, but in early testing it's mostly been caused by bugs). Final model:\n", m.debugModel (), "\n"])
--       else
--       switch m.minimize cost
--       case COPSolution {objective = Some (COPFloat {val = cost})} then
--         -- NOTE(vipa, 2023-10-10): The translation to a
--         -- constraint model isn't perfect: we don't model type
--         -- constraints. By merging all the Unification's we
--         -- check that the combination actually type-checks,
--         -- i.e., it's a valid solution.
--         let combinedUni = optionFoldlM
--           (lam acc. lam var. mergeUnifications acc (m.readVar var.1).uni)
--           -- NOTE(vipa, 2023-10-10): We start from an empty
--           -- unification, not `uni`, since the latter might
--           -- introduce more variables to the model, which can
--           -- make us loop forever.
--           (emptyUnification ())
--           vars in
--         let combinedUni = optionMap (filterUnification uniFilter) combinedUni in
--         match (combinedUni, optionBind combinedUni (lam x. mergeUnifications x uni))
--         with (Some localExternallyVisibleUni, Some uni) then
--           printError ".";  -- TODO(vipa, 2023-10-22): Remove
--           flushStderr ();
--           -- NOTE(vipa, 2023-08-18): Assert that any later
--           -- solution must differ from this one in some externally
--           -- visible way
--           m.newConstraint (m.not (uniToPredicate localExternallyVisibleUni));
--           let sol =
--             { cost = cost
--             , specType = alt.specType
--             , uni = uni
--             , innerSolutions = map (lam v. CPSolution (m.readVar v)) orderedVars
--             , idx = 0  -- NOTE(vipa, 2023-10-10): Updated later, to be unique across all alts
--             , token = alt.token
--             }
--           in work (snoc prevSolutions sol)
--         else
--           printError "?";  -- TODO(vipa, 2023-10-22): Remove
--           flushStderr ();
--           -- NOTE(vipa, 2023-10-10): The chosen implementations
--           -- do not type-check together. We need to rule out
--           -- this particular combination, then find another
--           -- solution.

--           -- NOTE(vipa, 2023-10-10): Most likely it's just a
--           -- *subset* of the implementations that don't mesh. As
--           -- an approximation of this set, we merge the `uni`s
--           -- of the `vars` until we fail, then assert that at
--           -- least one of the seen `vars` must differ.
--           let vars =
--             recursive let work = lam checkedVars. lam uni. lam varPairs.
--               match varPairs with [(_, var, opTy)] ++ varPairs then
--                 let checkedVars = snoc checkedVars (m.eq (m.var var) (m.enum opTy (m.readVar var))) in
--                 match mergeUnifications uni (m.readVar var).uni with Some uni
--                 then work checkedVars uni varPairs
--                 else checkedVars
--               else error "Compiler error, there should be a unification failure somewhere"
--             in work [] uni vars in
--           m.newConstraint (m.not (m.andMany vars));
--           work prevSolutions
--       case COPUnsat _ then
--         printError "!";  -- TODO(vipa, 2023-10-22): Remove
--         flushStderr ();
--         (if null prevSolutions then
--            warnSingle [alt.info] (join ["Found no solutions for alt. Final model:\n", m.debugModel (), "\n"])
--          else
--            printError (join ["solutions: ", int2string (length prevSolutions), ", info: ", info2str alt.info, "\n"]);
--            flushStderr ());
--         prevSolutions
--       case COPError x then
--         errorSingle [alt.info] (concat "CP-solver error during RepTypes solving:\n" x.msg)
--       end
--     in work []

--   sem concretizeSolution =
--   | CPSolution sol -> (sol.token, sol.innerSolutions)

--   sem cheapestSolution =
--   | CPSolutionSet promise ->
--     let forced = promiseForce promise in
--     CPSolution (minOrElse (lam. errorSingle [] "Couldn't put together a complete program, see earlier warnings about possible reasons.") (lam a. lam b. cmpfApprox 1.0 a.cost b.cost) forced)
-- end

-- lang RepTypesComposedSolver = RepTypesSolveAndReconstruct + SATishSolver + MExprUnify end
-- lang RepTypesComposedSolver = RepTypesSolveAndReconstruct + LazyTopDownSolver + MExprUnify end
-- lang RepTypesComposedSolver = RepTypesSolveAndReconstruct + MemoedTopDownSolver + MExprUnify end
-- lang RepTypesComposedSolver = RepTypesSolveAndReconstruct + EagerRepSolver + MExprUnify end

lang DumpRepTypesProblem = RepTypesFragments
  sem dumpRepTypesProblem : String -> Expr -> ()
  sem dumpRepTypesProblem path = | tm ->
    let lines = ref [] in
    dumpRepTypesProblemRoot (lam line. modref lines (snoc (deref lines) line)) 0 tm;
    writeFile path (strJoin "\n" (deref lines))

  sem dumpRepTypesProblemRoot : (String -> ()) -> Int -> Expr -> ()
  sem dumpRepTypesProblemRoot output reprScope = | tm ->
    let apps = dumpRepTypesProblemWork output [] tm in
    let reprToJson = lam repr. switch deref (botRepr repr)
      case BotRepr x then JsonArray [JsonInt x.scope, JsonInt (sym2hash x.sym)]
      case UninitRepr _ then JsonString "uninit"
      case LinkRepr _ then JsonString "link"  -- This should be impossible, but eh
      end in
    let appToLine = lam i. lam app.
      match clearAndCollectReprs [] app.1 with (reprs, ty) in
      let json = JsonObject (mapFromSeq cmpString
        [ ("opId", JsonInt i)
        , ("reprScope", JsonInt reprScope)
        , ("op", JsonString (nameGetStr app.0))
        , ("ty", JsonString (type2str ty))
        , ("reprs", JsonArray (map reprToJson reprs))
        ]) in
      output (json2string json) in
    iteri appToLine apps

  sem dumpRepTypesProblemWork : (String -> ()) -> [(Name, Type)] -> Expr -> [(Name, Type)]
  sem dumpRepTypesProblemWork output acc =
  | TmOpVar x -> snoc acc (x.ident, x.ty)
  | TmOpImpl x ->
    dumpRepTypesProblemRoot output x.reprScope x.body;
    dumpRepTypesProblemWork output acc x.inexpr
  | tm -> sfold_Expr_Expr (dumpRepTypesProblemWork output) acc tm

  sem clearAndCollectReprs : [ReprVar] -> Type -> ([ReprVar], Type)
  sem clearAndCollectReprs reprs =
  | TyRepr x ->
    let reprs = snoc reprs x.repr in
    match clearAndCollectReprs reprs x.arg with (reprs, arg) in
    (reprs, TyRepr {x with repr = ref (UninitRepr ()), arg = arg})
  | ty -> smapAccumL_Type_Type clearAndCollectReprs reprs ty
end

lang PrintMostFrequentRepr = RepTypesFragments + MExprAst
  sem findMostCommonRepr : Expr -> Option Symbol
  sem findMostCommonRepr = | tm ->
    let counts = findMostCommonRepr_ (mapEmpty _symCmp) tm in
    optionMap (lam x. x.0) (max (lam a. lam b. subi a.1 b.1) (mapBindings counts))

  sem findMostCommonRepr_ : Map Symbol Int -> Expr -> Map Symbol Int
  sem findMostCommonRepr_ acc =
  | TmOpVar x ->
    let symFromRepr = lam x. match deref (botRepr x) with BotRepr x in x.sym in
    let reprs = setOfSeq _symCmp (map symFromRepr x.reprs) in
    setFold (lam acc. lam repr. mapInsertWith addi repr 1 acc) acc reprs
  | tm -> sfold_Expr_Expr findMostCommonRepr_ acc tm

  sem printIfExprHasRepr : Symbol -> Expr -> ()
  sem printIfExprHasRepr reprSymbol =
  | TmOpDecl x -> printIfExprHasRepr reprSymbol x.inexpr
  | TmOpImpl x -> printIfExprHasRepr reprSymbol x.inexpr
  | tm ->
    -- (if hasInExpr tm
    --  then ()
    --  else printIfTypeIsRepr reprSymbol (infoTm tm) (tyTm tm));
    sfold_Expr_Type (lam. lam ty. printIfTypeHasRepr reprSymbol [infoTm tm] ty) () tm;
    sfold_Expr_Expr (lam. lam tm. printIfExprHasRepr reprSymbol tm) () tm

  sem printIfTypeIsRepr : Symbol -> [Info] -> Type -> ()
  sem printIfTypeIsRepr reprSymbol infos = | ty ->
    match unwrapType ty with TyRepr c then
      match deref (botRepr c.repr) with BotRepr x then
        if eqsym x.sym reprSymbol then
          let mkSection = lam info. {errorDefault with info = info} in
          let msg = errorMsg (map mkSection infos) {single = "", multi = ""} in
          printError (join ["\n", infoWarningString msg.0 msg.1, "\n"]);
          flushStderr ();
          ()
        else ()
      else ()
     else ()

  sem printIfTypeHasRepr : Symbol -> [Info] -> Type -> ()
  sem printIfTypeHasRepr reprSymbol infos =
  | ty & TyAlias x ->
    let infos = snoc infos (infoTy ty) in
    printIfTypeIsRepr reprSymbol infos ty;
    printIfTypeHasRepr reprSymbol infos x.display
  | ty ->
    let infos = snoc infos (infoTy ty) in
    printIfTypeIsRepr reprSymbol infos ty;
    sfold_Type_Type (lam. lam ty. printIfTypeHasRepr reprSymbol infos ty) () ty

  sem hasInExpr : Expr -> Bool
  sem hasInExpr =
  | TmLet _ | TmRecLets _ | TmExt _ | TmType _ | TmConDef _ | TmOpDecl _ | TmOpImpl _ -> true
  | _ -> false
end
