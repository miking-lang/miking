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
include "json.mc"

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
        let newTyVars = foldr (lam v. mapInsert v.0 newLvl) env.tyVarEnv vars in
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
          let newTyVars = foldr (lam v. mapInsert v.0 newLvl) env.tyVarEnv vars in
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

lang RecLetsRepTypesAnalysis = TypeCheck + RecLetsAst + MetaVarDisableGeneralize + RecordAst + OpImplAst + OpDeclAst + RepTypesHelpers + NonExpansive + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmRecLets t ->
    let typeCheckRecLets = lam env. lam t.
      let newLvl = addi 1 env.currentLvl in
      -- Build env with the recursive bindings
      let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
        let tyBody = substituteNewReprs env b.tyBody in
        let vars = if nonExpansive true b.body then (stripTyAll tyBody).0 else [] in
        let newEnv = _insertVar b.ident tyBody acc.0 in
        let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
        ((newEnv, newTyVars), {b with tyBody = tyBody}) in
      match mapAccumL recLetEnvIteratee (env, mapEmpty nameCmp) t.bindings
        with ((recLetEnv, tyVars), bindings) in
      let newTyVarEnv = mapFoldWithKey
        (lam vs. lam v. lam. mapInsert v newLvl vs)
        recLetEnv.tyVarEnv
        tyVars in

      -- Type check each body
      let typeCheckBinding = lam b: RecLetBinding.
        let body =
          if nonExpansive true b.body then
            let newEnv = {recLetEnv with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
            match stripTyAll b.tyBody with (_, stripped) in
            let body = typeCheckExpr newEnv b.body in
            -- Unify the inferred type of the body with the annotated one
            unify newEnv [infoTy b.tyAnnot, infoTm body] stripped (tyTm body);
            body
          else
            let body = typeCheckExpr {recLetEnv with currentLvl = newLvl} b.body in
            unify recLetEnv [infoTy b.tyAnnot, infoTm body] b.tyBody (tyTm body);
            body
        in {b with body = body} in
      let bindings = map typeCheckBinding bindings in

      -- Build env with generalized types
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
        ((newEnv, newTyVars), {b with tyBody = tyBody}) in
      match mapAccumL envIteratee (env, tyVars) bindings
        with ((env, _), bindings) in

      let inexpr = typeCheckExpr env t.inexpr in
      { t with bindings = bindings
             , inexpr = inexpr
             , ty = tyTm inexpr
      }
    in

    let shouldBeOp = if env.reptypes.inImpl then false else
      if forAll (lam b. nonExpansive true b.body) t.bindings
      then any (lam b. containsRepr b.tyBody) t.bindings
      else false in
    if not shouldBeOp then TmRecLets (typeCheckRecLets env t) else
    let bindingToBindingPair = lam b.
      ( stringToSid (nameGetStr b.ident)
      , TmVar
        { ident = b.ident
        , ty = tyunknown_
        , info = t.info
        , frozen = true
        }
      ) in
    let opRecord = TmRecord
      { bindings = mapFromSeq cmpSID (map bindingToBindingPair t.bindings)
      , ty = tyunknown_
      , info = t.info
      } in
    let implEnv = {env with reptypes = {env.reptypes with inImpl = true}} in
    match withNewReprScope implEnv (lam env. typeCheckRecLets env {t with inexpr = opRecord})
      with (newT, reprScope, delayedReprUnifications) in
    let recordName =
      let ident = (head newT.bindings).ident in
      nameSym (concat (nameGetStr ident) "_etc") in
    let inexpr =
      let opNamesInScope = foldl
        (lam acc. lam b. mapInsert b.ident (Some (recordName, stringToSid (nameGetStr b.ident))) acc)
        env.reptypes.opNamesInScope
        newT.bindings in
      let opNamesInScope = mapInsert recordName (None ()) opNamesInScope in
      let env = _insertVar recordName newT.ty env in
      let env = {env with reptypes = {env.reptypes with opNamesInScope = opNamesInScope}} in
      typeCheckExpr env t.inexpr in
    let ty = tyTm inexpr in
    TmOpDecl
    { info = t.info
    , ident = recordName
    , tyAnnot = newT.ty
    , ty = ty
    , inexpr = TmOpImpl
      { ident = recordName
      , implId = negi 1
      , selfCost = 1.0
      , body = TmRecLets newT
      , specType = newT.ty
      , delayedReprUnifications = delayedReprUnifications
      , inexpr = inexpr
      , ty = ty
      , reprScope = reprScope
      , metaLevel = env.currentLvl
      , info = t.info
      }
    }
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
      let newTyVars = foldr (lam v. mapInsert v.0 newLvl) newEnv.tyVarEnv vars in
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

lang RepTypesShallowSolverInterface = OpVarAst + OpImplAst + UnifyPure
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
    , reprScope : Int
    , metaLevel : Int
    , info : Info
    -- NOTE(vipa, 2023-07-06): A token used by the surrounding system
    -- to carry data required to reconstruct a solved AST.
    , token : a
    }

  type SolProps a =
    { sol : SolverSolution a
    , cost : OpCost
    , uni : Unification
    }

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
  sem debugSolution : all a. SolverGlobal a -> [SolverSolution a] -> ()

  -- NOTE(vipa, 2023-10-25): Solve the top-level, i.e., find a
  -- `SolverSolution` per previous call to `addOpUse`.
  sem topSolve : all a. Bool -> SolverGlobal a -> SolverTopQuery a -> [SolverSolution a]

  -- NOTE(vipa, 2023-07-05): The returned list should have one picked
  -- solution per element in `opUses`. The returned `ImplId` should be
  -- the greatest `ImplId` in use in this solution.
  sem concretizeSolution : all a. SolverGlobal a -> SolverSolution a -> (a, ImplId, [SolverSolution a])

  -- NOTE(vipa, 2023-10-25): An arbitrary ordering over solutions
  sem cmpSolution : all a. SolverSolution a -> SolverSolution a -> Int
end

type ReprSolverOptions =
  { debugBranchState : Bool
  , debugFinalSolution : Bool
  , debugSolveProcess : Bool
  , debugSolveTiming : Bool
  }

let defaultReprSolverOptions : ReprSolverOptions =
  { debugBranchState = false
  , debugFinalSolution = false
  , debugSolveProcess = false
  , debugSolveTiming = false
  }

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

  sem getVarsInType : {metaLevel : Int, scope : Int} -> VarMap () -> Type -> VarMap ()
  sem getVarsInType filter acc = | ty ->
    let addMeta = lam x. if geqi x.level filter.metaLevel
      then setInsert x.ident acc.metas
      else acc.metas in
    let addRepr = lam x. if geqi x.scope filter.scope
      then setInsert x.sym acc.reprs
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

lang RepTypesSolveAndReconstruct = RepTypesShallowSolverInterface + OpImplAst + VarAst + LetAst + OpDeclAst + ReprDeclAst + ReprTypeAst + UnifyPure + AliasTypeAst + PrettyPrint + ReprSubstAst + RepTypesHelpers
  -- Top interface, meant to be used outside --
  sem reprSolve : ReprSolverOptions -> Expr -> Expr
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
    let pickedSolutions = topSolve options.debugSolveProcess global state.topQuery in
    let postTopSolve = wallTimeMs () in
    (if options.debugFinalSolution then debugSolution global pickedSolutions else ());
    -- NOTE(vipa, 2023-10-25): The concretization phase *does* handle
    -- nested impls, so it shouldn't have to be updated if the
    -- collection phase is improved later on
    let initState =
      { remainingSolutions = pickedSolutions
      , requests = mapEmpty subi
      , requestsByOpAndSol = mapEmpty (lam a. lam b.
        let res = nameCmp a.0 b.0 in
        if neqi res 0 then res else
        cmpSolution a.1 b.1)
      , global = global
      } in
    let preConcretize = wallTimeMs () in
    match concretizeAlt initState tm with (state, tm) in
    let postConcretize = wallTimeMs () in
    (if options.debugSolveTiming then
      printLn (join
        [ "Collect time: ", float2string (subf postCollect preCollect), "ms\n"
        , "Top-solve time: ", float2string (subf postTopSolve postCollect), "ms\n"
        , "Concretize time: ", float2string (subf postConcretize preConcretize), "ms\n"
        ])
     else ());
    mapFoldWithKey (lam. lam id. lam deps. printLn (join ["(compiler error) Left-over dep, id: ", int2string id, ", num deps: ", int2string (length deps)])) () state.requests;
    removeReprExpr tm

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
      , reprScope = x.reprScope
      , metaLevel = x.metaLevel
      , info = x.info
      , token = x.body
      } in
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
      printLn (join [indent, nameGetStr x.impl.op, " (cost: ", float2string x.cost, ", scaling: ", float2string solWithMeta.scale, ", info: ", info2str x.impl.info, ")"]);
      -- TODO(vipa, 2023-11-28): This will print things in a strange
      -- order, and de-duped, which might not be desirable
      for_ x.subSols (lam x. work (concat indent "  ") x)
    in (iter (lam x. match x with SSContent x in work "" {idxes = setEmpty subi, scale = 1.0, sol = x}) solutions)

  sem topSolve debug global = | STQContent topTrees ->
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
        let ty = wildToMeta impl.metaLevel ty in
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
    printLn "\n# Solution cost tree:";
    recursive let work = lam indent. lam sol.
      match sol with SolContent x in
      printLn (join [indent, nameGetStr x.impl.op, " (cost: ", float2string x.cost, ", scaling: ", float2string x.scale, ", info: ", info2str x.impl.info, ")"]);
      -- TODO(vipa, 2023-11-28): This will print things in a strange
      -- order, and de-duped, which might not be desirable
      for_ x.subSols (lam x. work (concat indent "  ") x.sol)
    in (iter (lam x. match x with SSContent x in work "" x) solutions)

  sem topSolve debug global = | STQContent choices ->
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
        let ty = wildToMeta impl.metaLevel ty in
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
    printLn "\n# Solution cost tree:";
    recursive let work = lam indent. lam sol.
      match sol with SolContent x in
      printLn (join [indent, nameGetStr x.impl.op, " (cost: ", float2string x.cost, ", scaling: ", float2string x.scale, ", info: ", info2str x.impl.info, ")"]);
      -- TODO(vipa, 2023-11-28): This will print things in a strange
      -- order, and de-duped, which might not be desirable
      for_ x.subSols (lam x. work (concat indent "  ") x.sol)
    in (iter (lam x. match x with SSContent x in work "" x) solutions)

  sem addImpl global branch = | impl ->
    match branch with SBContent branch in

    let preProc = wallTimeMs () in
    let idxedOpUses = mapi (lam i. lam opUse. {idxes = setInsert i (setEmpty subi), opUse = opUse}) impl.opUses in
    let filter = {metaLevel = impl.metaLevel, scope = impl.reprScope} in
    let externalVars = getVarsInType filter varMapEmpty impl.specType in
    let countInternalVarUses = lam acc. lam idxedOpUse.
      let internal = varMapDifference (getVarsInType filter varMapEmpty idxedOpUse.opUse.ty) externalVars in
      let addOne = lam acc. lam k. mapInsertWith addi k 1 acc in
      let metas = setFold addOne acc.metas internal.metas in
      let reprs = setFold addOne acc.reprs internal.reprs in
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

  sem topSolve debug global = | STQContent opUses ->
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
      let ty = wildToMeta impl.metaLevel ty in
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

  sem topSolve debug global = | STQContent opUses ->
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
