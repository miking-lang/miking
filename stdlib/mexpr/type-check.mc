-- Type check MExpr terms, annotating AST nodes with the results.
--
-- The type system is based on FreezeML [1], and gives ML-style
-- type inference along with the expressive power of System F
-- with low syntactic overhead.
--
-- The implementation uses efficient side-effecting unification,
-- as described in [2]. The current implementation corresponds to
-- the sound but eager version described.
--
-- [1]: https://dl.acm.org/doi/abs/10.1145/3385412.3386003
-- [2]: http://okmij.org/ftp/ML/generalization.html.

include "error.mc"
include "math.mc"
include "seq.mc"

include "mexpr/annotate.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/builtin.mc"
include "mexpr/cmp.mc"
include "mexpr/const-types.mc"
include "mexpr/eq.mc"
include "mexpr/info.mc"
include "mexpr/pattern-analysis.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type.mc"
include "mexpr/unify.mc"
include "mexpr/value.mc"
include "mexpr/repr-ast.mc"

type ReprSubst = use Ast in {vars : [Name], pat : Type, repr : Type}

type TCEnv = {
  -- Normal typechecking related fields
  varEnv: Map Name (use Ast in Type),
  conEnv: Map Name (Level, use Ast in Type),
  tyVarEnv: Map Name (Level, use Ast in Kind),
  tyConEnv: Map Name (Level, [Name], use Ast in Type),
  typeDeps : Map Name (Set Name), -- The set of type names recursively occuring in a type
  conDeps  : Map Name (Set Name), -- The set of constructors in scope for a type
  matches : [(Expr, Set NPat)],
  currentLvl: Level,
  disableRecordPolymorphism: Bool,

  -- Reptypes relevant fields
  reptypes : {
    delayedReprUnifications : Ref [(ReprVar, ReprVar)],
    -- Ops derived from rec-lets get wrapped in a record, in which
    -- case the value below becomes `Some (record, label)`, where
    -- `record` is the `Name` of the record (which is an op) and
    -- `label` is the label of this particular function in that
    -- record.
    opNamesInScope : Map Name (Option (Name, SID)),
    reprEnv : Map Name ReprSubst,
    nextReprScope : Ref Int,
    inImpl : Bool,
    reprScope : Int
  }
}

let typcheckEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  conEnv = mapEmpty nameCmp,
  tyVarEnv = mapEmpty nameCmp,
  tyConEnv = mapEmpty nameCmp,
  typeDeps = mapEmpty nameCmp,
  conDeps  = mapEmpty nameCmp,
  matches  = [],
  currentLvl = 0,
  disableRecordPolymorphism = true,
  reptypes = {
    delayedReprUnifications = ref [],
    opNamesInScope = mapEmpty nameCmp,
    reprEnv = mapEmpty nameCmp,
    nextReprScope = ref 1,
    inImpl = false,
    reprScope = 0
  }
}

let typecheckEnvAddBuiltinTypes : TCEnv -> [(String, [String])] -> TCEnv
  = lam env. lam tys.
    use DataTypeAst in
    { env with
      tyConEnv =
        foldl
          (lam env. lam t.
            mapInsert (nameNoSym t.0) (0, map nameSym t.1, tyvariant_ []) env)
          env.tyConEnv tys }

let typcheckEnvDefault =
  typecheckEnvAddBuiltinTypes typcheckEnvEmpty builtinTypes

-- TODO(oerikss, 2023-11-14): Change all DSLs that use this name for the
-- type-check environment to instead point to `typcheckEnvDefault` and then
-- remove this alias.
let _tcEnvEmpty = typcheckEnvDefault

let _insertVar = lam name. lam ty. lam env : TCEnv.
  {env with varEnv = mapInsert name ty env.varEnv}

lang RepTypesHelpers = Unify + ReprTypeAst + AliasTypeAst + TyWildAst + ReprSubstAst
  sem unifyReprs : Int -> Ref [(ReprVar, ReprVar)] -> ReprVar -> ReprVar -> ()
  sem unifyReprs scope delayedReprUnifications a = | b ->
    let abot = botRepr a in
    let bbot = botRepr b in
    match (deref abot, deref bbot) with (UninitRepr _, _) | (_, UninitRepr _) then () else
    match (deref abot, deref bbot) with (BotRepr a, BotRepr b) in
    if eqsym a.sym b.sym then () else
    if lti (maxi a.scope b.scope) scope then
      modref delayedReprUnifications (snoc (deref delayedReprUnifications) (abot, bbot))
    else
      if leqi a.scope b.scope
      then modref bbot (LinkRepr abot)
      else modref abot (LinkRepr bbot)

  sem newRepr : TCEnv -> ReprVar
  sem newRepr = | env ->
    ref (BotRepr {sym = gensym (), scope = env.reptypes.reprScope})

  sem withNewReprScope : all a. TCEnv -> (TCEnv -> a) -> (a, Int, [(ReprVar, ReprVar)])
  sem withNewReprScope env = | f ->
    let reprScope = deref env.reptypes.nextReprScope in
    let env =
      { env with reptypes =
        { env.reptypes with delayedReprUnifications = ref []
        , reprScope = reprScope
        }
      } in
    modref env.reptypes.nextReprScope (addi 1 reprScope);
    let res = f env in
    (res, reprScope, deref env.reptypes.delayedReprUnifications)

  sem captureDelayedReprUnifications : all a. TCEnv -> (() -> a) -> (a, [(ReprVar, ReprVar)])
  sem captureDelayedReprUnifications env = | f ->
    let prev = deref env.reptypes.delayedReprUnifications in
    modref env.reptypes.delayedReprUnifications [];
    let res = f () in
    let new = deref env.reptypes.delayedReprUnifications in
    modref env.reptypes.delayedReprUnifications prev;
    (res, new)

  sem findReprs : [ReprVar] -> Type -> [ReprVar]
  sem findReprs acc =
  | TyRepr x ->
    let acc = snoc acc x.repr in
    let acc = findReprs acc x.arg in
    acc
  | TyAlias x -> findReprs acc x.content
  | ty -> sfold_Type_Type findReprs acc ty

  sem containsRepr : Type -> Bool
  sem containsRepr =
  | TyRepr _ -> true
  | ty -> sfold_Type_Type (lam acc. lam ty. if acc then acc else containsRepr ty) false ty

  sem removeReprSubsts : Type -> Type
  sem removeReprSubsts =
  | TySubst x -> removeReprSubsts x.arg
  | ty -> smap_Type_Type removeReprSubsts ty
end

----------------------
-- TYPE UNIFICATION --
----------------------

lang TCUnify = Unify + AliasTypeAst + PrettyPrint + Cmp + RepTypesHelpers
  -- Unify the types `ty1' and `ty2', where
  -- `ty1' is the expected type of an expression, and
  -- `ty2' is the inferred type of the expression.
  -- Modifies the types in place.
  sem unify (tcenv : TCEnv) (info : [Info]) (ty1 : Type) =
  | ty2 ->
    recursive let u : () -> Unifier () = lam.
      { empty = (),
        combine = lam. lam. (),
        unify = lam env. lam ty1. lam ty2. unifyMeta (u ()) tcenv info env (ty1, ty2),
        unifyRepr = lam env. lam l. lam r. unifyReprs tcenv.reptypes.reprScope tcenv.reptypes.delayedReprUnifications l r,
        err = lam err. unificationError [err] info ty1 ty2
      } in
    let env : UnifyEnv = {
      boundNames = biEmpty,
      wrappedLhs = ty1,
      wrappedRhs = ty2
    } in
    unifyTypes (u ()) env (ty1, ty2)

  -- unifyMeta unifies a metavariable with a given type, in a side-effecting way.
  sem unifyMeta : Unifier () -> TCEnv -> [Info] -> UnifyEnv -> (Type, Type) -> ()
  sem unifyMeta u tcenv info env =
  | _ -> error "Left hand side of unifyMeta input not a TyMetaVar!"

  -- unifyCheck is called before a variable `tv' is unified with another type.
  -- Performs multiple tasks in one traversal:
  -- - Occurs check
  -- - Update level fields of MetaVars
  -- - If `tv' is monomorphic, ensure it is not unified with a polymorphic type
  -- - If `tv' is unified with a free type variable, ensure no capture occurs
  sem unifyCheck : TCEnv -> [Info] -> MetaVarRec -> Type -> ()
  sem unifyCheck env info tv =
  | ty -> unifyCheckType env info (setEmpty nameCmp) tv ty

  sem unifyCheckType : TCEnv -> [Info] -> Set Name -> MetaVarRec -> Type -> ()
  sem unifyCheckType env info boundVars tv =
  | ty -> unifyCheckBase env info boundVars tv (unwrapType ty)

  sem unifyCheckBase : TCEnv -> [Info] -> Set Name -> MetaVarRec -> Type -> ()
  sem unifyCheckBase env info boundVars tv =
  | ty ->
    sfold_Type_Type (lam. lam ty. unifyCheckType env info boundVars tv ty) () ty

  sem unifyCheckKind : TCEnv -> [Info] -> Set Name -> MetaVarRec -> Kind -> ()
  sem unifyCheckKind env info boundVars tv =
  | ki ->
    sfold_Kind_Type (lam. lam ty. unifyCheckType env info boundVars tv ty) () ki

  sem pprintUnifyError : PprintEnv -> UnifyError -> (PprintEnv, String)
  sem pprintUnifyError env =
  | Types (l, r) ->
    match getTypeStringCode 0 env l with (env, l) in
    match getTypeStringCode 0 env r with (env, r) in
    (env, join ["types ", l, " != ", r])
  | Rows _ -> (env, "row inequality (pprint todo)")
  | Kinds _ -> (env, "kind inequality (pprint todo)")

  sem unificationError : [UnifyError] -> [Info] -> Type -> Type -> ()
  sem unificationError errors info expectedType =
  | foundType ->
    let pprintEnv = pprintEnvEmpty in
    match getTypeStringCode 0 pprintEnv expectedType with (pprintEnv, expected) in
    match getTypeStringCode 0 pprintEnv foundType with (pprintEnv, found) in
    recursive
      let collectAliasesAndKinds
        :  {aliases : Map Type Type, kinds : Map Name Kind}
        -> Type
        -> {aliases : Map Type Type, kinds : Map Name Kind}
        = lam acc. lam ty.
        switch ty
        case TyAlias x then
          let acc = {acc with aliases = mapInsert x.display x.content acc.aliases} in
          collectAliasesAndKinds (collectAliasesAndKinds acc x.display) x.content
        case TyMetaVar x then
          switch deref x.contents
          case Unbound u then
            let acc = {acc with kinds = mapInsert u.ident u.kind acc.kinds} in
            sfold_Kind_Type collectAliasesAndKinds acc u.kind
          case Link ty then
            collectAliasesAndKinds acc ty
          end
        case _ then sfold_Type_Type collectAliasesAndKinds acc ty
        end
    in
    let res =
      collectAliasesAndKinds
        { aliases = mapEmpty cmpType
        , kinds = mapEmpty nameCmp } expectedType in
    let res = collectAliasesAndKinds res foundType in
    match
      if mapIsEmpty res.kinds then (pprintEnv, "") else
        let f = lam env. lam pair.
          match pprintVarName env pair.0 with (env, l) in
          match getKindStringCode 0 env pair.1 with (env, r) in
          (env, join ["\n*   _", l, " :: ", r]) in
        match mapAccumL f pprintEnv (mapBindings res.kinds) with (pprintEnv, kinds) in
        (pprintEnv, join [join kinds, "\n"])
    with (pprintEnv, kinds) in
    match
      if mapIsEmpty res.aliases then (pprintEnv, "") else
        let f = lam env. lam pair.
          match getTypeStringCode 0 env pair.0 with (env, l) in
          match getTypeStringCode 0 env pair.1 with (env, r) in
          (env, join ["\n*   ", l, " = ", r]) in
        match mapAccumL f pprintEnv (mapBindings res.aliases) with (pprintEnv, aliases) in
        (pprintEnv, join [join aliases, "\n"])
    with (pprintEnv, aliases) in
    match mapAccumL pprintUnifyError pprintEnv errors with (pprintEnv, errors) in
    let msg = join [
      "* Expected an expression of type: ",
      expected, "\n",
      "*    Found an expression of type: ",
      found, "\n",
      if and (null kinds) (null aliases) then "" else "* where",
      kinds,
      aliases,
      "* (errors: ", strJoin ", " errors, ")\n",
      "* When type checking the expression\n"
    ] in
    errorSingle info msg
end

lang VarTypeTCUnify = TCUnify + VarTypeAst
  sem unifyCheckBase env info boundVars tv =
  | TyVar t ->
    if not (setMem t.ident boundVars) then
      if optionMapOr true (lam x. lti tv.level x.0) (mapLookup t.ident env.tyVarEnv) then
        let msg = join [
          "* Encountered a type variable escaping its scope: ",
          nameGetStr t.ident, "\n",
          "* Perhaps the annotation of the associated let-binding is too general?\n",
          "* When type checking the expression\n"
        ] in
        errorSingle info msg
      else ()
    else ()
end

lang DataTypeTCUnify = TCUnify + DataTypeAst
  sem unifyCheckData
    :  Map Name (Level, Type)
    -> Map Name (Level, [Name], Type)
    -> [Info]
    -> MetaVarRec
    -> Map Name (Set Name)
    -> ()
  sem unifyCheckData conEnv tyConEnv info tv =
  | data ->
    let mkMsg = lam sort. lam n. join [
      "* Encountered a ", sort, " escaping its scope: ",
      nameGetStr n, "\n",
      "* When type checking the expression\n"
    ] in
    iter
      (lam tks.
      if optionMapOr true (lam r. lti tv.level r.0) (mapLookup tks.0 tyConEnv) then
        errorSingle info (mkMsg "type constructor" tks.0)
      else
        iter (lam k.
          if optionMapOr true (lam r. lti tv.level r.0) (mapLookup k conEnv) then
            errorSingle info (mkMsg "constructor" k)
          else ())
          (setToSeq tks.1))
      (mapBindings data)

  sem unifyCheckBase env info boundVars tv =
  | TyData t ->
    unifyCheckData env.conEnv env.tyConEnv info tv (computeData t)

  sem unifyCheckKind env info boundVars tv =
  | Data t ->
    unifyCheckData env.conEnv env.tyConEnv info tv t.types
end

lang MetaVarTypeTCUnify = DataTypeTCUnify + MetaVarTypeUnify + RecordTypeAst + VarTypeAst
  sem getKind : TCEnv -> Type -> Kind
  sem getKind env =
  | TyVar {ident = n} ->
    optionMapOr (Poly ()) (lam x. x.1) (mapLookup n env.tyVarEnv)
  | TyRecord r -> Record { fields = r.fields }
  | TyData r -> Data { types = computeData r }
  | _ -> Poly ()

  sem unifyMeta u tcenv info env =
  | (TyMetaVar t1 & ty1, TyMetaVar t2 & ty2) ->
    match (deref t1.contents, deref t2.contents) with (Unbound r1, Unbound r2) then
      if not (nameEq r1.ident r2.ident) then
        unifyCheck tcenv info r1 ty2;
        unifyCheck tcenv info r2 ty1;
        let updated =
          Unbound {r1 with level = mini r1.level r2.level,
                           kind  = addKinds u env (r1.kind, r2.kind)} in
        modref t1.contents updated;
        modref t2.contents (Link ty1)
      else ()
    else error "unifyMeta reached non-unwrapped MetaVar!"
  | (TyMetaVar t1 & ty1, !TyMetaVar _ & ty2) ->
    match deref t1.contents with Unbound tv then
      unifyCheck tcenv info tv ty2;
      unifyKinds u env (getKind tcenv ty2, tv.kind);
      modref t1.contents (Link env.wrappedRhs)
    else error "unifyMeta reached non-unwrapped MetaVar!"

  sem unifyCheckBase env info boundVars tv =
  | TyMetaVar t ->
    match deref t.contents with Unbound r in
    if nameEq r.ident tv.ident then
      let msg = join [
        "* Encountered a type occurring within itself.\n",
        "* Recursive types are only permitted using data constructors.\n",
        "* When type checking the expression\n"
      ] in
      errorSingle info msg
    else
      let kind =
        match (tv.kind, r.kind) with (Mono _, Poly _) then Mono ()
        else unifyCheckKind env info boundVars tv r.kind; r.kind
      in
      let updated = Unbound {r with level = mini r.level tv.level,
                                    kind  = kind} in
      modref t.contents updated
end

lang AllTypeTCUnify = TCUnify + AllTypeAst
  sem unifyCheckBase env info boundVars tv =
  | TyAll t ->
    match tv.kind with Mono _ then
      let msg = join [
        "* Encountered a monomorphic type used in a polymorphic position.\n",
        "* Perhaps you encountered the value restriction, or need a type annotation?\n",
        "* When type checking the expression\n"
      ] in
      errorSingle info msg
    else
      unifyCheckKind env info boundVars tv t.kind;
      unifyCheckType env info (setInsert t.ident boundVars) tv t.ty
end

lang ConTypeTCUnify = TCUnify + ConTypeAst
  sem unifyCheckBase env info boundVars tv =
  | TyCon t ->
    if optionMapOr true (lam r. lti tv.level r.0) (mapLookup t.ident env.tyConEnv) then
      let msg = join [
        "* Encountered a type constructor escaping its scope: ",
        nameGetStr t.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle info msg
    else
      unifyCheckType env info boundVars tv t.data
end

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

lang Generalize = AllTypeAst + VarTypeSubstitute + MetaVarTypeAst
  -- Instantiate the top-level type variables of `ty' with fresh unification variables.
  sem inst : Info -> Level -> Type -> Type
  sem inst (info : Info) (lvl : Level) = | ty ->
    (instAndSubst info lvl ty).0

  sem instAndSubst : Info -> Level -> Type -> (Type, Map Name Type)
  sem instAndSubst info lvl = | ty ->
    switch stripTyAll ty
    case ([], _) then (tyWithInfo info ty, mapEmpty nameCmp)
    case (vars, stripped) then
      let inserter = lam subst. lam v : (Name, Kind).
        let kind = smap_Kind_Type (substituteVars info subst) v.1 in
        mapInsert v.0 (newnmetavar (nameGetStr v.0) kind lvl info) subst
      in
      let subst = foldl inserter (mapEmpty nameCmp) vars in
      (tyWithInfo info (substituteVars info subst stripped), subst)
    end


  -- Generalize the unification variables in `ty' introduced at least at level `lvl`.
  -- Return the generalized type and the sequence of variables quantified.
  -- Any rigid variable in the map `vs' encountered will also be quantified over.
  sem gen (lvl : Level) (vs : Map Name Kind) =
  | ty ->
    let vars = distinct (lam x. lam y. nameEq x.0 y.0)
                 (genBase lvl vs (setEmpty nameCmp) ty) in
    let iteratee = lam v. lam ty1.
      let kind = match v.1 with Mono _ then Poly () else v.1 in
      TyAll {info = infoTy ty, ident = v.0, ty = ty1, kind = kind}
    in
    (foldr iteratee ty vars, vars)

  sem genBase (lvl : Level) (vs : Map Name Kind) (bound : Set Name) =
  | ty ->
    sfold_Type_Type (lam vars. lam ty.
      concat vars (genBase lvl vs bound ty)) [] ty
end

lang MetaVarTypeGeneralize = Generalize + MetaVarTypeAst + VarTypeAst
  sem genBase (lvl : Level) (vs : Map Name Kind) (bound : Set Name) =
  | TyMetaVar t ->
    switch deref t.contents
    case Unbound {ident = n, level = k, kind = s} then
      if lti lvl k then
        -- Var is free, generalize
        let f = lam vars. lam ty.
          concat vars (genBase lvl vs bound ty) in
        let vars = sfold_Kind_Type f [] s in
        modref t.contents (Link (TyVar {info = t.info, ident = n}));
        snoc vars (n, s)
      else
        -- Var is bound in previous let, don't generalize
        []
    case Link ty then
      genBase lvl vs bound ty
    end
end

lang VarTypeGeneralize = Generalize + VarTypeAst
  sem genBase (lvl : Level) (vs : Map Name Kind) (bound : Set Name) =
  | TyVar t ->
    match mapLookup t.ident vs with Some kind then
      if not (setMem t.ident bound) then [(t.ident, kind)]
      else []
    else []
end

lang AllTypeGeneralize = Generalize + AllTypeAst
  sem genBase (lvl : Level) (vs : Map Name Kind) (bound : Set Name) =
  | TyAll t -> genBase lvl vs (setInsert t.ident bound) t.ty
end

lang WildToMeta = AliasTypeAst + TyWildAst
  sem wildToMeta lvl =
  | TyWild x -> newvar lvl x.info
  | TyAlias x -> TyAlias {x with content = wildToMeta lvl x.content}
  | ty -> smap_Type_Type (wildToMeta lvl) ty
end

-- The default cases handle all other constructors!

-------------------------
-- TYPE CHECKING UTILS --
-------------------------

lang MetaVarDisableGeneralize = MetaVarTypeAst
  sem weakenMetaVars (lvl : Level) =
  | TyMetaVar t & ty ->
    switch deref t.contents
    case Unbound r then
      sfold_Kind_Type (lam. lam ty. weakenMetaVars lvl ty) () r.kind;
      let kind = match r.kind with Poly _ then Mono () else r.kind in
      modref t.contents (Unbound {r with level = mini lvl r.level, kind = kind})
    case Link tyL then
      weakenMetaVars lvl tyL
    end
  | ty ->
    sfold_Type_Type (lam. lam ty. weakenMetaVars lvl ty) () ty

  sem disableRecordGeneralize (lvl : Level) =
  | TyMetaVar t & ty ->
    switch deref t.contents
    case Unbound {kind = Record _} then
      weakenMetaVars lvl ty
    case Unbound _ then ()
    case Link tyL then
      disableRecordGeneralize lvl tyL
    end
  | ty ->
    sfold_Type_Type (lam. lam ty. disableRecordGeneralize lvl ty) () ty
end

let _computeUniverse : TCEnv -> Name -> Map Name (Set Name) =
  lam env. lam ident.
    mapMapWithKey (lam s. lam.
      mapLookupOrElse (lam. setEmpty nameCmp) s env.conDeps)
      (mapLookupOrElse (lam. setEmpty nameCmp) ident env.typeDeps)

-- resolveType resolves type aliases and checks that they are fully applied.
-- NOTE(aathn, 2023-05-10): In the future, this should be replaced
-- with something which also performs a proper kind check.
lang ResolveType = ConTypeAst + AppTypeAst + AliasTypeAst + VariantTypeAst +
  UnknownTypeAst + DataTypeAst + FunTypeAst + VarTypeSubstitute + AppTypeGetArgs
  sem resolveType : Info -> TCEnv -> Bool -> Type -> Type
  sem resolveType info env closeDatas =
  | (TyCon _ | TyApp _) & ty ->
    match getTypeArgs ty with (constr, args) in
    let args = map (resolveType info env closeDatas) args in
    match constr with (TyCon t) & conTy then
      match mapLookup t.ident env.tyConEnv with Some (_, params, def) then
        match def with !TyVariant _ then  -- It's an alias
          match (length params, length args) with (paramLen, argLen) in
          if eqi paramLen argLen then
            let subst = foldl2 (lam s. lam v. lam t. mapInsert v t s)
                          (mapEmpty nameCmp) params args
            in
            -- We assume def has already been resolved before being put into tycons
            TyAlias {display = mkTypeApp conTy args, content = substituteVars (infoTy ty) subst def}
          else
            errorSingle [infoTy ty] (join [
              "* Encountered a misformed type constructor or alias.\n",
              "* Type ", nameGetStr t.ident, " is declared to have ",
              int2string paramLen, " parameters.\n",
              "* Found ", int2string argLen, " arguments.\n",
              "* When checking the annotation"
            ])
        else
          switch t.data
          case TyData d then
            let universe = _computeUniverse env t.ident in
            mkTypeApp (TyCon {t with data = TyData {d with universe = universe}}) args
          case TyUnknown _ then
            if closeDatas then
              let universe = _computeUniverse env t.ident in
              let data = TyData { info = t.info
                                , universe = universe
                                , positive = false
                                , cons = setEmpty nameCmp } in
              mkTypeApp (TyCon {t with data = data }) args
            else mkTypeApp conTy args
          case _ then
            mkTypeApp conTy args
          end
      else
        errorSingle [t.info] (join [
          "* Encountered an unknown type constructor: ", nameGetStr t.ident, "\n",
          "* When checking the annotation"
        ])
    else
      mkTypeApp (resolveType info env closeDatas constr) args

  | TyAll t ->
    let ty = resolveType info env closeDatas t.ty in
    match t.kind with Data d then
      let cons = mapLookupOrElse (lam. setEmpty nameCmp) (nameNoSym "") d.types in
      let types =
        setFold (lam m. lam k.
          match mapLookup k env.conEnv with Some (_, ty) then
            match stripTyAll ty with (_, TyArrow {to = to}) then
              match getTypeArgs to with (TyCon t, _) then
                mapInsertWith setUnion t.ident (setOfSeq nameCmp [k]) m
              else error "Shouldn't happen!"
            else error "Shouldn't happen!"
          else error "Shouldn't happen!")
          (mapEmpty nameCmp)
          cons
      in
      TyAll {t with ty = ty, kind = Data {types = types}}
    else
      TyAll {t with ty = ty}

  -- If we encounter a TyAlias, it means that the type was already processed by
  -- a previous call to typeCheck.
  | TyAlias t -> TyAlias t

  | ty ->
    smap_Type_Type (resolveType info env closeDatas) ty
end

lang SubstituteUnknown = UnknownTypeAst + AliasTypeAst
  sem substituteUnknown (kind : Kind) (lvl : Level) (info : Info) =
  | TyUnknown _ ->
    newmetavar kind lvl info
  | TyAlias t ->
    TyAlias {t with content = substituteUnknown kind lvl info t.content}
  | ty ->
    smap_Type_Type (substituteUnknown kind lvl info) ty
end

lang SubstituteNewReprs = ReprTypeAst + RepTypesHelpers
  sem substituteNewReprs env =
  | TyRepr x -> TyRepr
    { x with repr = newRepr env
    , arg = substituteNewReprs env x.arg
    }
  | ty -> smap_Type_Type (substituteNewReprs env) ty
end

lang RemoveMetaVar = MetaVarTypeAst + UnknownTypeAst + RecordTypeAst
  sem removeMetaVarType =
  | TyMetaVar t ->
    switch deref t.contents
    case Unbound {kind = Record x} then
      TyRecord {info = t.info, fields = mapMap removeMetaVarType x.fields}
    case Unbound _ then TyUnknown { info = t.info }
    case Link ty then removeMetaVarType ty
    end
  | ty ->
    smap_Type_Type removeMetaVarType ty

  sem removeMetaVarExpr =
  | tm ->
    let tm = smap_Expr_TypeLabel removeMetaVarType tm in
    let tm = smap_Expr_Type removeMetaVarType tm in
    let tm = smap_Expr_Pat removeMetaVarPat tm in
    smap_Expr_Expr removeMetaVarExpr tm

  sem removeMetaVarPat =
  | pat ->
    let pat = withTypePat (removeMetaVarType (tyPat pat)) pat in
    smap_Pat_Pat removeMetaVarPat pat
end

-------------------
-- TYPE CHECKING --
-------------------

lang TypeCheck = TCUnify + Generalize + RemoveMetaVar
  -- Type check 'tm', with FreezeML-style type inference. Returns the
  -- term annotated with its type. The resulting type contains no
  -- unification variables or links.
  -- IMPORTANT: Assumes that aliases in 'tm' have been replaced with TyAlias
  -- nodes (this is done in the symbolization step).
  sem typeCheck : Expr -> Expr
  sem typeCheck =
  | tm ->
    removeMetaVarExpr (typeCheckLeaveMeta tm)

  sem typeCheckLeaveMeta : Expr -> Expr
  sem typeCheckLeaveMeta =
  | tm -> typeCheckExpr typcheckEnvDefault tm

  -- Type check `expr' under the type environment `env'. The resulting
  -- type may contain unification variables and links.
  sem typeCheckExpr : TCEnv -> Expr -> Expr
  sem typeCheckExpr env =
  | tm ->
    dprint tm; print "\n"; error ""
end

lang PatTypeCheck = TCUnify + NormPatMatch + ConNormPat
  + ConTypeAst + DataTypeAst + AppTypeGetArgs + Generalize
  -- `typeCheckPat env patEnv pat' type checks `pat' under environment `env'
  -- supposing the variables in `patEnv' have been bound previously in the
  -- pattern.  Returns an updated `patEnv' and the type checked `pat'.
  sem typeCheckPat : TCEnv -> Map Name Type -> Pat -> (Map Name Type, Pat)

  -- Type check a pattern whose subpatterns must all be of the same type as the
  -- pattern itself.
  sem typeCheckPatSimple : TCEnv -> Map Name Type -> Pat -> (Map Name Type, Pat)
  sem typeCheckPatSimple env patEnv =
  | pat ->
    let patTy = newpolyvar env.currentLvl (infoPat pat) in
    match smapAccumL_Pat_Pat
      (lam patEnv. lam pat.
        match typeCheckPat env patEnv pat with (patEnv, pat) in
        unify env [infoPat pat] patTy (tyPat pat);
        (patEnv, pat))
      patEnv pat
    with (patEnv, pat) in
    (patEnv, withTypePat patTy pat)

  -- Perform an exhaustiveness check for the given pattern and type.
  sem normpatHasMatches : TCEnv -> (Type, NormPat) -> Bool
  sem normpatHasMatches env =
  | (ty, np) ->
    any (lam p. npatHasMatches env (ty, p)) (setToSeq np)

  sem npatHasMatches : TCEnv -> (Type, NPat) -> Bool
  sem npatHasMatches env =
  | (ty, SNPat p) -> snpatHasMatches env (unwrapType ty, p)
  | (ty, NPatNot cons) ->
    match getTypeArgs ty with (TyCon t, _) then
      match unwrapType t.data with TyData d then
        match mapLookup t.ident (computeData d) with Some ks in
        any (lam k. not (setMem (ConCon k) cons)) (setToSeq ks)
      else true
    else true

  sem snpatHasMatches : TCEnv -> (Type, SNPat) -> Bool
  sem snpatHasMatches env =
  | _ -> true

  sem matchesPossible : TCEnv -> Option (Map Name NormPat)
  sem matchesPossible =
  | env ->
    let matchedVariables : [Map Name NormPat] =
      (map
         (foldl (mapUnionWith normpatIntersect) (mapEmpty nameCmp))
         (seqMapM setToSeq
            (map matchNormpat env.matches)))
    in
    recursive
      let closeType : Bool -> Type -> Type = lam inferFull. lam ty.
        match getTypeArgs ty with (TyCon t, args) then
          match unwrapType t.data with TyMetaVar r then
            match deref r.contents with Unbound u then
              let universe = _computeUniverse env t.ident in
              let u1 =
                if inferFull then universe
                else mapRemove t.ident universe in
              let u2 =
                match u.kind with Data d then d.types
                else mapEmpty nameCmp in
              let data =
                TyData { info = t.info
                       , universe = mapUnionWith setUnion u1 u2
                       , positive = false
                       , cons = setEmpty nameCmp }
              in
              mkTypeApp (TyCon {t with data = data}) (map (closeType inferFull) args)
            else error "Unwrapped type was not unwrapped!"
          else smap_Type_Type (closeType inferFull) ty
        else smap_Type_Type (closeType inferFull) ty
    in
    find
      (lam m.
      let inferFull = gti (mapSize m) 1 in
      mapAllWithKey
        (lam n. lam p.
        match mapLookup n env.varEnv with Some ty then
          let ty = inst (infoTy ty) env.currentLvl ty in
          let closed = closeType inferFull ty in
          if normpatHasMatches env (closed, p) then true
          else unify env [] closed ty; false
        else
          error "Should not happen!") m)
      matchedVariables
end

lang VarTypeCheck = TypeCheck + VarAst
  sem typeCheckExpr env =
  | TmVar t ->
    match mapLookup t.ident env.varEnv with Some ty then
      let ty =
        if t.frozen then ty
        else inst t.info env.currentLvl ty
      in
      TmVar {t with ty = ty}
    else
      let msg = join [
        "* Encountered an unbound variable: ",
        nameGetStr t.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle [t.info] msg
end

lang OpVarTypeCheck = TypeCheck + OpVarAst + RepTypesHelpers + SubstituteNewReprs + NeverAst + NamedPat + RecordPat + VarAst
  sem typeCheckExpr env =
  | TmOpVar x ->
    match mapLookup x.ident env.varEnv with Some ty then
      switch mapLookup x.ident env.reptypes.opNamesInScope
      case Some (Some (rName, label)) then
        -- NOTE(vipa, 2023-06-16): "Desugar" the variable to an access
        -- of the record it was changed into
        let tmp = nameSym "tmp" in
        let newTm = TmMatch
          { target = TmOpVar {ident = rName, ty = tyunknown_, frozen = false, info = x.info, scaling = x.scaling}
          , pat = PatRecord
            { info = x.info
            , ty = tyunknown_
            , bindings = mapInsert label (PatNamed {ident = PName tmp, info = x.info, ty = tyunknown_})
              (mapEmpty cmpSID)
            }
            -- TODO(vipa, 2023-06-16): I believe this handles frozen
            -- variables correctly, but it should probably be checked
            -- more closely
          , thn = TmVar {ident = tmp, ty = tyunknown_, frozen = x.frozen, info = x.info}
          , els = TmNever {info = x.info, ty = tyunknown_}
          , ty = tyunknown_
          , info = x.info
          } in
        typeCheckExpr env newTm
      case Some _ then
        let ty = if x.frozen then ty else inst x.info env.currentLvl ty in
        let ty = substituteNewReprs env ty in
        TmOpVar {x with ty = ty}
      case None _ then
        let msg = join [
          "* Encountered scaled application of a non-operation: ",
          nameGetStr x.ident, "\n",
          "* When type checking the expression\n"
        ] in
        errorSingle [x.info] msg
      end
    else
      let msg = join [
        "* Encountered an unbound variable: ",
        nameGetStr x.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle [x.info] msg
end

lang LamTypeCheck = TypeCheck + LamAst + ResolveType + SubstituteUnknown + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmLam t ->
    let tyAnnot = resolveType t.info env false t.tyAnnot in
    let tyAnnot = substituteNewReprs env tyAnnot in
    let tyParam = substituteUnknown (Mono ()) env.currentLvl t.info tyAnnot in
    let body = typeCheckExpr (_insertVar t.ident tyParam env) t.body in
    let tyLam = ityarrow_ t.info tyParam (tyTm body) in
    TmLam {t with body = body, tyAnnot = tyAnnot, tyParam = tyParam, ty = tyLam}
end

lang AppTypeCheck = TypeCheck + AppAst
  sem typeCheckExpr env =
  | TmApp t ->
    let lhs = typeCheckExpr env t.lhs in
    let rhs = typeCheckExpr env t.rhs in
    let tyRhs = newpolyvar env.currentLvl t.info in
    let tyRes = newpolyvar env.currentLvl t.info in
    unify env [infoTm t.lhs] (ityarrow_ (infoTm lhs) tyRhs tyRes) (tyTm lhs);
    unify env [infoTm t.rhs] tyRhs (tyTm rhs);
    TmApp {t with lhs = lhs, rhs = rhs, ty = tyRes}
end

lang OpDeclTypeCheck = OpDeclAst + TypeCheck + ResolveType + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmOpDecl x ->
    let lvl = env.currentLvl in
    let tyAnnot = resolveType x.info env.tyConEnv x.tyAnnot in
    let tyAnnot = substituteNewReprs env tyAnnot in
    let env = {env with reptypes = {env.reptypes with opNamesInScope = mapInsert x.ident (None ()) env.reptypes.opNamesInScope}} in
    let inexpr = typeCheckExpr (_insertVar x.ident tyAnnot env) x.inexpr in
    TmOpDecl {x with inexpr = inexpr, ty = tyTm inexpr, tyAnnot = tyAnnot}
end

lang ReprDeclTypeCheck = ReprDeclAst + TypeCheck + ResolveType + WildToMeta
  sem typeCheckExpr env =
  | TmReprDecl x ->
    let pat = resolveType x.info env.tyConEnv x.pat in
    let repr = resolveType x.info env.tyConEnv x.repr in
    let env = {env with reptypes = {env.reptypes with reprEnv = mapInsert x.ident {vars = x.vars, pat = pat, repr = repr} env.reptypes.reprEnv}} in
    let inexpr = typeCheckExpr env x.inexpr in
    TmReprDecl {x with inexpr = inexpr, ty = tyTm inexpr, pat = pat, repr = repr}
end

lang PropagateTypeAnnot = FunTypeAst + LamAst + UnknownTypeAst
  sem propagateTyAnnot =
  | (tm, TyAll a) -> propagateTyAnnot (tm, a.ty)
  | (TmLam l, TyArrow a) ->
    let body = propagateTyAnnot (l.body, a.to) in
    let ty = optionGetOr a.from (sremoveUnknown l.tyAnnot) in
    TmLam {l with body = body, tyAnnot = ty}
  | (tm, ty) -> tm
end

lang LetTypeCheck =
  TypeCheck + LetAst + LamAst + FunTypeAst + ResolveType + SubstituteUnknown +
  IsValue + MetaVarDisableGeneralize + PropagateTypeAnnot
  sem typeCheckExpr env =
  | TmLet t ->
    let newLvl = addi 1 env.currentLvl in
    let tyAnnot = resolveType t.info env false t.tyAnnot in
    let tyBody = substituteUnknown (Poly ()) newLvl t.info tyAnnot in
    match
      if isValue (GVal ()) t.body then
        match stripTyAll tyBody with (vars, stripped) in
        let newTyVars = foldr (lam v. mapInsert v.0 (newLvl, v.1)) env.tyVarEnv vars in
        let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVars} in
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
    let inexpr = typeCheckExpr (_insertVar t.ident tyBody env) t.inexpr in
    TmLet {t with body = body,
                  tyAnnot = tyAnnot,
                  tyBody = tyBody,
                  inexpr = inexpr,
                  ty = tyTm inexpr}
end

lang ApplyReprSubsts = TypeCheck + WildToMeta + ReprSubstAst
  sem applyReprSubsts : TCEnv -> Type -> Type
  sem applyReprSubsts env =
  | TySubst s ->
    match unwrapType (applyReprSubsts env s.arg) with TyRepr r then
      match mapLookup s.subst env.reptypes.reprEnv with Some subst then
        let pat = wildToMeta env.currentLvl subst.pat in
        let repr = wildToMeta env.currentLvl subst.repr in
        let combinedFromSubst = foldr ntyall_ (tytuple_ [pat, repr]) subst.vars in
        let combinedFromSubst = inst s.info env.currentLvl combinedFromSubst in
        let replacement = newvar env.currentLvl s.info in
        let combinedFromTy = tytuple_ [r.arg, replacement] in
        unify env [infoTy subst.pat, infoTy subst.repr, s.info] combinedFromSubst combinedFromTy;
        replacement
      else
        let msg = join [
          "* Encountered an unbound repr: ",
          nameGetStr s.subst, "\n",
          "* When substituting representations in a type\n"
        ] in
        errorSingle [s.info] msg
    else
      let msg = join [
        "* Encountered a substitution applied to a non-Repr type\n",
        "* When substituting representations in a type\n"
      ] in
      errorSingle [s.info] msg
  | TyAlias x -> TyAlias {x with content = applyReprSubsts env x.content}
  | TyAll x ->
    let newEnv = {env with tyVarEnv = mapInsert x.ident env.currentLvl env.tyVarEnv} in
    TyAll { x with ty = applyReprSubsts newEnv x.ty }
  | ty -> smap_Type_Type (applyReprSubsts env) ty
end

lang OpImplTypeCheck = OpImplAst + TypeCheck + ResolveType + PropagateTypeAnnot + SubstituteNewReprs + WildToMeta + ApplyReprSubsts + SubstituteUnknown
  sem typeCheckExpr env =
  | TmOpImpl x ->
    match mapLookup x.ident env.varEnv with Some ty then
      if optionIsSome (mapLookup x.ident env.reptypes.opNamesInScope) then
        let newLvl = addi 1 env.currentLvl in
        let typeCheckBody = lam env.
          let specTypeInfo = infoTy x.specType in
          let opTypeInfo = infoTy ty in
          -- NOTE(vipa, 2023-06-30): First we want to check that
          -- `specType` is a stricter version of the original op-decl's
          -- type, modulo wildcards. We instantiate the op-decl's type,
          -- strip `specType`, and unify the two.
          let ty = inst x.info newLvl ty in
          let ty = substituteNewReprs env ty in
          let specType = resolveType (infoTy x.specType) env.tyConEnv x.specType in
          let specType = substituteUnknown (Poly ()) newLvl x.info specType in
          let specType = inst x.info newLvl specType in
          let specType = substituteNewReprs env specType in
          let specType = wildToMeta newLvl specType in
          -- NOTE(vipa, 2023-07-03): This may do some unifications from
          -- substitutions, as a side-effect, so we do it here rather
          -- than later.
          let newEnv = {env with currentLvl = newLvl} in
          let reprType = applyReprSubsts newEnv specType in
          unify newEnv [opTypeInfo, specTypeInfo] ty (removeReprSubsts specType);
          -- NOTE(vipa, 2023-06-30): Next we want to type-check the body
          -- of the impl against the strictest type signature we have
          -- available: `specType` after filling in wildcards and
          -- applying explicit repr substitutions. We get there by
          -- generalizing `reprType`, then stripping it.
          match gen env.currentLvl (mapEmpty nameCmp) reprType with (reprType, genVars) in
          match stripTyAll reprType with (vars, reprType) in
          let newTyVars = foldr (lam v. mapInsert v.0 newLvl) env.tyVarEnv vars in
          let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVars} in
          match captureDelayedReprUnifications env
            (lam. typeCheckExpr newEnv (propagateTyAnnot (x.body, reprType)))
            with (body, delayedReprUnifications) in
          unify newEnv [specTypeInfo, infoTm body] reprType (tyTm body);

          -- NOTE(vipa, 2023-08-15): Later analysis requires that
          -- `specType` references the reprs that exist in the alt-body,
          -- thus we generalize it here
          match gen env.currentLvl (mapFromSeq nameCmp genVars) specType with (specType, _) in
          {x with body = body, delayedReprUnifications = delayedReprUnifications, specType = specType} in
        match withNewReprScope env (lam env. typeCheckBody env)
          with (x, reprScope, []) in
        let inexpr = typeCheckExpr env x.inexpr in
        TmOpImpl
        { x with reprScope = reprScope
        , metaLevel = newLvl
        , inexpr = inexpr
        , ty = tyTm inexpr
        }
      else
        let msg = join
          [ "* Encountered implementation of a non-operation: "
          , nameGetStr x.ident, "\n"
          , "* When type checking the expression\n"
          ] in
        errorSingle [x.info] msg
    else
      let msg = join [
        "* Encountered an unbound variable: ",
        nameGetStr x.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle [x.info] msg
end

lang RecLetsTypeCheck = TypeCheck + RecLetsAst + LetTypeCheck + MetaVarDisableGeneralize
  sem typeCheckExpr env =
  | TmRecLets t ->
    let newLvl = addi 1 env.currentLvl in
    -- First: Generate a new environment containing the recursive bindings
    let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
      let tyAnnot = resolveType t.info env false b.tyAnnot in
      let tyBody = substituteUnknown (Poly ()) newLvl t.info tyAnnot in
      let vars = if isValue (GVal ()) b.body then (stripTyAll tyBody).0 else [] in
      let newEnv = _insertVar b.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
      ((newEnv, newTyVars), {b with tyAnnot = tyAnnot, tyBody = tyBody})
    in
    match mapAccumL recLetEnvIteratee (env, mapEmpty nameCmp) t.bindings
      with ((recLetEnv, tyVars), bindings) in
    let newTyVarEnv =
      mapFoldWithKey (lam vs. lam v. lam k. mapInsert v (newLvl, k) vs) recLetEnv.tyVarEnv tyVars in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckBinding = lam b: RecLetBinding.
      let body =
        if isValue (GVal ()) b.body then
          let newEnv = {recLetEnv with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
          match stripTyAll b.tyBody with (_, stripped) in
          let body = typeCheckExpr newEnv (propagateTyAnnot (b.body, b.tyAnnot)) in
          -- Unify the inferred type of the body with the annotated one
          unify newEnv [infoTy b.tyAnnot, infoTm body] stripped (tyTm body);
          body
        else
          let body = typeCheckExpr {recLetEnv with currentLvl = newLvl} b.body in
          unify recLetEnv [infoTy b.tyAnnot, infoTm body] b.tyBody (tyTm body);
          body
      in
      {b with body = body}
    in
    let bindings = map typeCheckBinding bindings in

    -- Third: Produce a new environment with generalized types
    let envIteratee = lam acc. lam b : RecLetBinding.
      match
        if isValue (GVal ()) b.body then
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
end

lang MatchTypeCheck = TypeCheck + PatTypeCheck + MatchAst + NormPat
  sem typeCheckExpr env =
  | TmMatch t ->
    let target = typeCheckExpr env t.target in
    match typeCheckPat env (mapEmpty nameCmp) t.pat with (patEnv, pat) in
    unify env [infoTm target, infoPat pat] (tyPat pat) (tyTm target);
    let np = patToNormpat t.pat in
    let thnEnv = {env with varEnv = mapUnion env.varEnv patEnv,
                           matches = snoc env.matches (t.target, np) } in
    let elsEnv = {env with varEnv = mapUnion env.varEnv patEnv,
                           matches = snoc env.matches
                                       (t.target, normpatComplement np)} in
    let thn = typeCheckExpr thnEnv t.thn in
    let els = typeCheckExpr elsEnv t.els in
    unify env [infoTm thn, infoTm els] (tyTm thn) (tyTm els);
    TmMatch {t with target = target
                  , thn = thn
                  , els = els
                  , ty = tyTm thn
                  , pat = pat}
end

lang ConstTypeCheck = TypeCheck + MExprConstType + ResolveType
  sem typeCheckExpr env =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    let ty = resolveType t.info env true (f (tyConst t.val)) in
    TmConst {t with ty = inst t.info env.currentLvl ty}
end

lang SeqTypeCheck = TypeCheck + SeqAst
  sem typeCheckExpr env =
  | TmSeq t ->
    let elemTy = newpolyvar env.currentLvl t.info in
    let tms = map (typeCheckExpr env) t.tms in
    iter (lam tm. unify env [infoTm tm] elemTy (tyTm tm)) tms;
    TmSeq {t with tms = tms, ty = ityseq_ t.info elemTy}
end

lang RecordTypeCheck = TypeCheck + RecordAst + RecordTypeAst
  sem typeCheckExpr env =
  | TmRecord t ->
    let bindings = mapMap (typeCheckExpr env) t.bindings in
    let bindingTypes = mapMap tyTm bindings in
    let ty = TyRecord {fields = bindingTypes, info = t.info} in
    TmRecord {t with bindings = bindings, ty = ty}
  | TmRecordUpdate t ->
    let rec = typeCheckExpr env t.rec in
    let value = typeCheckExpr env t.value in
    let fields = mapInsert t.key (tyTm value) (mapEmpty cmpSID) in
    unify env [infoTm rec] (newrecvar fields env.currentLvl (infoTm rec)) (tyTm rec);
    TmRecordUpdate {t with rec = rec, value = value, ty = tyTm rec}
end

lang TypeTypeCheck = TypeCheck + TypeAst + VariantTypeAst + ResolveType
  sem typeCheckExpr env =
  | TmType t ->
    let tyIdent = resolveType t.info env false t.tyIdent in
    -- NOTE(aathn, 2023-05-08): Aliases are treated as the underlying
    -- type and do not need to be scope checked.
    let newLvl =
      match tyIdent with !TyVariant _ then addi 1 env.currentLvl else 0 in
    let newTyConEnv = mapInsert t.ident (newLvl, t.params, tyIdent) env.tyConEnv in
    let inexpr =
      typeCheckExpr {env with currentLvl = addi 1 env.currentLvl,
                              tyConEnv = newTyConEnv} t.inexpr in
    unify env [t.info, infoTm inexpr] (newpolyvar env.currentLvl t.info) (tyTm inexpr);
    TmType {t with tyIdent = tyIdent, inexpr = inexpr, ty = tyTm inexpr}
end

lang DataTypeCheck = TypeCheck + DataAst + FunTypeAst + ResolveType + SubstituteNewReprs
  sem _makeConstructorType : Info -> Name -> Type -> (Name, Set Name, Type)
  sem _makeConstructorType info ident =
  | ty ->
    let msg = lam. join [
      "* Invalid type of constructor: ", nameGetStr ident, "\n",
      "* The constructor should have a function type, where the\n",
      "* right-hand side should refer to a constructor type.\n",
      "* When type checking the expression\n"
    ] in
    match inspectType ty with TyArrow {to = to & (TyCon _ | TyApp _)} then
      match getTypeArgs to with (TyCon target, _) then
        recursive let substituteData = lam v. lam acc. lam x.
          switch x
          case TyCon (t & {data = TyUnknown _}) then
            (setInsert t.ident acc, TyCon { t with data = v })
          case TyAlias t then
            match substituteData v acc t.content with (acc, content) in
            (acc, TyAlias { t with content = content })
          case _ then
            smapAccumL_Type_Type (substituteData v) acc x
          end
        in
        let x = nameSym "x" in
        match substituteData (TyVar {info = info, ident = x}) (setEmpty nameCmp) ty
        with (tydeps, newTy) in
        let data = Data {
          types = mapFromSeq nameCmp [ (target.ident, setOfSeq nameCmp [ ident ]) ]
        } in
        (target.ident,
         tydeps,
         TyAll { info = info
               , ident = x
               , kind = data
               , ty = newTy })
      else errorSingle [info] (msg ())
    else errorSingle [info] (msg ())

  sem typeCheckExpr env =
  | TmConDef t ->
    let tyIdent = resolveType t.info env false t.tyIdent in
    let tyIdent = substituteNewReprs env tyIdent in
    match _makeConstructorType t.info t.ident tyIdent with (target, tydeps, tyIdent) in
    let tydeps =
      mapInsert target tydeps
        (setFold (lam m. lam t. mapInsert t (setOfSeq nameCmp [target]) m)
           (mapEmpty nameCmp) tydeps) in
    let newLvl = addi 1 env.currentLvl in
    let inexpr =
      typeCheckExpr
        {env with currentLvl = newLvl,
                  conEnv = mapInsert t.ident (newLvl, tyIdent) env.conEnv,
                  typeDeps = mapUnionWith setUnion tydeps env.typeDeps,
                  conDeps  = mapInsertWith setUnion target
                               (setOfSeq nameCmp [t.ident]) env.conDeps}
        t.inexpr
    in
    unify env [t.info, infoTm inexpr] (newpolyvar env.currentLvl t.info) (tyTm inexpr);
    TmConDef {t with tyIdent = tyIdent, inexpr = inexpr, ty = tyTm inexpr}
  | TmConApp t ->
    let body = typeCheckExpr env t.body in
    match mapLookup t.ident env.conEnv with Some (_, lty) then
      match inst t.info env.currentLvl lty with TyArrow {from = from, to = to} in
      unify env [infoTm body] from (tyTm body);
      TmConApp {t with body = body, ty = to}
    else
      let msg = join [
        "* Encountered an unbound constructor: ",
        nameGetStr t.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle [t.info] msg
end

lang UtestTypeCheck = TypeCheck + UtestAst
  sem typeCheckExpr env =
  | TmUtest t ->
    let test = typeCheckExpr env t.test in
    let expected = typeCheckExpr env t.expected in
    let next = typeCheckExpr env t.next in
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
    TmUtest {t with test = test
            , expected = expected
            , next = next
            , tusing = tusing
            , tonfail = tonfail
            , ty = tyTm next}
end

lang NeverTypeCheck = TypeCheck + NeverAst + PatTypeCheck
  sem typeCheckExpr env =
  | TmNever t ->
    switch matchesPossible env
    case None () then
      TmNever {t with ty = newpolyvar env.currentLvl t.info}
    case Some m then
      let matchstr =
        if mapIsEmpty m then
          "* An expression is not exhaustively matched on.\n"
        else
          join [
            "* Variables ", strJoin ", " (map nameGetStr (mapKeys m)),
            " are not exhaustively matched on.\n",
            "* An assignment not being matched is:\n",
            mapFoldWithKey
              (lam str. lam n. lam p.
              join [ str
                   , "  ", nameGetStr n
                   , " = "
                   , (getPatStringCode 0 pprintEnvEmpty (normpatToPat p)).1
                   , "\n" ]) "" m ]
      in
      let msg = join [
        "* Encountered a live never term.\n",
        matchstr,
        "* When type checking the expression\n"
      ] in
      errorSingle [t.info] msg
    end
end

lang ExtTypeCheck = TypeCheck + ExtAst + ResolveType
  sem typeCheckExpr env =
  | TmExt t ->
    -- TODO(vipa, 2023-06-15): Error if a RepType shows up in an external definition?
    let tyIdent = resolveType t.info env true t.tyIdent in
    let env = {env with varEnv = mapInsert t.ident tyIdent env.varEnv} in
    let inexpr = typeCheckExpr env t.inexpr in
    TmExt {t with tyIdent = tyIdent, inexpr = inexpr, ty = tyTm inexpr}
end

---------------------------
-- PATTERN TYPE CHECKING --
---------------------------

lang NamedPatTypeCheck = PatTypeCheck + NamedPat
  sem typeCheckPat env patEnv =
  | PatNamed t ->
    match t.ident with PName n then
      match mapLookup n patEnv with Some ty then
        (patEnv, PatNamed {t with ty = ty})
      else
        let patTy = newpolyvar env.currentLvl t.info in
        (mapInsert n patTy patEnv, PatNamed {t with ty = patTy})
    else
      (patEnv, PatNamed {t with ty = newpolyvar env.currentLvl t.info})
end

lang SeqTotPatTypeCheck = PatTypeCheck + SeqTotPat + SeqNormPat + SeqTypeAst + SubstituteNewReprs
  sem typeCheckPat env patEnv =
  | PatSeqTot t ->
    let elemTy = newvar env.currentLvl t.info in
    match mapAccumL (typeCheckPat env) patEnv t.pats with (patEnv, pats) in
    iter (lam pat. unify env [infoPat pat] elemTy (tyPat pat)) pats;
    (patEnv, PatSeqTot {t with pats = pats, ty = ityseq_ t.info elemTy})

  sem snpatHasMatches env =
  | (TySeq { ty = ty }, NPatSeqTot pats) ->
    forAll (lam p. npatHasMatches env (ty, p)) pats
end

lang SeqEdgePatTypeCheck = PatTypeCheck + SeqEdgePat + SeqNormPat + SeqTypeAst + SubstituteNewReprs
  sem typeCheckPat env patEnv =
  | PatSeqEdge t ->
    let elemTy = newpolyvar env.currentLvl t.info in
    let seqTy = ityseq_ t.info elemTy in
    let unifyPat = lam pat. unify env [infoPat pat] elemTy (tyPat pat) in
    match mapAccumL (typeCheckPat env) patEnv t.prefix with (patEnv, prefix) in
    iter unifyPat prefix;
    match mapAccumL (typeCheckPat env) patEnv t.postfix with (patEnv, postfix) in
    iter unifyPat postfix;
    let patEnv =
      match t.middle with PName n then
        mapInsertWith
          (lam ty1. lam ty2. unify env [t.info] ty1 ty2; ty2) n seqTy patEnv
      else patEnv
    in
    (patEnv, PatSeqEdge {t with prefix = prefix, postfix = postfix, ty = seqTy})

  sem snpatHasMatches env =
  | (TySeq { ty = ty }, NPatSeqEdge { prefix = pre, postfix = post }) ->
    forAll (lam p. npatHasMatches env (ty, p)) (concat pre post)
end

lang RecordPatTypeCheck = PatTypeCheck + RecordPat + RecordNormPat + RecordTypeAst
  sem typeCheckPat env patEnv =
  | PatRecord t ->
    let typeCheckBinding = lam patEnv. lam. lam pat. typeCheckPat env patEnv pat in
    match mapMapAccum typeCheckBinding patEnv t.bindings with (patEnv, bindings) in
    let ty = newrecvar (mapMap tyPat bindings) env.currentLvl t.info in
    (patEnv, PatRecord {t with bindings = bindings, ty = ty})

  sem snpatHasMatches env =
  | (TyRecord { fields = fields }, NPatRecord pats) ->
    mapAll (lam x. x)
      (mapIntersectWith (lam ty. lam p. npatHasMatches env (ty, p))
         fields pats)
end

lang DataPatTypeCheck = PatTypeCheck + DataPat + ConNormPat + FunTypeAst + Generalize
  sem typeCheckPat env patEnv =
  | PatCon t ->
    match mapLookup t.ident env.conEnv with Some (_, ty) then
      match inst t.info env.currentLvl ty with TyArrow {from = from, to = to} in
      match typeCheckPat env patEnv t.subpat with (patEnv, subpat) in
      unify env [infoPat subpat] from (tyPat subpat);
      (patEnv, PatCon {t with subpat = subpat, ty = to})
    else
      let msg = join [
        "* Encountered an unbound constructor: ",
        nameGetStr t.ident, "\n",
        "* When type checking the pattern\n"
      ] in
      errorSingle [t.info] msg

  sem snpatHasMatches env =
  | (ty, NPatCon {ident = c, subpat = p}) ->
    match mapLookup c env.conEnv with Some (_, tycon) then
      match inst (infoTy ty) env.currentLvl tycon with TyArrow {from = from, to = to} in
      unify env [infoTy ty] ty to;
      npatHasMatches env (from, p)
    else
      error "Should not happen!"
end

lang IntPatTypeCheck = PatTypeCheck + IntPat + IntTypeAst
  sem typeCheckPat env patEnv =
  | PatInt t -> (patEnv, PatInt {t with ty = TyInt {info = t.info}})
end

lang CharPatTypeCheck = PatTypeCheck + CharPat + CharTypeAst
  sem typeCheckPat env patEnv =
  | PatChar t -> (patEnv, PatChar {t with ty = TyChar {info = t.info}})
end

lang BoolPatTypeCheck = PatTypeCheck + BoolPat + BoolTypeAst
  sem typeCheckPat env patEnv =
  | PatBool t -> (patEnv, PatBool {t with ty = TyBool {info = t.info}})
end

lang AndPatTypeCheck = PatTypeCheck + AndPat
  sem typeCheckPat env patEnv =
  | PatAnd t -> typeCheckPatSimple env patEnv (PatAnd t)
end

lang OrPatTypeCheck = PatTypeCheck + OrPat
  sem typeCheckPat env patEnv =
  | PatOr t -> typeCheckPatSimple env patEnv (PatOr t)
end

lang NotPatTypeCheck = PatTypeCheck + NotPat
  sem typeCheckPat env patEnv =
  | PatNot t -> typeCheckPatSimple env patEnv (PatNot t)
end

lang MExprTypeCheckLamLetVar = VarTypeCheck + LamTypeCheck + LetTypeCheck + RecLetsTypeCheck
end

lang MExprTypeCheckMost =
  -- Type unification
  MExprUnify + VarTypeTCUnify + MetaVarTypeTCUnify + AllTypeTCUnify + ConTypeTCUnify +
  DataTypeTCUnify +

  -- Type generalization
  MetaVarTypeGeneralize + VarTypeGeneralize + AllTypeGeneralize +

  -- Terms
  AppTypeCheck + MatchTypeCheck + ConstTypeCheck + SeqTypeCheck +
  RecordTypeCheck + TypeTypeCheck + DataTypeCheck + UtestTypeCheck +
  NeverTypeCheck + ExtTypeCheck +

  -- Patterns
  NamedPatTypeCheck + SeqTotPatTypeCheck + SeqEdgePatTypeCheck +
  RecordPatTypeCheck + DataPatTypeCheck + IntPatTypeCheck + CharPatTypeCheck +
  BoolPatTypeCheck + AndPatTypeCheck + OrPatTypeCheck + NotPatTypeCheck +

  MExprPatAnalysis +

  -- Value restriction
  MExprIsValue +

  -- Meta variable handling
  MetaVarTypeCmp + MetaVarTypeEq + MetaVarTypePrettyPrint
end

lang MExprTypeCheck = MExprTypeCheckMost + MExprTypeCheckLamLetVar
end

lang RepTypesTypeCheck = OpDeclTypeCheck + ReprDeclTypeCheck + OpVarTypeCheck + OpImplTypeCheck + RepTypesUnify
end

-- NOTE(vipa, 2022-10-07): This can't use AnnotateMExprBase because it
-- has to thread a pprint environment, which AnnotateMExprBase doesn't
-- allow.
lang TyAnnot = AnnotateSources + PrettyPrint + Ast + AliasTypeAst
  sem annotateMExpr : Expr -> Output
  sem annotateMExpr = | tm -> annotateAndReadSources (_annotateExpr pprintEnvEmpty tm).1

  sem _removeAliases : Type -> Type
  sem _removeAliases =
  | TyAlias x -> _removeAliases x.content
  | ty -> smap_Type_Type _removeAliases ty

  sem _annotateExpr : PprintEnv -> Expr -> (PprintEnv, [(Info, Annotation)])
  sem _annotateExpr env = | tm ->
    match getTypeStringCode 0 env (_removeAliases (tyTm tm)) with (env, annot) in
    let annot = escapeAnnot annot in
    let res = (env, [(infoTm tm, annot)]) in
    let helper = lam f. lam acc. lam x.
      match f acc.0 x with (env, new) in
      (env, concat acc.1 new) in
    let res = sfold_Expr_Expr (helper _annotateExpr) res tm in
    let res = sfold_Expr_Pat (helper _annotatePat) res tm in
    res

  sem _annotatePat : PprintEnv -> Pat -> (PprintEnv, [(Info, Annotation)])
  sem _annotatePat env = | pat ->
    match getTypeStringCode 0 env (_removeAliases (tyPat pat)) with (env, annot) in
    let annot = escapeAnnot annot in
    let res = (env, [(infoPat pat, annot)]) in
    let helper = lam f. lam acc. lam x.
      match f acc.0 x with (env, new) in
      (env, concat acc.1 new) in
    let res = sfold_Pat_Expr (helper _annotateExpr) res pat in
    let res = sfold_Pat_Pat (helper _annotatePat) res pat in
    res
end

lang PprintTyAnnot = PrettyPrint + Annotator + Ast + AliasTypeAst
  syn Expr = | FakeExpr {id : Int, result : Ref String, real : Expr}
  syn Type = | FakeType {id : Int, result : Ref String, real : Type}
  syn Pat  = | FakePat  {id : Int, result : Ref String, real : Pat}

  sem isAtomic =
  | FakeExpr x -> isAtomic x.real
  sem patIsAtomic =
  | FakePat x -> patIsAtomic x.real
  sem typePrecedence =
  | FakeType x -> typePrecedence x.real

  sem pprintCode indent env =
  | FakeExpr x ->
    match pprintAnnotExpr indent env x.real with (env, real) in
    modref x.result real;
    (env, cons '!' (cons '!' (int2string x.id)))
  sem getPatStringCode indent env =
  | FakePat x ->
    match pprintAnnotPat indent env x.real with (env, real) in
    modref x.result real;
    (env, cons '!' (cons '!' (int2string x.id)))
  sem getTypeStringCode indent env =
  | FakeType x ->
    match pprintAnnotType indent env x.real with (env, real) in
    modref x.result real;
    (env, cons '!' (cons '!' (int2string x.id)))

  sem subSwap
  : all a. (a -> Int -> (Ref String, a))
  -> [Ref String]
  -> a
  -> ([Ref String], a)
  sem subSwap mkPlaceholder acc = | a ->
    match mkPlaceholder a (length acc) with (newRef, fake) in
    (snoc acc newRef, fake)
  sem mkFakeExpr real = | id ->
    let r = ref "" in
    (r, FakeExpr {id = id, result = r, real = real})
  sem mkFakeType real = | id ->
    let r = ref "" in
    (r, FakeType {id = id, result = r, real = real})
  sem mkFakePat real = | id ->
    let r = ref "" in
    (r, FakePat {id = id, result = r, real = real})

  sem pprintAst : Expr -> Output
  sem pprintAst = | tm ->
    match pprintAnnotExpr 0 pprintEnvEmpty tm with (_, output) in
    finalize output

  sem pprintAnnotExpr : Int -> PprintEnv -> Expr -> (PprintEnv, Output)
  sem pprintAnnotExpr indent env =
  | orig & x ->
    let subs = [] in
    match smapAccumL_Expr_Expr (subSwap mkFakeExpr) subs x with (subs, x) in
    match smapAccumL_Expr_Type (subSwap mkFakeType) subs x with (subs, x) in
    match smapAccumL_Expr_Pat (subSwap mkFakePat) subs x with (subs, x) in
    match pprintCode indent env x with (env, x) in
    match getTypeStringCode 0 env (_removeAliases (tyTm orig)) with (env, ty) in
    (env, annotate ty (_fixOutput x subs))

  sem pprintAnnotPat : Int -> PprintEnv -> Pat -> (PprintEnv, Output)
  sem pprintAnnotPat indent env =
  | orig & x ->
    let subs = [] in
    match smapAccumL_Pat_Expr (subSwap mkFakeExpr) subs x with (subs, x) in
    match smapAccumL_Pat_Type (subSwap mkFakeType) subs x with (subs, x) in
    match smapAccumL_Pat_Pat (subSwap mkFakePat) subs x with (subs, x) in
    match getPatStringCode indent env x with (env, x) in
    match getTypeStringCode 0 env (_removeAliases (tyPat orig)) with (env, ty) in
    (env, annotate ty (_fixOutput x subs))

  sem pprintAnnotType : Int -> PprintEnv -> Type -> (PprintEnv, Output)
  sem pprintAnnotType indent env =
  | orig & x ->
    let subs = [] in
    match smapAccumL_Type_Type (subSwap mkFakeType) subs x with (subs, x) in
    match getTypeStringCode indent env x with (env, x) in
    match getTypeStringCode 0 env (_removeAliases orig) with (env, ty) in
    (env, annotate ty (_fixOutput x subs))

  sem _removeAliases : Type -> Type
  sem _removeAliases =
  | TyAlias x -> _removeAliases x.content
  | ty -> smap_Type_Type _removeAliases ty

  sem _fixOutput : String -> [Ref String] -> Output
  sem _fixOutput str = | subs ->
    recursive let splitWhile : all a. (a -> Bool) -> [a] -> ([a], [a]) = lam pred. lam seq.
      match seq with [x] ++ rest then
        if pred x then
          match splitWhile pred rest with (passing, rest) in
          (cons x passing, rest)
        else ([], seq)
      else ([], [])
    in
    recursive let work = lam acc. lam str.
      switch str
      case ['!', '!', c & ('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9')] ++ str then
        match splitWhile isDigit (cons c str) with (number, str) in
        let acc = concat acc (deref (get subs (string2int number))) in
        work acc str
      case [c] ++ str then
        work (snoc acc c) str
      case [] then
        acc
      end
    in work "" (escapeContent str)
end

lang TestLang = MExprTypeCheck + MExprEq + MExprPrettyPrint
  sem unwrapTypes =
  | ty ->
    smap_Type_Type unwrapTypes (unwrapType ty)
end

mexpr

use TestLang in

let gen_  = lam tm. bind_ (ulet_ "x" tm) (freeze_ (var_ "x")) in
let inst_ = lam tm. bind_ (ulet_ "x" tm) (var_ "x") in

let a = tyvar_ "a" in
let b = tyvar_ "b" in
let fa = newpolyvar 0 (NoInfo ()) in
let fb = newpolyvar 0 (NoInfo ()) in
let wa = newmonovar 0 (NoInfo ()) in
let wb = newmonovar 0 (NoInfo ()) in

let tychoose_ = tyall_ "a" (tyarrows_ [a, a, a]) in
let choose_ = ("choose", tychoose_) in

let idbody_ = ulam_ "y" (var_ "y") in
let tyid_ = tyall_ "a" (tyarrow_ a a) in
let id_ = ("id", tyid_) in

let idsbody_ = bind_ idbody_ (seq_ [freeze_ (var_ "id")]) in
let tyids_ = tyseq_ tyid_ in
let ids_ = ("ids", tyids_) in

let autobody_ = lam_ "x" tyid_ (app_ (var_ "x") (freeze_ (var_ "x"))) in
let tyauto_ = tyarrow_ tyid_ tyid_ in
let auto_ = ("auto", tyauto_) in

let auto1body_ = lam_ "x" tyid_ (app_ (var_ "x") (var_ "x")) in
let tyauto1_ = tyall_ "b" (tyarrows_ [tyid_, b, b]) in
let auto1_ = ("auto1", tyauto1_) in

let polybody_ = lam_ "f" tyid_ (utuple_ [app_ (var_ "f") (int_ 1), app_ (var_ "f") true_]) in
let typoly_ = tyarrow_ tyid_ (tytuple_ [tyint_, tybool_]) in
let poly_ = ("poly", typoly_) in

type TypeTest = {
  -- Name of the test case, for documentation purposes
  name : String,
  -- The term to typecheck
  tm : Expr,
  -- Its expected type
  ty : Type,
  -- Environment assigning types to functions like id, choose, et.c.
  env : [(String, Type)]
}
in

let typeOf = lam test : TypeTest.
  let bindings = map (lam p. (nameSym p.0, p.1)) test.env in
  let symEnv = mapFromSeq cmpString (map (lam p. (nameGetStr p.0, p.0)) bindings) in
  let tyEnv = mapFromSeq nameCmp bindings in
  unwrapTypes
    (tyTm
       (typeCheckExpr {typcheckEnvDefault with varEnv = tyEnv}
          (symbolizeExpr {symEnvDefault with varEnv = symEnv} test.tm)))
in

let runTest =
  lam test : TypeTest.
  -- Make sure to print the test name if the test fails.
  let eqTypeTest = lam a : Type. lam b : Type.
    if eqType a b then true
    else print (join ["\n ** Type test FAILED: ", test.name, " **"]); false
  in
  utest typeOf test with test.ty using eqTypeTest in ()
in

let tests = [

  -- Examples from the paper
  -- A : Polymorphic Instantiation
  {name = "A1",
   tm = ulam_ "x" idbody_,
   ty = tyarrows_ [wa, wb, wb],
   env = []},

  {name = "A1o",
   tm = gen_ (ulam_ "x" idbody_),
   ty = tyalls_ ["a", "b"] (tyarrows_ [a, b, b]),
   env = []},

  {name = "A2",
   tm = app_ (var_ "choose") (var_ "id"),
   ty = tyarrows_ [tyarrow_ fa fa, fa, fa],
   env = [choose_, id_]},

  {name = "A2o",
   tm = app_ (var_ "choose") (freeze_ (var_ "id")),
   ty = tyauto_,
   env = [choose_, id_]},

  {name = "A3",
   tm = appf2_ (var_ "choose") empty_ (var_ "ids"),
   ty = tyids_,
   env = [choose_, ids_]},

  {name = "A4",
   tm = auto1body_,
   ty = tyarrows_ [tyid_, fb, fb],
   env = []},

  {name = "A4o",
   tm = autobody_,
   ty = tyauto_,
   env = []},

  {name = "A5",
   tm = app_ (var_ "id") (var_ "auto"),
   ty = tyauto_,
   env = [id_, auto_]},

  {name = "A6",
   tm = app_ (var_ "id") (var_ "auto1"),
   ty = tyarrows_ [tyid_, fb, fb],
   env = [id_, auto1_]},

  {name = "A6o",
   tm = app_ (var_ "id") (freeze_ (var_ "auto1")),
   ty = tyauto1_,
   env = [id_, auto1_]},

  {name = "A7",
   tm = appf2_ (var_ "choose") (var_ "id") (var_ "auto"),
   ty = tyauto_,
   env = [choose_, id_, auto_]},

  -- We can't handle negative tests yet, since the type checker errors on failure
  -- {name = "A8",
  --  tm = appf2_ (var_ "choose") (var_ "id") (var_ "auto1"),
  --  ty = fails,
  --  env = [choose_, id_, auto1_]}

  {name = "A9*",
   tm = appf2_ (var_ "f") (app_ (var_ "choose") (freeze_ (var_ "id"))) (var_ "ids"),
   ty = tyid_,
   env = [
     choose_,
     id_,
     ids_,
     ("f", tyall_ "a" (tyarrows_ [tyarrow_ a a, tyseq_ a, a]))
   ]},

  {name = "A10*",
   tm = app_ (var_ "poly") (freeze_ (var_ "id")),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_, id_]},

  {name = "A11*",
   tm = app_ (var_ "poly") (gen_ idbody_),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_]},

  {name = "A12*",
   tm = appf2_ (var_ "id") (var_ "poly") (gen_ idbody_),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_, id_]},

  -- TODO(aathn, 2021-10-02): Add remaining tests from the paper
  -- B : Inference with Polymorphic Arguments
  -- C : Functions on Polymorphic Lists
  -- D : Application Functions
  -- E : Eta-Expansion
  -- F : FreezeML Programs

  -- Other tests
  {name = "RecLets1",
   tm = bindall_ [
     ureclets_ [
       ("x", ulam_ "n" (app_ (var_ "y") false_)),
       ("y", ulam_ "n" (app_ (var_ "x") false_))
     ],
     var_ "x"
   ],
   ty = tyarrow_ tybool_ fa,
   env = []},

  {name = "RecLets2",
   tm = bindall_ [
     ureclets_ [
       ("even", ulam_ "n"
         (if_ (eqi_ (var_ "n") (int_ 0))
           true_
           (app_ (var_ "odd") (subi_ (var_ "n") (int_ 1))))),
       ("odd", ulam_ "n"
         (if_ (eqi_ (var_ "n") (int_ 0))
           false_
           (app_ (var_ "even") (subi_ (var_ "n") (int_ 1)))))
     ],
     var_ "even"
   ],
   ty = tyarrow_ tyint_ tybool_,
   env = []},

  {name = "RecLets3",
   tm = bindall_ [
     ureclets_ [
       ("f", ulam_ "x" (var_ "x")),
       ("g", ulam_ "x" (app_ (var_ "f") (var_ "x")))
     ],
     app_ (var_ "g") (int_ 1)
   ],
   ty = tyint_,
   env = []},

  {name = "Match1",
   tm = if_ true_ (int_ 1) (int_ 0),
   ty = tyint_,
   env = []},

  {name = "Match2",
   tm = ulam_ "x"
     (match_ (var_ "x") (pvar_ "y") (addi_ (var_ "y") (int_ 1)) (int_ 0)),
   ty = tyarrow_ tyint_ tyint_,
   env = []},

  {name = "Match3",
   tm = match_
     (seq_ [str_ "a", str_ "b", str_ "c", str_ "d"])
     (pseqedge_ [pseqtot_ [pchar_ 'a']] "mid" [pseqtot_ [pchar_ 'd']])
     (var_ "mid")
     never_,
   ty = tyseq_ tystr_,
   env = []},

  {name = "Const1",
   tm = addi_ (int_ 5) (int_ 2),
   ty = tyint_,
   env = []},

  {name = "Const2",
   tm = cons_ (int_ 0) empty_,
   ty = tyseq_ tyint_,
   env = []},

  {name = "Const3",
   tm = ulam_ "x" (int_ 0),
   ty = tyarrow_ wa tyint_,
   env = []},

  {name = "Seq1",
   tm = seq_ [],
   ty = tyseq_ fa,
   env = []},

  {name = "Seq2",
   tm = seq_ [int_ 1, int_ 2],
   ty = tyseq_ tyint_,
   env = []},

  {name = "Seq3",
   tm = seq_ [seq_ [int_ 1, int_ 2],
              seq_ [int_ 3, int_ 4]],
   ty = tyseq_ (tyseq_ tyint_),
   env = []},

  {name = "Record1",
   tm = uunit_,
   ty = tyunit_,
   env = []},

  {name = "Record2",
   tm = utuple_ [int_ 0, true_],
   ty = tytuple_ [tyint_, tybool_],
   env = []},

  {name = "Record3",
   tm = urecord_ [
     ("a", int_ 0), ("b", float_ 2.718), ("c", urecord_ []),
     ("d", urecord_ [
       ("e", seq_ [int_ 1, int_ 2]),
       ("f", urecord_ [
         ("x", var_ "x"), ("y", var_ "y"), ("z", var_ "z")
       ])
     ])
   ],
   ty = tyrecord_ [
     ("a", tyint_), ("b", tyfloat_), ("c", tyunit_),
     ("d", tyrecord_ [
       ("e", tyseq_ tyint_),
       ("f", tyrecord_ [
         ("x", tyint_), ("y", tyfloat_), ("z", tybool_)
       ])
     ])
   ],
   env = [("x", tyint_), ("y", tyfloat_), ("z", tybool_)]},

  {name = "Record4",
   tm = recordupdate_ (urecord_ [
     ("a", int_ 0),
     ("b", float_ 2.718)
   ]) "a" (int_ 1),
   ty = tyrecord_ [
     ("a", tyint_),
     ("b", tyfloat_)
   ],
   env = []},

  {name = "Record5",
   tm = bind_
     (ulet_ "f"
       (ulam_ "r" (ulam_ "x" (ulam_ "y"
         (recordupdate_
           (recordupdate_
             (var_ "r") "x" (var_ "x"))
           "y" (var_ "y"))))))
     (freeze_ (var_ "f")),
   ty =
     let fields =  mapInsert (stringToSid "x") wa
                  (mapInsert (stringToSid "y") wb
                  (mapEmpty cmpSID))
     in
     let r = newrecvar fields 0 (NoInfo ()) in
     tyarrows_ [r, wa, wb, r],
   env = []},

  {name = "Con1",
   tm = bindall_ [
     type_ "Tree" [] (tyvariant_ []),
     condef_ "Branch" (tyarrow_ (tytuple_ [tycon_ "Tree", tycon_ "Tree"])
                                (tycon_ "Tree")),
     condef_ "Leaf" (tyarrow_ (tyseq_ tyint_) (tycon_ "Tree")),
     ulet_ "t" (conapp_ "Branch" (utuple_ [
       conapp_ "Leaf" (seq_ [int_ 1, int_ 2, int_ 3]),
       conapp_ "Branch" (utuple_ [
         conapp_ "Leaf" (seq_ [int_ 2]),
         conapp_ "Leaf" (seq_ [])])])),
     (match_ (var_ "t")
       (pcon_ "Branch" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]))
       (match_ (var_ "lhs")
         (pcon_ "Leaf" (pvar_ "n"))
         (var_ "n")
         never_)
       never_)
   ],
   ty = tyseq_ tyint_,
   env = []},

  {name = "Type1",
   tm = bindall_ [
     type_ "Foo" [] (tyrecord_ [("x", tyint_)]),
     ulet_ "f" (lam_ "r" (tycon_ "Foo") (recordupdate_ (var_ "r") "x" (int_ 1))),
     app_ (var_ "f") (urecord_ [("x", int_ 0)])
   ],
   ty = tyrecord_ [("x", tyint_)],
   env = []},

  {name = "Utest1",
   tm = utest_ (int_ 1) (addi_ (int_ 0) (int_ 1)) false_,
   ty = tybool_,
   env = []},

  {name = "Utest2",
   tm = utestu_ (int_ 1) true_ false_ (ulam_ "x" idbody_),
   ty = tybool_,
   env = []},

  {name = "Never1",
   tm = never_,
   ty = fa,
   env = []},

  {name = "Unknown1",
   tm = bind_
     (let_ "f" (tyarrow_ tyunknown_ tyunknown_)
       (ulam_ "x" (var_ "x")))
     (freeze_ (var_ "f")),
   ty = tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")),
   env = []},

  {name = "Unknown2",
   tm = bind_
     (let_ "f" (tyarrow_ tyint_ tyunknown_)
       (ulam_ "x" (var_ "x")))
     (freeze_ (var_ "f")),
   ty = tyarrow_ tyint_ tyint_,
   env = []}

]
in

iter runTest tests;

()

-- TODO(aathn, 2021-09-28): Proper error reporting and propagation
-- Report a "stack trace" when encountering a unification failure
