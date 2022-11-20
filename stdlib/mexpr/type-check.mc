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

include "ast.mc"
include "ast-builder.mc"
include "builtin.mc"
include "const-types.mc"
include "eq.mc"
include "info.mc"
include "error.mc"
include "math.mc"
include "pprint.mc"
include "seq.mc"
include "mexpr/annotate.mc"

type TCEnv = {
  varEnv: Map Name Type,
  conEnv: Map Name Type,
  -- For each type constructor, keep its list of formal parameters and definition
  tyConEnv: Map Name ([Name], Type),
  currentLvl: Level,
  disableRecordPolymorphism: Bool
}

let _tcEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  conEnv = mapEmpty nameCmp,

  -- Built-in type constructors
  tyConEnv = mapFromSeq nameCmp (
    map (lam t : (String, [String]).
          (nameNoSym t.0, (map nameSym t.1, tyvariant_ [])))
        builtinTypes
  ),

  currentLvl = 1,
  disableRecordPolymorphism = true
}

let _insertVar = lam name. lam ty. lam env : TCEnv.
  {env with varEnv = mapInsert name ty env.varEnv}

let _insertCon = lam name. lam ty. lam env : TCEnv.
  {env with conEnv = mapInsert name ty env.conEnv}

let _insertTyCon = lam name. lam ty. lam env : TCEnv.
  {env with tyConEnv = mapInsert name ty env.tyConEnv}

type UnifyEnv = {
  info: [Info],  -- The info of the expression(s) triggering the unification
  originalLhs: Type,
  originalRhs: Type,
  names: BiNameMap,
  tyConEnv: Map Name ([Name], Type)
}

let unificationError =
  lam info. lam originalLhs. lam originalRhs. lam lhs. lam rhs.
  let msg = join [
    "Type check failed: unification failure\n",
    "LHS: ", lhs, "\n",
    "RHS: ", rhs, "\n",
    "while unifying these:\n",
    "LHS: ", originalLhs, "\n",
    "RHS: ", originalRhs, "\n"
  ] in
  errorSingle info msg

let _sort2str = use MExprPrettyPrint in
  lam ident. lam sort.
  match getVarSortStringCode 0 pprintEnvEmpty (nameGetStr ident) sort
  with (_, str) in str

lang VarTypeSubstitute = VarTypeAst
  sem substituteVars (subst : Map Name Type) =
  | TyVar t & ty ->
    match mapLookup t.ident subst with Some tyvar then tyvar
    else ty
  | ty ->
    smap_Type_Type (substituteVars subst) ty
end

lang AppTypeGetArgs = AppTypeAst
  sem getTypeArgs =
  | TyApp t ->
    match getTypeArgs t.lhs with (tycon, args) in
    (tycon, snoc args t.rhs)
  | ty ->
    (ty, [])
end

lang ResolveAlias = VarTypeSubstitute + AppTypeGetArgs + ConTypeAst + VariantTypeAst
  sem tryResolveAlias (env : Map Name ([Name], Type)) =
  | ty ->
    match getTypeArgs ty with (TyCon t, args) then
      match mapLookup t.ident env with Some (params, def) then
        let isAlias =
          match def with TyVariant r then not (mapIsEmpty r.constrs) else true
        in
        if isAlias then
          let subst =
            foldl2 (lam s. lam v. lam t. mapInsert v t s) (mapEmpty nameCmp) params args
          in
          let ty = substituteVars subst def in
          optionOr (tryResolveAlias env ty) (Some ty)
        else None ()
      else error (join ["Encountered unknown type constructor ",
                        t.ident.0, " in resolveAlias!"])
    else None ()

  sem resolveAlias (env : Map Name ([Name], Type)) =
  | ty -> optionGetOr ty (tryResolveAlias env ty)
end

----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = MExprAst + ResolveAlias + PrettyPrint
  -- Unify the types `ty1' and `ty2'. Modifies the types in place.
  sem unify (info : [Info]) (env : TCEnv) (ty1 : Type) =
  | ty2 ->
    let env : UnifyEnv = {names = biEmpty, tyConEnv = env.tyConEnv, info = info, originalLhs = ty1, originalRhs = ty2} in
    unifyTypes env (ty1, ty2)

  sem unifyTypes (env : UnifyEnv) =
  | (ty1, ty2) ->
    let resolve = compose (resolveAlias env.tyConEnv) resolveLink in
    unifyBase env (resolve ty1, resolve ty2)

  -- Unify the types `ty1' and `ty2' under the assumptions of `env'.
  sem unifyBase (env : UnifyEnv) =
  | (ty1, ty2) ->
    unificationError env.info (type2str env.originalLhs) (type2str env.originalRhs) (type2str ty1) (type2str ty2)

  -- unifyCheck is called before a variable `tv' is unified with another type.
  -- Performs multiple tasks in one traversal:
  -- - Occurs check
  -- - Update level fields of FlexVars
  -- - If `tv' is monomorphic, ensure it is not unified with a polymorphic type
  -- - If `tv' is unified with a free type variable, ensure no capture occurs
  sem unifyCheck : [Info] -> FlexVarRec -> Type -> ()
  sem unifyCheck info tv =
  | ty -> unifyCheckBase info (setEmpty nameCmp) tv ty

  sem unifyCheckBase : [Info] -> Set Name -> FlexVarRec -> Type -> ()
  sem unifyCheckBase info boundVars tv =
  | ty ->
    sfold_Type_Type (lam. lam ty. unifyCheckBase info boundVars tv ty) () ty

  sem _fields2str = | fields -> type2str (TyRecord {info = NoInfo (), fields = fields})
end

-- Helper language providing functions to unify fields of record-like types
lang UnifyFields = Unify + PrettyPrint
  -- Check that 'm1' is a subset of 'm2'
  sem unifyFields (env : UnifyEnv) (m1 : Map SID Type) =
  | m2 ->
    let f = lam b : (SID, Type).
      match b with (k, tyfield1) in
      match mapLookup k m2 with Some tyfield2 then
        unifyTypes env (tyfield1, tyfield2)
      else
        unificationError env.info (type2str env.originalLhs) (type2str env.originalRhs) (_fields2str m1) (_fields2str m2)
    in
    iter f (mapBindings m1)

  -- Check that 'm1' and 'm2' contain the same fields
  sem unifyFieldsStrict (env : UnifyEnv) (m1 : Map SID Type) =
  | m2 ->
    if eqi (mapSize m1) (mapSize m2) then
      unifyFields env m1 m2
    else
      unificationError env.info (type2str env.originalLhs) (type2str env.originalRhs) (_fields2str m1) (_fields2str m2)
end

lang VarTypeUnify = Unify + VarTypeAst + PrettyPrint
  sem unifyBase (env : UnifyEnv) =
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if nameEq t1.ident t2.ident then ()
    else if biMem (t1.ident, t2.ident) env.names then ()
    else unificationError env.info (type2str env.originalLhs) (type2str env.originalRhs) (type2str ty1) (type2str ty2)

  sem unifyCheckBase info boundVars tv =
  | TyVar t ->
    -- NOTE(aathn, 2022-06-09): We should also disallow unifying weak variables
    -- with type variables in the future. For now, we allow it to facilitate
    -- polymorphic type signatures containing records
    if leqi tv.level t.level then
      if not (setMem t.ident boundVars) then
        let msg = join [
          "Type check failed: unification failure\n",
          "Attempted to unify with type variable escaping its scope!\n"
        ] in
        errorSingle info msg
      else ()
    else ()
end

lang FlexTypeUnify = UnifyFields + FlexTypeAst + PrettyPrint
  sem addSorts (env : UnifyEnv) =
  | (RecordVar r1, RecordVar r2) ->
    let f = lam acc. lam b : (SID, Type).
      match b with (k, ty2) in
      match mapLookup k r1.fields with Some ty1 then
        unifyTypes env (ty1, ty2);
        acc
      else
        mapInsert k ty2 acc
    in
    let fields = foldl f r1.fields (mapBindings r2.fields) in
    RecordVar {r1 with fields = fields}
  | (RecordVar _ & rv, ! RecordVar _ & tv)
  | (! RecordVar _ & tv, RecordVar _ & rv) ->
    rv
  | (PolyVar _, PolyVar _) -> PolyVar ()
  | (s1, s2) -> MonoVar ()

  sem unifyBase (env : UnifyEnv) =
  | (TyFlex t1 & ty1, TyFlex t2 & ty2) ->
    -- NOTE(aathn, 2021-11-17): unifyBase is always called by unifyTypes, which
    -- resolves any potential links, so TyFlexes are always unbound here.
    match (deref t1.contents, deref t2.contents) with (Unbound r1, Unbound r2) in
    if not (nameEq r1.ident r2.ident) then
      unifyCheck env.info r1 ty2;
      let updated =
        Unbound {r1 with level = mini r1.level r2.level
                       , sort = addSorts env (r1.sort, r2.sort)
                       , isWeak = or r1.isWeak r2.isWeak} in
      modref t1.contents updated;
      modref t2.contents (Link ty1)
    else ()
  | (TyFlex t1 & ty1, !TyFlex _ & ty2)
  | (!TyFlex _ & ty2, TyFlex t1 & ty1) ->
    match deref t1.contents with Unbound tv in
    unifyCheck env.info tv ty2;
    (match (tv.sort, ty2) with (RecordVar r1, TyRecord r2) then
       unifyFields env r1.fields r2.fields
     else match tv.sort with RecordVar _ then
       unificationError env.info (type2str env.originalLhs) (type2str env.originalRhs) (type2str ty1) (type2str ty2)
     else ());
    modref t1.contents (Link ty2)

  sem unifyCheckBase info boundVars tv =
  | TyFlex t & ty ->
    match deref t.contents with Unbound r then
      if nameEq r.ident tv.ident then
        let msg = "Type check failed: occurs check\n" in
        errorSingle info msg
      else
        let sort =
          match (tv.sort, r.sort) with (MonoVar _, PolyVar _) then MonoVar ()
          else
            sfold_VarSort_Type
              (lam. lam ty. unifyCheckBase info boundVars tv ty) () r.sort;
            r.sort
        in
        let updated = Unbound {r with level = mini r.level tv.level
                                    , sort  = sort
                                    , isWeak = or r.isWeak tv.isWeak} in
        modref t.contents updated
    else
      unifyCheckBase info boundVars tv (resolveLink ty)
end

lang FunTypeUnify = Unify + FunTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyArrow {from = from1, to = to1}, TyArrow {from = from2, to = to2}) ->
    unifyTypes env (from1, from2);
    unifyTypes env (to1, to2)
end

lang AppTypeUnify = Unify + AppTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyApp t1, TyApp t2) ->
    unifyTypes env (t1.lhs, t2.lhs);
    unifyTypes env (t1.rhs, t2.rhs)
end

lang AllTypeUnify = UnifyFields + AllTypeAst + PrettyPrint
  sem unifyBase (env : UnifyEnv) =
  | (TyAll t1, TyAll t2) ->
    (match (t1.sort, t2.sort) with (RecordVar r1, RecordVar r2) then
       unifyFieldsStrict env r1.fields r2.fields
     else if eqi (constructorTag t1.sort) (constructorTag t2.sort) then ()
     else unificationError env.info (type2str env.originalLhs) (type2str env.originalRhs) (_sort2str t1.ident t1.sort) (_sort2str t2.ident t2.sort));
    let env = {env with names = biInsert (t1.ident, t2.ident) env.names} in
    unifyTypes env (t1.ty, t2.ty)

  sem unifyCheckBase info boundVars tv =
  | TyAll t ->
    match tv.sort with MonoVar _ then
      let msg = join [
        "Type check failed: unification failure\n",
        "Attempted to unify monomorphic type variable with polymorphic type!\n"
      ] in
      errorSingle info msg
    else
      sfold_VarSort_Type (lam. lam ty. unifyCheckBase info boundVars tv ty) () t.sort;
      unifyCheckBase info (setInsert t.ident boundVars) tv t.ty
end

lang ConTypeUnify = Unify + ConTypeAst + PrettyPrint
  sem unifyBase (env : UnifyEnv) =
  | (TyCon t1 & ty1, TyCon t2 & ty2) ->
    if nameEq t1.ident t2.ident then ()
    else unificationError env.info (type2str env.originalLhs) (type2str env.originalRhs) (type2str ty1) (type2str ty2)
end

lang BoolTypeUnify = Unify + BoolTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyBool _, TyBool _) -> ()
end

lang IntTypeUnify = Unify + IntTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyInt _, TyInt _) -> ()
end

lang FloatTypeUnify = Unify + FloatTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyFloat _, TyFloat _) -> ()
end

lang CharTypeUnify = Unify + CharTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyChar _, TyChar _) -> ()
end

lang SeqTypeUnify = Unify + SeqTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TySeq t1, TySeq t2) ->
    unifyTypes env (t1.ty, t2.ty)
end

lang TensorTypeUnify = Unify + TensorTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyTensor t1, TyTensor t2) ->
    unifyTypes env (t1.ty, t2.ty)
end

lang RecordTypeUnify = UnifyFields + RecordTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyRecord t1, TyRecord t2) ->
    unifyFieldsStrict env t1.fields t2.fields
end

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

let newflexvar =
  lam sort. lam level. lam info.
  tyFlexUnbound info (nameSym "a") level sort false

let newvarMono = use VarSortAst in
  newflexvar (MonoVar ())
let newvar = use VarSortAst in
  newflexvar (PolyVar ())
let newrecvar = use VarSortAst in
  lam fields. newflexvar (RecordVar {fields = fields})

lang Generalize = AllTypeAst + VarTypeSubstitute + ResolveAlias + FlexTypeAst
  sem stripTyAllAlias (env : Map Name ([Name], Type)) =
  | ty -> stripTyAllBaseAlias env [] (resolveLink ty)

  sem stripTyAllBaseAlias (env : Map Name ([Name], Type)) (vars : [(Name, VarSort)]) =
  | TyAll t -> stripTyAllBaseAlias env (snoc vars (t.ident, t.sort)) t.ty
  | ty ->
    match tryResolveAlias env (resolveLink ty) with Some ty
    then stripTyAllBaseAlias env vars ty
    else (vars, ty)

  -- Instantiate the top-level type variables of `ty' with fresh unification variables.
  sem inst (env : Map Name ([Name], Type)) (lvl : Level) =
  | ty ->
    match stripTyAllAlias env ty with (vars, ty) in
    if gti (length vars) 0 then
      let inserter = lam subst. lam v : (Name, VarSort).
        let sort = smap_VarSort_Type (substituteVars subst) v.1 in
        mapInsert v.0 (newflexvar sort lvl (infoTy ty)) subst
      in
      let subst = foldl inserter (mapEmpty nameCmp) vars in
      substituteVars subst ty
    else
      ty

  -- Generalize the unification variables in `ty' introduced at least at level `lvl`.
  sem gen (lvl : Level) =
  | ty ->
    match genBase lvl ty with (vars, genTy) in
    -- OPT(aathn, 2022-06-29): It might be better to use a set for `vars`
    -- to avoid having to check for duplicates here.
    let vars = distinct (lam x. lam y. nameEq x.0 y.0) vars in
    let iteratee = lam v : (Name, VarSort). lam ty.
      let sort = match v.1 with MonoVar _ then PolyVar () else v.1 in
      TyAll {info = infoTy genTy, ident = v.0, ty = ty, sort = sort}
    in
    foldr iteratee genTy vars

  sem genBase (lvl : Level) =
  | ty ->
    smapAccumL_Type_Type (lam vars1. lam ty.
      match genBase lvl ty with (vars2, ty) in
      (concat vars1 vars2, ty)
    ) [] ty
end

lang FlexTypeGeneralize = Generalize + FlexTypeAst + VarTypeAst
  sem genBase (lvl : Level) =
  | TyFlex t & ty ->
    match deref t.contents with Unbound {ident = n, level = k, sort = s, isWeak = w} then
      if and (not w) (gti k lvl) then
        -- Var is free, generalize
        let f = lam vars1. lam ty.
          match genBase lvl ty with (vars2, ty) in
          (concat vars1 vars2, ty)
        in
        match smapAccumL_VarSort_Type f [] s with (vars, sort) in
        (snoc vars (n, sort), TyVar {info = t.info, ident = n, level = lvl})
      else
        -- Var is bound in previous let, don't generalize
        ([], ty)
    else
      genBase lvl (resolveLink ty)
end

-- The default cases handle all other constructors!

-------------------
-- TYPE CHECKING --
-------------------

lang ResolveLinks = FlexTypeAst
  sem resolveLinks =
  | ty ->
    smap_Type_Type resolveLinks (resolveLink ty)

  sem resolveLinksExpr =
  | tm ->
    let tm = smap_Expr_TypeLabel resolveLinks tm in
    let tm = smap_Expr_Type resolveLinks tm in
    let tm = smap_Expr_Pat resolveLinksPat tm in
    smap_Expr_Expr resolveLinksExpr tm

  sem resolveLinksPat =
  | pat ->
    let pat = withTypePat (resolveLinks (tyPat pat)) pat in
    smap_Pat_Pat resolveLinksPat pat
end

lang SubstituteUnknown = UnknownTypeAst + VarSortAst
  sem substituteUnknown (sort : VarSort) (lvl : Level) (info : Info) =
  | TyUnknown _ ->
    newflexvar sort lvl info
  | ty ->
    smap_Type_Type (substituteUnknown sort lvl info) ty

  sem checkUnknown (info : Info) =
  | TyUnknown _ ->
    let msg = join [
      "Type check failed: encountered unexpected Unknown type.\n",
      "Unknown types are only allowed in type annotations, not in ",
      "definitions or declarations!"
    ] in
    errorSingle [info] msg
  | ty ->
    sfold_Type_Type (lam. lam ty. checkUnknown info ty) () ty
end

lang TypeCheck = Unify + Generalize + ResolveLinks
  -- Type check `tm', with FreezeML-style type inference. Returns the
  -- term annotated with its type. The resulting type contains no
  -- TyFlex links.
  sem typeCheck : Expr -> Expr
  sem typeCheck =
  | tm ->
    resolveLinksExpr (typeCheckExpr _tcEnvEmpty tm)

  -- Type check `expr' under the type environment `env'. The resulting
  -- type may contain TyFlex links.
  sem typeCheckExpr : TCEnv -> Expr -> Expr
end

lang PatTypeCheck = Unify
  -- `typeCheckPat env patEnv pat' type checks `pat' under environment `env'
  -- supposing the variables in `patEnv' have been bound previously in the
  -- pattern.  Returns an updated `patEnv' and the type checked `pat'.
  sem typeCheckPat : TCEnv -> Map Name Type -> Pat -> (Map Name Type, Pat)

  -- Type check a pattern whose subpatterns must all be of the same type as the
  -- pattern itself.
  sem typeCheckPatSimple : TCEnv -> Map Name Type -> Pat -> (Map Name Type, Pat)
  sem typeCheckPatSimple env patEnv =
  | pat ->
    let patTy = newvar env.currentLvl (infoPat pat) in
    match smapAccumL_Pat_Pat
      (lam patEnv. lam pat.
        match typeCheckPat env patEnv pat with (patEnv, pat) in
        unify [infoPat pat] env patTy (tyPat pat);
        (patEnv, pat))
      patEnv pat
    with (patEnv, pat) in
    (patEnv, withTypePat patTy pat)
end

lang VarTypeCheck = TypeCheck + VarAst
  sem typeCheckExpr env =
  | TmVar t ->
    match mapLookup t.ident env.varEnv with Some ty then
      let ty =
        if t.frozen then ty
        else inst env.tyConEnv env.currentLvl ty
      in
      TmVar {t with ty = ty}
    else
      let msg = join [
        "Type check failed: reference to unbound variable: ",
        nameGetStr t.ident, "\n"
      ] in
      errorSingle [t.info] msg
end

lang LamTypeCheck = TypeCheck + LamAst + SubstituteUnknown
  sem typeCheckExpr env =
  | TmLam t ->
    -- If there is a programmer annotation, use it; otherwise, use the tyIdent field,
    -- in which there may be a propagated type from an earlier annotation.
    let tyAnnot = optionGetOr t.tyIdent (sremoveUnknown t.tyAnnot) in
    let tyIdent = substituteUnknown (MonoVar ()) env.currentLvl t.info tyAnnot in
    let body = typeCheckExpr (_insertVar t.ident tyIdent env) t.body in
    let tyLam = ityarrow_ t.info tyIdent (tyTm body) in
    TmLam {t with body = body, tyIdent = tyIdent, ty = tyLam}
end

lang AppTypeCheck = TypeCheck + AppAst
  sem typeCheckExpr env =
  | TmApp t ->
    let lhs = typeCheckExpr env t.lhs in
    let rhs = typeCheckExpr env t.rhs in
    let tyRes = newvar env.currentLvl t.info in
    unify [infoTm t.lhs] env (tyTm lhs) (ityarrow_ (infoTm lhs) (tyTm rhs) tyRes);
    TmApp {t with lhs = lhs, rhs = rhs, ty = tyRes}
end

lang LetTypeCheck = TypeCheck + LetAst + SubstituteUnknown
  sem typeCheckExpr env =
  | TmLet t ->
    let lvl = env.currentLvl in
    let body = optionMapOr t.body
      (lam ty. propagateTyAnnot (t.body, ty)) (sremoveUnknown t.tyAnnot) in
    let body = typeCheckExpr {env with currentLvl = addi 1 lvl} body in
    let tyBody = substituteUnknown (PolyVar ()) (addi 1 lvl) t.info t.tyAnnot in
    match stripTyAll (resolveAlias env.tyConEnv tyBody) with (_, tyStripped) in
    -- Unify the annotated type with the inferred one and generalize
    unify [infoTy t.tyAnnot, infoTm body] env tyStripped (tyTm body);
    let tyBody = gen lvl tyBody in
    let inexpr = typeCheckExpr (_insertVar t.ident tyBody env) t.inexpr in
    TmLet {t with body = body
                , tyBody = tyBody
                , inexpr = inexpr
                , ty = tyTm inexpr}

  sem propagateTyAnnot =
  | (tm, TyAll a) -> propagateTyAnnot (tm, a.ty)
  | (TmLam l, TyArrow a) ->
    let body = propagateTyAnnot (l.body, a.to) in
    let ty = optionGetOr a.from (sremoveUnknown l.tyAnnot) in
    TmLam {l with body = body, tyIdent = ty}
  | (tm, ty) -> tm
end

lang RecLetsTypeCheck = TypeCheck + RecLetsAst + LetTypeCheck
  sem typeCheckExpr env =
  | TmRecLets t ->
    let lvl = env.currentLvl in

    -- First: Generate a new environment containing the recursive bindings
    let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
      let tyBody = substituteUnknown (PolyVar ()) (addi 1 lvl) t.info b.tyAnnot in
      (_insertVar b.ident tyBody acc, {b with tyBody = tyBody})
    in
    match mapAccumL recLetEnvIteratee env t.bindings with (recLetEnv, bindings) in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckBinding = lam b: RecLetBinding.
      let body = optionMapOr b.body
        (lam ty. propagateTyAnnot (b.body, ty)) (sremoveUnknown b.tyAnnot) in
      let body = typeCheckExpr {recLetEnv with currentLvl = addi 1 lvl} body in
      -- Unify the inferred type of the body with the annotated one
      match stripTyAll (resolveAlias env.tyConEnv b.tyBody) with (_, tyStripped) in
      unify [infoTy b.tyAnnot, infoTm body] env tyStripped (tyTm body);
      {b with body = body}
    in
    let bindings = map typeCheckBinding bindings in

    -- Third: Produce a new environment with generalized types
    let envIteratee = lam acc. lam b : RecLetBinding.
      let tyBody = gen lvl b.tyBody in
      (_insertVar b.ident tyBody acc, {b with tyBody = tyBody})
    in
    match mapAccumL envIteratee env bindings with (env, bindings) in
    let inexpr = typeCheckExpr env t.inexpr in
    TmRecLets {t with bindings = bindings, inexpr = inexpr, ty = tyTm inexpr}
end

lang MatchTypeCheck = TypeCheck + PatTypeCheck + MatchAst
  sem typeCheckExpr env =
  | TmMatch t ->
    let target = typeCheckExpr env t.target in
    match typeCheckPat env (mapEmpty nameCmp) t.pat with (patEnv, pat) in
    unify [infoTm target, infoPat pat] env (tyTm target) (tyPat pat);
    let thnEnv : TCEnv = {env with varEnv = mapUnion env.varEnv patEnv} in
    let thn = typeCheckExpr thnEnv t.thn in
    let els = typeCheckExpr env t.els in
    unify [infoTm thn, infoTm els] env (tyTm thn) (tyTm els);
    TmMatch {t with target = target
                  , thn = thn
                  , els = els
                  , ty = tyTm thn
                  , pat = pat}
end

lang ConstTypeCheck = TypeCheck + MExprConstType
  sem typeCheckExpr env =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    let ty = inst env.tyConEnv env.currentLvl (f (tyConst t.val)) in
    TmConst {t with ty = ty}
end

lang SeqTypeCheck = TypeCheck + SeqAst
  sem typeCheckExpr env =
  | TmSeq t ->
    let elemTy = newvar env.currentLvl t.info in
    let tms = map (typeCheckExpr env) t.tms in
    iter (lam tm. unify [infoTm tm] env elemTy (tyTm tm)) tms;
    TmSeq {t with tms = tms, ty = ityseq_ t.info elemTy}
end

lang FlexDisableGeneralize = FlexTypeAst
  sem disableGeneralize =
  | TyFlex t & ty ->
    match deref t.contents with Unbound r then
      modref t.contents (Unbound {r with isWeak = true});
      sfold_VarSort_Type (lam. lam ty. disableGeneralize ty) () r.sort
    else
      disableGeneralize (resolveLink ty)
  | ty ->
    sfold_Type_Type (lam. lam ty. disableGeneralize ty) () ty
end

lang RecordTypeCheck = TypeCheck + RecordAst + RecordTypeAst + FlexDisableGeneralize
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
    unify [infoTm rec] env (tyTm rec) (newrecvar fields env.currentLvl (infoTm rec));
    (if env.disableRecordPolymorphism then disableGeneralize (tyTm rec) else ());
    TmRecordUpdate {t with rec = rec, value = value, ty = tyTm rec}
end

lang TypeTypeCheck = TypeCheck + TypeAst + SubstituteUnknown
  sem typeCheckExpr env =
  | TmType t ->
    checkUnknown t.info t.tyIdent;
    let env = _insertTyCon t.ident (t.params, t.tyIdent) env in
    let inexpr = typeCheckExpr env t.inexpr in
    TmType {t with inexpr = inexpr, ty = tyTm inexpr}
end

lang DataTypeCheck = TypeCheck + DataAst + SubstituteUnknown
  sem typeCheckExpr env =
  | TmConDef t ->
    checkUnknown t.info t.tyIdent;
    let inexpr = typeCheckExpr (_insertCon t.ident t.tyIdent env) t.inexpr in
    TmConDef {t with inexpr = inexpr, ty = tyTm inexpr}
  | TmConApp t ->
    let body = typeCheckExpr env t.body in
    match mapLookup t.ident env.conEnv with Some lty then
      match inst env.tyConEnv env.currentLvl lty with TyArrow {from = from, to = to} in
      unify [infoTm body] env (tyTm body) from;
      TmConApp {t with body = body, ty = to}
    else
      let msg = join [
        "Type check failed: reference to unbound constructor: ",
        nameGetStr t.ident, "\n"
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
    (match tusing with Some tu then
       unify [infoTm tu] env (tyTm tu) (tyarrows_ [tyTm test, tyTm expected, tybool_])
     else
       unify [infoTm test, infoTm expected] env (tyTm test) (tyTm expected));
    TmUtest {t with test = test
                  , expected = expected
                  , next = next
                  , tusing = tusing
                  , ty = tyTm next}
end

lang NeverTypeCheck = TypeCheck + NeverAst
  sem typeCheckExpr env =
  | TmNever t -> TmNever {t with ty = newvar env.currentLvl t.info}
end

lang ExtTypeCheck = TypeCheck + ExtAst + SubstituteUnknown
  sem typeCheckExpr env =
  | TmExt t ->
    checkUnknown t.info t.tyIdent;
    let env = {env with varEnv = mapInsert t.ident t.tyIdent env.varEnv} in
    let inexpr = typeCheckExpr env t.inexpr in
    TmExt {t with inexpr = inexpr, ty = tyTm inexpr}
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
        let patTy = newvar env.currentLvl t.info in
        (mapInsert n patTy patEnv, PatNamed {t with ty = patTy})
    else
      (patEnv, PatNamed {t with ty = newvar env.currentLvl t.info})
end

lang SeqTotPatTypeCheck = PatTypeCheck + SeqTotPat
  sem typeCheckPat env patEnv =
  | PatSeqTot t ->
    let elemTy = newvar env.currentLvl t.info in
    match mapAccumL (typeCheckPat env) patEnv t.pats with (patEnv, pats) in
    iter (lam pat. unify [infoPat pat] env elemTy (tyPat pat)) pats;
    (patEnv, PatSeqTot {t with pats = pats, ty = ityseq_ t.info elemTy})
end

lang SeqEdgePatTypeCheck = PatTypeCheck + SeqEdgePat
  sem typeCheckPat env patEnv =
  | PatSeqEdge t ->
    let elemTy = newvar env.currentLvl t.info in
    let seqTy = ityseq_ t.info elemTy in
    let unifyPat = lam pat. unify [infoPat pat] env elemTy (tyPat pat) in
    match mapAccumL (typeCheckPat env) patEnv t.prefix with (patEnv, prefix) in
    iter unifyPat prefix;
    match mapAccumL (typeCheckPat env) patEnv t.postfix with (patEnv, postfix) in
    iter unifyPat postfix;
    let patEnv =
      match t.middle with PName n then
        mapInsertWith
          (lam ty1. lam ty2. unify [t.info] env ty1 ty2; ty2) n seqTy patEnv
      else patEnv
    in
    (patEnv, PatSeqEdge {t with prefix = prefix, postfix = postfix, ty = seqTy})
end

lang RecordPatTypeCheck = PatTypeCheck + RecordPat + FlexDisableGeneralize
  sem typeCheckPat env patEnv =
  | PatRecord t ->
    let typeCheckBinding = lam patEnv. lam. lam pat. typeCheckPat env patEnv pat in
    match mapMapAccum typeCheckBinding patEnv t.bindings with (patEnv, bindings) in
    let ty = newrecvar (mapMap tyPat bindings) env.currentLvl t.info in
    (if env.disableRecordPolymorphism then disableGeneralize ty else ());
    (patEnv, PatRecord {t with bindings = bindings, ty = ty})
end

lang DataPatTypeCheck = TypeCheck + PatTypeCheck + DataPat
  sem typeCheckPat env patEnv =
  | PatCon t ->
    match mapLookup t.ident env.conEnv with Some ty then
      match inst env.tyConEnv env.currentLvl ty with TyArrow {from = from, to = to} in
      match typeCheckPat env patEnv t.subpat with (patEnv, subpat) in
      unify [infoPat subpat] env (tyPat subpat) from;
      (patEnv, PatCon {t with subpat = subpat, ty = to})
    else
      let msg = join [
        "Type check failed: reference to unbound constructor: ",
        nameGetStr t.ident, "\n"
      ] in
      errorSingle [t.info] msg
end

lang IntPatTypeCheck = PatTypeCheck + IntPat
  sem typeCheckPat env patEnv =
  | PatInt t -> (patEnv, PatInt {t with ty = TyInt {info = t.info}})
end

lang CharPatTypeCheck = PatTypeCheck + CharPat
  sem typeCheckPat env patEnv =
  | PatChar t -> (patEnv, PatChar {t with ty = TyChar {info = t.info}})
end

lang BoolPatTypeCheck = PatTypeCheck + BoolPat
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


lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FlexTypeUnify + FunTypeUnify + AppTypeUnify + AllTypeUnify +
  ConTypeUnify + SeqTypeUnify + BoolTypeUnify + IntTypeUnify + FloatTypeUnify +
  CharTypeUnify + TensorTypeUnify + RecordTypeUnify +

  -- Type generalization
  FlexTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck + RecLetsTypeCheck +
  MatchTypeCheck + ConstTypeCheck + SeqTypeCheck + RecordTypeCheck +
  TypeTypeCheck + DataTypeCheck + UtestTypeCheck + NeverTypeCheck + ExtTypeCheck +

  -- Patterns
  NamedPatTypeCheck + SeqTotPatTypeCheck + SeqEdgePatTypeCheck +
  RecordPatTypeCheck + DataPatTypeCheck + IntPatTypeCheck + CharPatTypeCheck +
  BoolPatTypeCheck + AndPatTypeCheck + OrPatTypeCheck + NotPatTypeCheck

end

-- NOTE(vipa, 2022-10-07): This can't use AnnotateMExprBase because it
-- has to thread a pprint environment, which AnnotateMExprBase doesn't
-- allow.
lang TyAnnot = AnnotateSources + PrettyPrint + Ast
  sem annotateMExpr : Expr -> Output
  sem annotateMExpr = | tm -> annotateAndReadSources (_annotateExpr pprintEnvEmpty tm).1

  sem _annotateExpr : PprintEnv -> Expr -> (PprintEnv, [(Info, Annotation)])
  sem _annotateExpr env = | tm ->
    match getTypeStringCode 0 env (tyTm tm) with (env, annot) in
    let res = (env, [(infoTm tm, annot)]) in
    let helper = lam f. lam acc. lam x.
      match f acc.0 x with (env, new) in
      (env, concat acc.1 new) in
    let res = sfold_Expr_Expr (helper _annotateExpr) res tm in
    let res = sfold_Expr_Pat (helper _annotatePat) res tm in
    res

  sem _annotatePat : PprintEnv -> Pat -> (PprintEnv, [(Info, Annotation)])
  sem _annotatePat env = | pat ->
    match getTypeStringCode 0 env (tyPat pat) with (env, annot) in
    let res = (env, [(infoPat pat, annot)]) in
    let helper = lam f. lam acc. lam x.
      match f acc.0 x with (env, new) in
      (env, concat acc.1 new) in
    let res = sfold_Pat_Expr (helper _annotateExpr) res pat in
    let res = sfold_Pat_Pat (helper _annotatePat) res pat in
    res
end

lang TestLang = MExprTypeCheck + MExprEq end

mexpr

use TestLang in

let gen_  = lam tm. bind_ (ulet_ "x" tm) (freeze_ (var_ "x")) in
let inst_ = lam tm. bind_ (ulet_ "x" tm) (var_ "x") in

let a = tyvar_ "a" in
let b = tyvar_ "b" in
let fa = newvar 0 (NoInfo ()) in
let fb = newvar 0 (NoInfo ()) in
let wa = newvarMono 0 (NoInfo ()) in
let wb = newvarMono 0 (NoInfo ()) in

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
  let env = foldr (lam n : (String, Type).
    mapInsert (nameNoSym n.0) n.1) (mapEmpty nameCmp) test.env in
  tyTm (typeCheckExpr {_tcEnvEmpty with varEnv = env} test.tm)
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
     type_ "Tree" (tyvariant_ []),
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
     type_ "Foo" (tyrecord_ [("x", tyint_)]),
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

-- TODO(aathn, 2021-09-28): Value restriction
