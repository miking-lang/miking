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
include "mexpr/const-types.mc"
include "mexpr/eq.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type.mc"
include "mexpr/cmp.mc"

-- A level denotes the nesting level of the let that a type variable is introduced by
type Level = Int

type TCEnv = {
  varEnv: Map Name Type,
  conEnv: Map Name Type,
  tyVarEnv: Map Name Level,
  currentLvl: Level,
  disableRecordPolymorphism: Bool
}

let _tcEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  conEnv = mapEmpty nameCmp,
  tyVarEnv = mapEmpty nameCmp,

  currentLvl = 0,
  disableRecordPolymorphism = true
}

let _insertVar = lam name. lam ty. lam env : TCEnv.
  {env with varEnv = mapInsert name ty env.varEnv}

let _insertCon = lam name. lam ty. lam env : TCEnv.
  {env with conEnv = mapInsert name ty env.conEnv}

type UnifyEnv = {
  info: [Info],  -- The info of the expression(s) triggering the unification
  expectedType: Type,  -- The expected type of the expression
  foundType: Type,  -- The inferred type of the expression
  lhsName: Type,  -- The currently examined left-hand subtype, before resolving aliases
  rhsName: Type,  -- The currently examined right-hand subtype, before resolving aliases
  tyVarEnv: Map Name Level,  -- The free type variables in scope and their levels
  names: BiNameMap  -- The bijective correspondence between bound variables in scope
}

-- Unification (or 'flexible') variables.  These variables represent some
-- specific but as-of-yet undetermined type, and are used only in type checking.
lang FlexTypeAst = VarSortAst + Ast
  type FlexVarRec = {ident  : Name,
                     level  : Level,
    -- The level indicates at what depth the variable was bound introduced,
    -- which is used to determine which variables can be generalized.
                     sort   : VarSort}
    -- The sort of a variable can be polymorphic, monomorphic or a record.

  syn FlexVar =
  | Unbound FlexVarRec
  | Link Type

  syn Type =
  -- Flexible type variable
  | TyFlex {info     : Info,
            contents : Ref FlexVar}

  sem tyWithInfo (info : Info) =
  | TyFlex t ->
    switch deref t.contents
    case Unbound _ then
      TyFlex {t with info = info}
    case Link ty then
      tyWithInfo info ty
    end

  sem infoTy =
  | TyFlex {info = info} -> info

  sem smapAccumL_Type_Type (f : acc -> Type -> (acc, Type)) (acc : acc) =
  | TyFlex t ->
    switch deref t.contents
    case Unbound r then
      match smapAccumL_VarSort_Type f acc r.sort with (acc, sort) in
      modref t.contents (Unbound {r with sort = sort});
      (acc, TyFlex t)
    case Link ty then
      f acc ty
    end

  sem rappAccumL_Type_Type (f : acc -> Type -> (acc, Type)) (acc : acc) =
  | TyFlex t & ty ->
    match deref t.contents with Link inner then f acc inner
    else (acc, ty)
end

lang FlexTypeCmp = Cmp + FlexTypeAst
  sem cmpTypeH =
  | (TyFlex l, TyFlex r) ->
    -- NOTE(vipa, 2023-04-19): Any non-link TyFlex should have been
    -- unwrapped already, thus we can assume `Unbound` here.
    match (deref l.contents, deref r.contents) with (Unbound l, Unbound r) in
    nameCmp l.ident r.ident
end

lang FlexTypePrettyPrint = IdentifierPrettyPrint + VarSortPrettyPrint + FlexTypeAst
  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  | TyFlex t ->
    switch deref t.contents
    case Unbound t then
      match pprintVarName env t.ident with (env, idstr) in
      match getVarSortStringCode indent env idstr t.sort with (env, str) in
      let monoPrefix =
        match t.sort with MonoVar _ then "_" else "" in
      (env, concat monoPrefix str)
    case Link ty then
      getTypeStringCode indent env ty
    end
end

lang FlexTypeEq = VarSortEq + FlexTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyFlex _ & rhs ->
    switch (unwrapType lhs, unwrapType rhs)
    case (TyFlex l, TyFlex r) then
      match (deref l.contents, deref r.contents) with (Unbound n1, Unbound n2) in
      optionBind
        (_eqCheck n1.ident n2.ident biEmpty free.freeTyFlex)
        (lam freeTyFlex.
          eqVarSort typeEnv {free with freeTyFlex = freeTyFlex} (n1.sort, n2.sort))
    case (! TyFlex _, ! TyFlex _) then
      eqTypeH typeEnv free lhs rhs
    case _ then None ()
    end
end

----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = MExprAst + FlexTypeAst + PrettyPrint + Cmp + FlexTypeCmp
  -- Unify the types `ty1' and `ty2', where
  -- `ty1' is the expected type of an expression, and
  -- `ty2' is the inferred type of the expression.
  -- Modifies the types in place.
  sem unify (tcEnv : TCEnv) (info : [Info]) (ty1 : Type) =
  | ty2 ->
    let env : UnifyEnv = {
      names = biEmpty,
      info = info,
      expectedType = ty1,
      foundType = ty2,
      lhsName = ty1,
      rhsName = ty2,
      tyVarEnv = tcEnv.tyVarEnv
    } in
    unifyTypes env (ty1, ty2)

  sem unifyTypes (env : UnifyEnv) =
  | (ty1, ty2) ->
    unifyBase
      {env with lhsName = ty1, rhsName = ty2}
      (unwrapType ty1, unwrapType ty2)

  -- Unify the types `ty1' and `ty2' under the assumptions of `env'.
  -- IMPORTANT: Assumes that ty1 and ty2 have been unwrapped using unwrapType
  sem unifyBase (env : UnifyEnv) =
  | (ty1, ty2) ->
    unificationError env

  -- unifyCheck is called before a variable `tv' is unified with another type.
  -- Performs multiple tasks in one traversal:
  -- - Occurs check
  -- - Update level fields of FlexVars
  -- - If `tv' is monomorphic, ensure it is not unified with a polymorphic type
  -- - If `tv' is unified with a free type variable, ensure no capture occurs
  sem unifyCheck : UnifyEnv -> FlexVarRec -> Type -> ()
  sem unifyCheck env tv =
  | ty -> unifyCheckBase env (setEmpty nameCmp) tv ty

  sem unifyCheckBase : UnifyEnv -> Set Name -> FlexVarRec -> Type -> ()
  sem unifyCheckBase env boundVars tv =
  | ty ->
    sfold_Type_Type (lam. lam ty. unifyCheckBase env boundVars tv ty) () ty

  sem unificationError : UnifyEnv -> ()
  sem unificationError =
  | env ->
    let pprintEnv = pprintEnvEmpty in
    match getTypeStringCode 0 pprintEnv env.expectedType with (pprintEnv, expected) in
    match getTypeStringCode 0 pprintEnv env.foundType with (pprintEnv, found) in
    recursive let collectAliases : Map Type Type -> Type -> Map Type Type
      = lam acc. lam ty.
        match ty with TyAlias x then
          let acc = mapInsert x.display x.content acc in
          collectAliases (collectAliases acc x.display) x.content
        else sfold_Type_Type collectAliases acc ty
    in
    let aliases = collectAliases (mapEmpty cmpType) env.expectedType in
    let aliases = collectAliases aliases env.foundType in
    match
      if mapIsEmpty aliases then (pprintEnv, "") else
        let f = lam env. lam pair.
          match getTypeStringCode 0 env pair.0 with (env, l) in
          match getTypeStringCode 0 env pair.1 with (env, r) in
          (env, join ["\n*   ", l, " = ", r]) in
        match mapAccumL f pprintEnv (mapBindings aliases) with (pprintEnv, aliases) in
        (pprintEnv, join ["* where", join aliases, "\n"])
    with (pprintEnv, aliases) in
    let msg = join [
      "* Expected an expression of type: ",
      expected, "\n",
      "* Found an expression of type: ",
      found, "\n",
      aliases,
      "* When type checking the expression\n"
    ] in
    errorSingle env.info msg
end

-- Helper language providing functions to unify fields of record-like types
lang UnifyFields = Unify
  -- Check that 'm1' is a subset of 'm2'
  sem unifyFields (env : UnifyEnv) (m1 : Map SID Type) =
  | m2 ->
    let f = lam b : (SID, Type).
      match b with (k, tyfield1) in
      match mapLookup k m2 with Some tyfield2 then
        unifyTypes env (tyfield1, tyfield2)
      else
        unificationError env
    in
    iter f (mapBindings m1)

  -- Check that 'm1' and 'm2' contain the same fields
  sem unifyFieldsStrict (env : UnifyEnv) (m1 : Map SID Type) =
  | m2 ->
    if eqi (mapSize m1) (mapSize m2) then
      unifyFields env m1 m2
    else
      unificationError env
end

lang VarTypeUnify = Unify + VarTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if nameEq t1.ident t2.ident then ()
    else if biMem (t1.ident, t2.ident) env.names then ()
    else unificationError env

  sem unifyCheckBase env boundVars tv =
  | TyVar t ->
    if not (setMem t.ident boundVars) then
      match optionMap (lti tv.level) (mapLookup t.ident env.tyVarEnv) with
        !Some false then
        let msg = join [
          "* Encountered a type variable escaping its scope: ",
          nameGetStr t.ident, "\n",
          "* Perhaps the annotation of the associated let-binding is too general?\n",
          "* When type checking the expression\n"
        ] in
        errorSingle env.info msg
      else ()
    else ()
end

lang FlexTypeUnify = UnifyFields + FlexTypeAst + RecordTypeAst
  sem addSorts (env : UnifyEnv) =
  | (RecordVar r1, RecordVar r2) ->
    let f = lam ty1. lam ty2. unifyTypes env (ty1, ty2); ty1 in
    RecordVar {r1 with fields = mapUnionWith f r1.fields r2.fields}
  | (RecordVar _ & rv, ! RecordVar _ & tv)
  | (! RecordVar _ & tv, RecordVar _ & rv) ->
    rv
  | (PolyVar _, PolyVar _) -> PolyVar ()
  | (s1, s2) -> MonoVar ()

  sem unifyBase (env : UnifyEnv) =
  | (TyFlex t1 & ty1, TyFlex t2 & ty2) ->
    match (deref t1.contents, deref t2.contents) with (Unbound r1, Unbound r2) in
    if not (nameEq r1.ident r2.ident) then
      unifyCheck env r1 ty2;
      unifyCheck env r2 ty1;
      let updated =
        Unbound {r1 with level = mini r1.level r2.level
                , sort = addSorts env (r1.sort, r2.sort)} in
      modref t1.contents updated;
      modref t2.contents (Link ty1)
    else ()
  | (TyFlex t1 & ty1, !TyFlex _ & ty2) ->
    match deref t1.contents with Unbound tv in
    unifyCheck env tv ty2;
    (match (tv.sort, ty2) with (RecordVar r1, TyRecord r2) then
      unifyFields env r1.fields r2.fields
    else match tv.sort with RecordVar _ then
      unificationError env
    else ());
    modref t1.contents (Link env.rhsName)
  | (!TyFlex _ & ty1, TyFlex _ & ty2) ->
    unifyBase {env with lhsName = env.rhsName, rhsName = env.lhsName} (ty2, ty1)

  sem unifyCheckBase env boundVars tv =
  | TyFlex t ->
    switch deref t.contents
    case Unbound r then
      if nameEq r.ident tv.ident then
        let msg = join [
          "* Encountered a type occurring within itself.\n",
          "* Recursive types are only permitted using data constructors.\n",
          "* When type checking the expression\n"
        ] in
        errorSingle env.info msg
      else
        let sort =
          match (tv.sort, r.sort) with (MonoVar _, PolyVar _) then MonoVar ()
          else
            sfold_VarSort_Type
              (lam. lam ty. unifyCheckBase env boundVars tv ty) () r.sort;
            r.sort
        in
        let updated = Unbound {r with level = mini r.level tv.level,
                                      sort  = sort} in
        modref t.contents updated
    case Link ty then
      unifyCheckBase env boundVars tv ty
    end
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

lang AllTypeUnify = UnifyFields + AllTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyAll t1, TyAll t2) ->
    (match (t1.sort, t2.sort) with (RecordVar r1, RecordVar r2) then
      unifyFieldsStrict env r1.fields r2.fields
    else if eqi (constructorTag t1.sort) (constructorTag t2.sort) then ()
    else unificationError env);
    let env = {env with names = biInsert (t1.ident, t2.ident) env.names} in
    unifyTypes env (t1.ty, t2.ty)

  sem unifyCheckBase env boundVars tv =
  | TyAll t ->
    match tv.sort with MonoVar _ then
      let msg = join [
        "* Encountered a function parameter used in a polymorphic position.\n",
        "* Perhaps you need a type annotation for the parameter?\n",
        "* When type checking the expression\n"
      ] in
      errorSingle env.info msg
    else
      sfold_VarSort_Type (lam. lam ty. unifyCheckBase env boundVars tv ty) () t.sort;
      unifyCheckBase env (setInsert t.ident boundVars) tv t.ty
end

lang ConTypeUnify = Unify + ConTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyCon t1 & ty1, TyCon t2 & ty2) ->
    if nameEq t1.ident t2.ident then ()
    else unificationError env
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
  lam sort. lam level. lam info. use FlexTypeAst in
  TyFlex {info = info,
          contents = ref (Unbound {ident = nameSym "a",
                                   level = level,
                                   sort = sort})}

let newvarMono = use VarSortAst in
  newflexvar (MonoVar ())
let newvar = use VarSortAst in
  newflexvar (PolyVar ())
let newrecvar = use VarSortAst in
  lam fields. newflexvar (RecordVar {fields = fields})

lang Generalize = AllTypeAst + VarTypeSubstitute + FlexTypeAst
  -- Instantiate the top-level type variables of `ty' with fresh unification variables.
  sem inst (info : Info) (lvl : Level) =
  | ty ->
    switch stripTyAll ty
    case ([], _) then ty
    case (vars, stripped) then
      let inserter = lam subst. lam v : (Name, VarSort).
        let sort = smap_VarSort_Type (substituteVars subst) v.1 in
        mapInsert v.0 (newflexvar sort lvl info) subst
      in
      let subst = foldl inserter (mapEmpty nameCmp) vars in
      substituteVars subst stripped
    end

  -- Generalize the unification variables in `ty' introduced at least at level `lvl`.
  -- Return the generalized type and the sequence of variables quantified.
  -- Any rigid variable in the map `vs' encountered will also be quantified over.
  sem gen (lvl : Level) (vs : Map Name VarSort) =
  | ty ->
    let vars = distinct (lam x. lam y. nameEq x.0 y.0)
                 (genBase lvl vs (setEmpty nameCmp) ty) in
    let iteratee = lam v. lam ty1.
      let sort = match v.1 with MonoVar _ then PolyVar () else v.1 in
      TyAll {info = infoTy ty, ident = v.0, ty = ty1, sort = sort}
    in
    (foldr iteratee ty vars, vars)

  sem genBase (lvl : Level) (vs : Map Name VarSort) (bound : Set Name) =
  | ty ->
    sfold_Type_Type (lam vars. lam ty.
      concat vars (genBase lvl vs bound ty)) [] ty
end

lang FlexTypeGeneralize = Generalize + FlexTypeAst + VarTypeAst
  sem genBase (lvl : Level) (vs : Map Name VarSort) (bound : Set Name) =
  | TyFlex t ->
    switch deref t.contents
    case Unbound {ident = n, level = k, sort = s} then
      if lti lvl k then
        -- Var is free, generalize
        let f = lam vars. lam ty.
          concat vars (genBase lvl vs bound ty) in
        let vars = sfold_VarSort_Type f [] s in
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
  sem genBase (lvl : Level) (vs : Map Name VarSort) (bound : Set Name) =
  | TyVar t ->
    match mapLookup t.ident vs with Some sort then
      if not (setMem t.ident bound) then [(t.ident, sort)]
      else []
    else []
end

lang AllTypeGeneralize = Generalize + AllTypeAst
  sem genBase (lvl : Level) (vs : Map Name VarSort) (bound : Set Name) =
  | TyAll t -> genBase lvl vs (setInsert t.ident bound) t.ty
end

-- The default cases handle all other constructors!

-------------------
-- TYPE CHECKING --
-------------------

lang RemoveFlex = FlexTypeAst + UnknownTypeAst + RecordTypeAst
  sem removeFlexType =
  | TyFlex t ->
    switch deref t.contents
    case Unbound {sort = RecordVar x} then
      TyRecord {info = t.info, fields = mapMap removeFlexType x.fields}
    case Unbound _ then TyUnknown { info = t.info }
    case Link ty then removeFlexType ty
    end
  | ty ->
    smap_Type_Type removeFlexType ty

  sem removeFlexExpr =
  | tm ->
    let tm = smap_Expr_TypeLabel removeFlexType tm in
    let tm = smap_Expr_Type removeFlexType tm in
    let tm = smap_Expr_Pat removeFlexPat tm in
    smap_Expr_Expr removeFlexExpr tm

  sem removeFlexPat =
  | pat ->
    let pat = withTypePat (removeFlexType (tyPat pat)) pat in
    smap_Pat_Pat removeFlexPat pat
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
      "* Encountered Unknown type in an illegal position.\n",
      "* Unknown is only allowed in annotations, not in definitions or declarations.\n",
      "* When type checking the expression\n"
    ] in
    errorSingle [info] msg
  | ty ->
    sfold_Type_Type (lam. lam ty. checkUnknown info ty) () ty
end

lang TypeCheck = Unify + Generalize + RemoveFlex
  -- Type check 'tm', with FreezeML-style type inference. Returns the
  -- term annotated with its type. The resulting type contains no
  -- unification variables or links.
  -- IMPORTANT: Assumes that aliases in 'tm' have been replaced with TyAlias
  -- nodes (this is done in the symbolization step).
  sem typeCheck : Expr -> Expr
  sem typeCheck =
  | tm ->
    removeFlexExpr (typeCheckExpr _tcEnvEmpty tm)

  -- Type check `expr' under the type environment `env'. The resulting
  -- type may contain unification variables and links.
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
        unify env [infoPat pat] patTy (tyPat pat);
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
    let tyRhs = newvar env.currentLvl t.info in
    let tyRes = newvar env.currentLvl t.info in
    unify env [infoTm t.lhs] (ityarrow_ (infoTm lhs) tyRhs tyRes) (tyTm lhs);
    unify env [infoTm t.rhs] tyRhs (tyTm rhs);
    TmApp {t with lhs = lhs, rhs = rhs, ty = tyRes}
end

lang FlexDisableGeneralize = Unify
  sem weakenTyFlex (lvl : Level) =
  | TyFlex t & ty ->
    switch deref t.contents
    case Unbound r then
      sfold_VarSort_Type (lam. lam ty. weakenTyFlex lvl ty) () r.sort;
      let sort = match r.sort with PolyVar _ then MonoVar () else r.sort in
      modref t.contents (Unbound {r with level = mini lvl r.level, sort = sort})
    case Link tyL then
      weakenTyFlex lvl tyL
    end
  | ty ->
    sfold_Type_Type (lam. lam ty. weakenTyFlex lvl ty) () ty

  sem disableRecordGeneralize (lvl : Level) =
  | TyFlex t & ty ->
    switch deref t.contents
    case Unbound {sort = RecordVar _} then
      weakenTyFlex lvl ty
    case Unbound _ then ()
    case Link tyL then
      disableRecordGeneralize lvl tyL
    end
  | ty ->
    sfold_Type_Type (lam. lam ty. disableRecordGeneralize lvl ty) () ty
end

lang LetTypeCheck =
  TypeCheck + LetAst + LamAst + FunTypeAst + SubstituteUnknown + FlexDisableGeneralize
  sem typeCheckExpr env =
  | TmLet t ->
    let newLvl = addi 1 env.currentLvl in
    let tyBody = substituteUnknown (PolyVar ()) newLvl t.info t.tyAnnot in
    match stripTyAll tyBody with (vars, stripped) in
    let newTyVars = foldr (lam v. mapInsert v.0 newLvl) env.tyVarEnv vars in
    let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVars} in
    let body = typeCheckExpr newEnv (propagateTyAnnot (t.body, t.tyAnnot)) in
    -- Unify the annotated type with the inferred one and generalize
    (match tyTm body with TyAll _ then
      unify newEnv [infoTy t.tyAnnot, infoTm body] tyBody (tyTm body)
     else
      unify newEnv [infoTy t.tyAnnot, infoTm body] stripped (tyTm body));
    (if env.disableRecordPolymorphism then
      disableRecordGeneralize env.currentLvl tyBody else ());
    match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
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

lang RecLetsTypeCheck = TypeCheck + RecLetsAst + LetTypeCheck + FlexDisableGeneralize
  sem typeCheckExpr env =
  | TmRecLets t ->

    let newLvl = addi 1 env.currentLvl in
    -- First: Generate a new environment containing the recursive bindings
    let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
      let tyBody = substituteUnknown (PolyVar ()) newLvl t.info b.tyAnnot in
      match stripTyAll tyBody with (vars, _) in
      let newEnv = _insertVar b.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
      ((newEnv, newTyVars), {b with tyBody = tyBody})
    in
    match mapAccumL recLetEnvIteratee (env, mapEmpty nameCmp) t.bindings
      with ((newEnv, tyVars), bindings) in
    let newTyVarEnv =
      mapFoldWithKey (lam vs. lam v. lam. mapInsert v newLvl vs) newEnv.tyVarEnv tyVars in
    let recLetEnv = {newEnv with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckBinding = lam b: RecLetBinding.
      let body = typeCheckExpr recLetEnv (propagateTyAnnot (b.body, b.tyAnnot)) in
      -- Unify the inferred type of the body with the annotated one
      (match tyTm body with TyAll _ then
        unify recLetEnv [infoTy b.tyAnnot, infoTm body] b.tyBody (tyTm body)
       else
        match stripTyAll b.tyBody with (_, stripped) in
        unify recLetEnv [infoTy b.tyAnnot, infoTm body] stripped (tyTm body));
      {b with body = body}
    in
    let bindings = map typeCheckBinding bindings in

    -- Third: Produce a new environment with generalized types
    let envIteratee = lam acc. lam b : RecLetBinding.
      (if env.disableRecordPolymorphism then
        disableRecordGeneralize env.currentLvl b.tyBody else ());
      match gen env.currentLvl acc.1 b.tyBody with (tyBody, vars) in
      let newEnv = _insertVar b.ident tyBody acc.0 in
      let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
      ((newEnv, newTyVars), {b with tyBody = tyBody})
    in
    match mapAccumL envIteratee (env, tyVars) bindings with ((env, _), bindings) in
    let inexpr = typeCheckExpr env t.inexpr in
    TmRecLets {t with bindings = bindings, inexpr = inexpr, ty = tyTm inexpr}
end

lang MatchTypeCheck = TypeCheck + PatTypeCheck + MatchAst
  sem typeCheckExpr env =
  | TmMatch t ->
    let target = typeCheckExpr env t.target in
    match typeCheckPat env (mapEmpty nameCmp) t.pat with (patEnv, pat) in
    unify env [infoTm target, infoPat pat] (tyPat pat) (tyTm target);
    let thnEnv : TCEnv = {env with varEnv = mapUnion env.varEnv patEnv} in
    let thn = typeCheckExpr thnEnv t.thn in
    let els = typeCheckExpr env t.els in
    unify env [infoTm thn, infoTm els] (tyTm thn) (tyTm els);
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
    let ty = inst t.info env.currentLvl (f (tyConst t.val)) in
    TmConst {t with ty = ty}
end

lang SeqTypeCheck = TypeCheck + SeqAst
  sem typeCheckExpr env =
  | TmSeq t ->
    let elemTy = newvar env.currentLvl t.info in
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

lang TypeTypeCheck = TypeCheck + TypeAst + SubstituteUnknown
  sem typeCheckExpr env =
  | TmType t ->
    checkUnknown t.info t.tyIdent;
    let inexpr = typeCheckExpr env t.inexpr in
    TmType {t with inexpr = inexpr, ty = tyTm inexpr}
end

lang DataTypeCheck = TypeCheck + DataAst + FunTypeAst + SubstituteUnknown
  sem typeCheckExpr env =
  | TmConDef t ->
    checkUnknown t.info t.tyIdent;
    let inexpr = typeCheckExpr (_insertCon t.ident t.tyIdent env) t.inexpr in
    TmConDef {t with inexpr = inexpr, ty = tyTm inexpr}
  | TmConApp t ->
    let body = typeCheckExpr env t.body in
    match mapLookup t.ident env.conEnv with Some lty then
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
    (match tusing with Some tu then
       unify env [infoTm tu] (tyarrows_ [tyTm test, tyTm expected, tybool_]) (tyTm tu)
     else
       unify env [infoTm test, infoTm expected] (tyTm test) (tyTm expected));
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
    iter (lam pat. unify env [infoPat pat] elemTy (tyPat pat)) pats;
    (patEnv, PatSeqTot {t with pats = pats, ty = ityseq_ t.info elemTy})
end

lang SeqEdgePatTypeCheck = PatTypeCheck + SeqEdgePat
  sem typeCheckPat env patEnv =
  | PatSeqEdge t ->
    let elemTy = newvar env.currentLvl t.info in
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
end

lang RecordPatTypeCheck = PatTypeCheck + RecordPat
  sem typeCheckPat env patEnv =
  | PatRecord t ->
    let typeCheckBinding = lam patEnv. lam. lam pat. typeCheckPat env patEnv pat in
    match mapMapAccum typeCheckBinding patEnv t.bindings with (patEnv, bindings) in
    let ty = newrecvar (mapMap tyPat bindings) env.currentLvl t.info in
    (patEnv, PatRecord {t with bindings = bindings, ty = ty})
end

lang DataPatTypeCheck = PatTypeCheck + DataPat + FunTypeAst + Generalize
  sem typeCheckPat env patEnv =
  | PatCon t ->
    match mapLookup t.ident env.conEnv with Some ty then
      match inst t.info env.currentLvl ty with TyArrow {from = from, to = to} in
      match typeCheckPat env patEnv t.subpat with (patEnv, subpat) in
      unify env [infoPat subpat] from (tyPat subpat);
      (patEnv, PatCon {t with subpat = subpat, ty = to})
    else
      let msg = join [
        "* Encountered an unbound constructor: ",
        nameGetStr t.ident, "\n",
        "* when type checking the pattern\n"
      ] in
      errorSingle [t.info] msg
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


lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FlexTypeUnify + FunTypeUnify + AppTypeUnify + AllTypeUnify +
  ConTypeUnify + SeqTypeUnify + BoolTypeUnify + IntTypeUnify + FloatTypeUnify +
  CharTypeUnify + TensorTypeUnify + RecordTypeUnify +

  -- Type generalization
  FlexTypeGeneralize + VarTypeGeneralize + AllTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck + RecLetsTypeCheck +
  MatchTypeCheck + ConstTypeCheck + SeqTypeCheck + RecordTypeCheck +
  TypeTypeCheck + DataTypeCheck + UtestTypeCheck + NeverTypeCheck + ExtTypeCheck +

  -- Patterns
  NamedPatTypeCheck + SeqTotPatTypeCheck + SeqEdgePatTypeCheck +
  RecordPatTypeCheck + DataPatTypeCheck + IntPatTypeCheck + CharPatTypeCheck +
  BoolPatTypeCheck + AndPatTypeCheck + OrPatTypeCheck + NotPatTypeCheck +

  -- Pretty Printing
  FlexTypePrettyPrint
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

lang TestLang = MExprTypeCheck + MExprEq + FlexTypeEq + MExprPrettyPrint
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
  let bindings = map (lam p. (nameSym p.0, p.1)) test.env in
  let symEnv = mapFromSeq cmpString (map (lam p. (nameGetStr p.0, p.0)) bindings) in
  let tyEnv = mapFromSeq nameCmp bindings in
  unwrapTypes
    (tyTm
       (typeCheckExpr {_tcEnvEmpty with varEnv = tyEnv}
          (symbolizeExpr {symEnvEmpty with varEnv = symEnv} test.tm)))
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

-- TODO(aathn, 2021-09-28): Value restriction
