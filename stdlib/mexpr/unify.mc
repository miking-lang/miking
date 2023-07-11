-- Unification of MExpr types.  See type-check.mc for an overview of
-- the type checker.

include "result.mc"

include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"

---------------------------
-- UNIFICATION VARIABLES --
---------------------------

-- A level denotes the level in the AST that a type was introduced at
type Level = Int

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
  sem typePrecedence =
  | TyFlex t ->
    switch deref t.contents
    case Unbound _ then
      100000
    case Link ty then
      typePrecedence ty
    end
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

lang Unifier = FlexTypeAst
  syn TCError =
  | TypeUnificationError (Type, Type)

  type TCResult a = Result () TCError a

  syn Unifier =
  -- Intentionally left blank

  sem uempty : () -> Unifier

  sem uconcat : Unifier -> Unifier -> TCResult Unifier

  sem uinsert : FlexVarRec -> Type -> Unifier -> TCResult Unifier
end

lang Unify = Unifier + AliasTypeAst + PrettyPrint + Cmp + FlexTypeCmp
  syn UnifyExt =
  -- Intentionally left blank

  type UnifyEnv =
    { wrappedLhs : Type
    , wrappedRhs : Type
    , boundNames : BiNameMap
    , ext        : UnifyExt
    }

  -- Unify the types `ty1' and `ty2', where
  -- `ty1' is the expected type of an expression, and
  -- `ty2' is the inferred type of the expression,
  -- under the assumptions of `env'.
  sem unifyTypes : UnifyEnv -> (Type, Type) -> TCResult Unifier
  sem unifyTypes env =
  | (ty1, ty2) ->
    unifyBase
      {env with wrappedLhs = ty1, wrappedRhs = ty2}
      (unwrapType ty1, unwrapType ty2)

  -- unifyBase env (ty1, ty2) unifies ty1 and ty2 under the
  -- assumptions of env.
  -- IMPORTANT: Assumes that ty1 = unwrapType env.wrappedLhs and
  -- ty2 = unwrapType env.wrappedRhs.
  sem unifyBase : UnifyEnv -> (Type, Type) -> TCResult Unifier
  sem unifyBase env =
  | (ty1, ty2) ->
    result.err (TypeUnificationError (ty1, ty2))

  -- unifyCheck is called before a variable `tv' is unified with another type.
  sem unifyCheck : UnifyEnv -> FlexVarRec -> Type -> TCResult ()
end

-- Helper language providing functions to unify fields of record-like types
lang UnifyRows = Unify

  -- Check that 'm1' is a subset of 'm2'
  sem unifyRowsSubset : UnifyEnv -> Map SID Type -> Map SID Type -> TCResult Unifier
  sem unifyRowsSubset env m1 =
  | m2 ->
    let f = lam b.
      match b with (k, tyfield1) in
      match mapLookup k m2 with Some tyfield2 then
        unifyTypes env (tyfield1, tyfield2)
      else
        result.err (RowUnificationError (m1, m2))
    in
    let g = lam acc. lam b. result.bind (result.map2 uconcat acc (f b)) (lam x. x) in
    (result.mapAccumLM g (mapBindings m1)).0

  -- Check that 'm1' and 'm2' contain the same fields
  sem unifyRowsStrict : UnifyEnv -> Map SID Type -> Map SID Type -> TCResult Unifier
  sem unifyRowsStrict env m1 =
  | m2 ->
    if eqi (mapSize m1) (mapSize m2) then
      unifyRowsSubset env m1 m2
    else
      result.err (RowUnificationError (m1, m2))
end

lang VarTypeUnify = Unify + VarTypeAst
  sem unifyBase env =
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if nameEq t1.ident t2.ident then result.ok (uempty ())
    else if biMem (t1.ident, t2.ident) env.boundNames then result.ok (uempty ())
    else result.err (TypeUnificationError (ty1, ty2))
end

lang FlexTypeUnify = UnifyRows + FlexTypeAst + RecordTypeAst
  sem addSorts : UnifyEnv -> (VarSort, VarSort) -> TCResult (Unifier, VarSort)
  sem addSorts env =
  | (RecordVar r1, RecordVar r2) ->
    let f = lam acc. lam b.
      match b with (k, tyfield1) in
      match mapLookup k acc.1 with Some tyfield2 then
        let res =
          result.bind
            (result.map2 uconcat acc.0 (unifyTypes env (tyfield1, tyfield2) b))
            (lam x. x)
        in
        (res, acc.1)
      else
        (acc.0, mapInsert k tyfield1 acc.1)
    in
    match foldl f (result.ok (uempty ()), r2.fields) (mapBindings r1.fields)
      with (unifier, fields)
    in (unifier, RecordVar {r1 with fields = fields})
  | (RecordVar _ & rv, ! RecordVar _ & tv)
  | (! RecordVar _ & tv, RecordVar _ & rv) ->
    (uempty (), rv)
  | (PolyVar _, PolyVar _) -> (uempty (), PolyVar ())
  | (s1, s2) -> (uempty (), MonoVar ())

  sem unifyBase env =
  | (TyFlex t1 & ty1, TyFlex t2 & ty2) ->
    match (deref t1.contents, deref t2.contents) with (Unbound r1, Unbound r2) in
    if not (nameEq r1.ident r2.ident) then
      unifyCheck env r1 ty2;
      unifyCheck env r2 ty1;
      let updated =
        Unbound {r1 with level = mini r1.level r2.level,
                         sort = addSorts env (r1.sort, r2.sort)} in
      modref t1.contents updated;
      modref t2.contents (Link ty1)
    else ()
  | (TyFlex t1 & ty1, !TyFlex _ & ty2) ->
    match deref t1.contents with Unbound tv in
    unifyCheck env tv ty2;
    (match (tv.sort, ty2) with (RecordVar r1, TyRecord r2) then
      unifyRowsSubset env r1.fields r2.fields
    else match tv.sort with RecordVar _ then
      unificationError env
    else ());
    modref t1.contents (Link env.rhsName)
  | (!TyFlex _ & ty1, TyFlex _ & ty2) ->
    unifyBase {env with lhsName = env.rhsName, rhsName = env.lhsName} (ty2, ty1)

  sem unifyCheckBase env boundVars tv =
  | TyFlex t ->
    match deref t.contents with Unbound r in
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
            (lam. lam ty. unifyCheckType env boundVars tv ty) () r.sort;
          r.sort
      in
      let updated = Unbound {r with level = mini r.level tv.level,
                                    sort  = sort} in
      modref t.contents updated
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

lang AllTypeUnify = UnifyRows + AllTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyAll t1, TyAll t2) ->
    (match (t1.sort, t2.sort) with (RecordVar r1, RecordVar r2) then
      unifyRowsStrict env r1.fields r2.fields
    else if eqi (constructorTag t1.sort) (constructorTag t2.sort) then ()
    else unificationError env);
    let env = {env with names = biInsert (t1.ident, t2.ident) env.names} in
    unifyTypes env (t1.ty, t2.ty)

  sem unifyCheckBase env boundVars tv =
  | TyAll t ->
    match tv.sort with MonoVar _ then
      let msg = join [
        "* Encountered a monomorphic type used in a polymorphic position.\n",
        "* Perhaps you encountered the value restriction, or need a type annotation?\n",
        "* When type checking the expression\n"
      ] in
      errorSingle env.info msg
    else
      sfold_VarSort_Type (lam. lam ty. unifyCheckType env boundVars tv ty) () t.sort;
      unifyCheckType env (setInsert t.ident boundVars) tv t.ty
end

lang ConTypeUnify = Unify + ConTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyCon t1 & ty1, TyCon t2 & ty2) ->
    if nameEq t1.ident t2.ident then ()
    else unificationError env

  sem unifyCheckBase env boundVars tv =
  | TyCon t ->
    match optionMap (lam r. lti tv.level r.0) (mapLookup t.ident env.tyConEnv) with
      !Some false then
      let msg = join [
        "* Encountered a type constructor escaping its scope: ",
        nameGetStr t.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle env.info msg
    else ()
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

lang RecordTypeUnify = UnifyRows + RecordTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyRecord t1, TyRecord t2) ->
    unifyRowsStrict env t1.fields t2.fields
end
