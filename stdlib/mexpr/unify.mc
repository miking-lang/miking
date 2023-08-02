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
lang FlexTypeAst = KindAst + Ast
  type FlexVarRec = {ident  : Name,
                     level  : Level,
    -- The level indicates at what depth the variable was bound introduced,
    -- which is used to determine which variables can be generalized.
                     kind   : Kind}

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
      match smapAccumL_Kind_Type f acc r.kind with (acc, kind) in
      modref t.contents (Unbound {r with kind = kind});
      (acc, TyFlex t)
    case Link ty then
      f acc ty
    end

  sem rappAccumL_Type_Type (f : acc -> Type -> (acc, Type)) (acc : acc) =
  | TyFlex t & ty ->
    recursive let work = lam ty.
      match ty with TyFlex x then
        switch deref x.contents
        case Link l then
          let new = work l in
          modref x.contents (Link new);
          new
        case Unbound _ then
          ty
        end
      else ty in
    switch work ty
    case TyFlex _ then (acc, ty)
    case ty1 then f acc ty1
    end
end

lang FlexTypeCmp = Cmp + FlexTypeAst
  sem cmpTypeH =
  | (TyFlex l, TyFlex r) ->
    -- NOTE(vipa, 2023-04-19): Any non-link TyFlex should have been
    -- unwrapped already, thus we can assume `Unbound` here.
    match (deref l.contents, deref r.contents) with (Unbound l, Unbound r) in
    nameCmp l.ident r.ident
end

lang FlexTypePrettyPrint = IdentifierPrettyPrint + KindPrettyPrint + FlexTypeAst
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
      match getKindStringCode indent env idstr t.kind with (env, str) in
      let monoPrefix =
        match t.kind with Mono _ then "_" else "" in
      (env, concat monoPrefix str)
    case Link ty then
      getTypeStringCode indent env ty
    end
end

lang FlexTypeEq = KindEq + FlexTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyFlex _ & rhs ->
    switch (unwrapType lhs, unwrapType rhs)
    case (TyFlex l, TyFlex r) then
      match (deref l.contents, deref r.contents) with (Unbound n1, Unbound n2) in
      optionBind
        (_eqCheck n1.ident n2.ident biEmpty free.freeTyFlex)
        (lam freeTyFlex.
          eqKind typeEnv {free with freeTyFlex = freeTyFlex} (n1.kind, n2.kind))
    case (! TyFlex _, ! TyFlex _) then
      eqTypeH typeEnv free lhs rhs
    case _ then None ()
    end
end


----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = AliasTypeAst + PrettyPrint + Cmp + FlexTypeCmp
  type UnifyEnv = {
    wrappedLhs: Type,  -- The currently examined left-hand subtype, before resolving aliases
    wrappedRhs: Type,  -- The currently examined right-hand subtype, before resolving aliases
    boundNames: BiNameMap  -- The bijective correspondence between bound variables in scope
  }

  syn UnifyError =
  | Types (Type, Type)
  | Rows (Map SID Type, Map SID Type)
  | Kinds (Kind, Kind)

  type UnifyResult a = Result () UnifyError a
  type Unifier = [(Ref FlexVar, Type)]

  -- Unify the types `ty1` and `ty2`, where
  -- `ty1` is the expected type of an expression, and
  -- `ty2` is the inferred type of the expression,
  -- under the assumptions of `env`.  Returns a list of pairs
  -- `var, ty`, where variable `var` should be unified with the type
  -- `ty`.
  sem unifyTypes : UnifyEnv -> (Type, Type) -> UnifyResult Unifier
  sem unifyTypes env =
  | (ty1, ty2) ->
    unifyBase
      {env with wrappedLhs = ty1, wrappedRhs = ty2}
      (unwrapType ty1, unwrapType ty2)

  -- unifyBase env (ty1, ty2) unifies ty1 and ty2 under the
  -- assumptions of env.
  -- IMPORTANT: Assumes that ty1 = unwrapType env.wrappedLhs and
  -- ty2 = unwrapType env.wrappedRhs.
  sem unifyBase : UnifyEnv -> (Type, Type) -> UnifyResult Unifier
  sem unifyBase env =
  | (ty1, ty2) ->
    result.err (Types (ty1, ty2))
end

-- Helper language providing functions to unify fields of record-like types
lang UnifyRows = Unify
  -- Check that 'm1' is a subset of 'm2'
  sem unifyRowsSubset : UnifyEnv -> Map SID Type -> Map SID Type -> UnifyResult Unifier
  sem unifyRowsSubset env m1 =
  | m2 ->
    let f = lam acc. lam b.
      let unifier =
        match b with (k, tyfield1) in
        match mapLookup k m2 with Some tyfield2 then
          unifyTypes env (tyfield1, tyfield2)
        else
          result.err (Rows (m1, m2))
      in
      result.map2 concat acc unifier
    in
    foldl f (result.ok []) (mapBindings m1)

  -- Check that 'm1' and 'm2' contain the same fields
  sem unifyRowsStrict : UnifyEnv -> Map SID Type -> Map SID Type -> UnifyResult Unifier
  sem unifyRowsStrict env m1 =
  | m2 ->
    if eqi (mapSize m1) (mapSize m2) then
      unifyRowsSubset env m1 m2
    else
      result.err (Rows (m1, m2))

  -- Check that the intersection of 'm1' and 'm2' unifies, then return their union
  sem unifyRowsUnion : UnifyEnv -> Map SID Type -> Map SID Type -> (UnifyResult Unifier, Map SID Type)
  sem unifyRowsUnion env m1 =
  | m2 ->
    let f = lam acc. lam b.
      match b with (k, tyfield1) in
      match mapLookup k acc.1 with Some tyfield2 then
        (result.map2 concat acc.0 (unifyTypes env (tyfield1, tyfield2)), acc.1)
      else
        (acc.0, mapInsert k tyfield1 acc.1)
    in
    foldl f (result.ok [], m2) (mapBindings m1)
end

lang VarTypeUnify = Unify + VarTypeAst
  sem unifyBase env =
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if nameEq t1.ident t2.ident then result.ok []
    else if biMem (t1.ident, t2.ident) env.boundNames then result.ok []
    else result.err (Types (ty1, ty2))
end

lang FlexTypeUnify = Unify + FlexTypeAst + RecordTypeAst
  sem unifyBase env =
  | (TyFlex t1, ty2) ->
    result.ok [(t1.contents, env.wrappedRhs)]
  | (!TyFlex _ & ty1, TyFlex _ & ty2) ->
    unifyBase {env with wrappedLhs = env.wrappedRhs, wrappedRhs = env.wrappedLhs} (ty2, ty1)
end

lang FunTypeUnify = Unify + FunTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyArrow t1, TyArrow t2) ->
    result.map2 concat
      (unifyTypes env (t1.from, t2.from))
      (unifyTypes env (t1.to, t2.to))
end

lang AppTypeUnify = Unify + AppTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyApp t1, TyApp t2) ->
    result.map2 concat
      (unifyTypes env (t1.lhs, t2.lhs))
      (unifyTypes env (t1.rhs, t2.rhs))
end

lang AllTypeUnify = UnifyRows + AllTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyAll t1, TyAll t2) ->
    result.map2 concat
      (match (t1.kind, t2.kind) with (Row r1, Row r2) then
        unifyRowsStrict env r1.fields r2.fields
       else if eqi (constructorTag t1.kind) (constructorTag t2.kind) then result.ok []
            else result.err (Kinds (t1.kind, t2.kind)))
      (let env = {env with boundNames = biInsert (t1.ident, t2.ident) env.boundNames} in
       unifyTypes env (t1.ty, t2.ty))
end

lang ConTypeUnify = Unify + ConTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyCon t1 & ty1, TyCon t2 & ty2) ->
    if nameEq t1.ident t2.ident then result.ok []
    else result.err (Types (ty1, ty2))
end

lang BoolTypeUnify = Unify + BoolTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyBool _, TyBool _) -> result.ok []
end

lang IntTypeUnify = Unify + IntTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyInt _, TyInt _) -> result.ok []
end

lang FloatTypeUnify = Unify + FloatTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyFloat _, TyFloat _) -> result.ok []
end

lang CharTypeUnify = Unify + CharTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyChar _, TyChar _) -> result.ok []
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
