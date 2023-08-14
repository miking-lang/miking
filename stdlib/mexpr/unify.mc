-- Unification of MExpr types.  See type-check.mc for an overview of
-- the type checker.

include "result.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/info.mc"
include "mexpr/type.mc"


----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = Ast
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
  type Unifier = [(UnifyEnv, Type, Type)]

  -- Unify the types `ty1` and `ty2` under the assumptions of `env`.
  -- Returns a list of unification obligations `(env, TyMetaVar m, ty)`, where the
  -- variable of the left-hand side should be unified with the type `ty`.  Note that
  -- this function can return a non-error result even for two incompatible types.
  -- For instance, it could return `[(env, varA, Int), (env, varA, Bool)]`, which gives
  -- two incompatible types to `varA`.
  -- For a full unification which errors in this scenario, see `unifyPure` below.
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

lang MetaVarTypeUnify = Unify + UnifyRows + MetaVarTypeAst
  sem addKinds : UnifyEnv -> (Kind, Kind) -> (UnifyResult Unifier, Kind)
  sem addKinds env =
  | (Row r1, Row r2) ->
    match unifyRowsUnion env r1.fields r2.fields with (unifier, fields) in
    (unifier, Row {r1 with fields = fields})
  | (Row _ & rv, ! Row _ & tv)
  | (! Row _ & tv, Row _ & rv) ->
    (result.ok [], rv)
  | (Poly _, Poly _) -> (result.ok [], Poly ())
  | (s1, s2) -> (result.ok [], Mono ())

  sem unifyBase env =
  | (TyMetaVar _ & ty1, ty2) ->
    result.ok [(env, ty1, ty2)]
  | (!TyMetaVar _ & ty1, TyMetaVar _ & ty2) ->
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


lang UnifyPure = Unify + MetaVarTypeAst + VarTypeSubstitute
  -- Unify types `ty1` and `ty2`, returning a map of variable substitutions
  -- equating the two, or giving an error if the types are incompatible.
  -- This function does not perform any occurs checks, scope checking, or
  -- level updates, and accepts cyclic equations.
  sem unifyPure : Type -> Type -> UnifyResult (Map Name Type)
  sem unifyPure ty1 = | ty2 ->
  recursive let work = lam acc. lam unifier.
    switch unifier
    case [] then result.ok acc
    case [ (env, meta, ty) ] ++ rest then
      switch unwrapType meta
      case TyMetaVar t then
        match deref t.contents with Unbound r in
        let isEqual =
          match unwrapType ty with TyMetaVar t2 then
            match deref t2.contents with Unbound r2 in nameEq r.ident r2.ident
          else false
        in
        if isEqual then work acc rest else
          if mapMem r.ident acc then work acc rest else
            let subst = mapInsert r.ident ty (mapEmpty nameCmp) in
            let f = substituteMetaVars subst in
            let g = lam x. (x.0, f x.1, f x.2) in
            work (mapUnion (mapMap f acc) subst) (map g rest)
      case other then
        result.bind (unifyTypes env (other, ty))
          (lam newUnifier. work acc (concat newUnifier rest))
      end
    end
  in
  let env : UnifyEnv = {
    boundNames = biEmpty,
    wrappedLhs = ty1,
    wrappedRhs = ty2
  } in
  result.bind (unifyTypes env (ty1, ty2)) (work (mapEmpty nameCmp))
end


lang MExprUnify =
  VarTypeUnify + MetaVarTypeUnify + FunTypeUnify + AppTypeUnify + AllTypeUnify +
  ConTypeUnify + BoolTypeUnify + IntTypeUnify + FloatTypeUnify + CharTypeUnify +
  SeqTypeUnify + TensorTypeUnify + RecordTypeUnify
end

lang TestLang = UnifyPure + MExprUnify + MExprEq + MetaVarTypeEq end

mexpr

use TestLang in

let eqUnifyError = lam e1. lam e2.
  switch (e1, e2)
  case (Types t1, Types t2) then and (eqType t1.0 t2.0) (eqType t1.1 t2.1)
  case _ then error "eqUnifyError: TODO"
  end
in

let unifyEq = eitherEq (eqSeq eqUnifyError) (mapEq eqType) in

let a = nameSym "a" in
let b = nameSym "b" in

let wa =
  TyMetaVar {info = NoInfo (),
             contents = ref (Unbound {ident = a,
                                      level = 0,
                                      kind  = Mono ()})} in
let wb =
  TyMetaVar {info = NoInfo (),
             contents = ref (Unbound {ident = b,
                                      level = 0,
                                      kind  = Mono ()})} in

let ok  = lam x. Right (mapFromSeq nameCmp x) in
let err = lam x. Left (map (lam y. Types y) x) in
let testUnify = lam ty1. lam ty2. (result.consume (unifyPure ty1 ty2)).1 in

utest testUnify tyint_ tyint_ with ok [] using unifyEq in

utest testUnify tybool_ tyint_ with err [(tybool_, tyint_)] using unifyEq in

utest testUnify wa tyint_ with ok [(a, tyint_)] using unifyEq in

utest testUnify (tyarrow_ wa wb) (tyarrow_ tyint_ tybool_)
  with ok [(a, tyint_), (b, tybool_)]
  using unifyEq
in

utest testUnify (tyarrow_ wa wa) (tyarrow_ tyint_ tybool_)
  with err [(tyint_, tybool_)]
  using unifyEq
in

utest testUnify (tyarrow_ wa tybool_) (tyarrow_ wb wb)
  with ok [(a, tybool_), (b, tybool_)]
  using unifyEq
in

utest testUnify (tytuple_ [wa, wb]) (tytuple_ [wa, wa])
  with ok [(b, wa)]
  using unifyEq
in

utest testUnify (tytuple_ [wa, wa]) (tytuple_ [tyseq_ wa, tyseq_ (tyseq_ wa)])
  with ok [(a, tyseq_ wa)]
  using unifyEq
in

()
