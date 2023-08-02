-- Eliminates occurrences of polymorphic types in the provided (typed) MExpr
-- AST, by replacing polymorphic functions by multiple monomorphic functions
-- (one for each distinct combination of types used to invoke the function).

include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"

lang Monomorphize = MExprAst + MExprCmp
  type MOptions = {
    -- Enable monomorphization of intrinsic functions. This means that distinct
    -- uses of, e.g., map will be bound to different let-bindings which use
    -- monomorphic types. For example, we may get
    --
    --   let mapIntInt : (Int -> Int) -> [Int] -> [Int] = lam f. lam s. map f s
    intrinsics : Bool
  }

  sem monomorphizeDefaultOptions : () -> MOptions
  sem monomorphizeDefaultOptions =
  | _ -> { intrinsics = true }

  -- The monomorphization state consists of a map from each polymorphic
  -- function to its monomorphic instantiations. An instantiation is a map from
  -- type parameter names to concrete types. We map each instantiation to a
  -- distinct identifier.
  type Instantiation = Map Name Type
  type MonoState = Map Name (Map Instantiation Name)

  sem emptyInstantiation : () -> Instantiation
  sem emptyInstantiation =
  | _ -> mapEmpty nameCmp

  sem cmpInstantiation : Instantiation -> Instantiation -> Int
  sem cmpInstantiation lhs =
  | rhs -> mapCmp cmpType lhs rhs
end

lang MonomorphizeTypeInstantiation = Monomorphize
  -- NOTE(larshum, 2023-08-01): Finds the type parameter mapping of a
  -- monomorphic type with respect to its polymorphic type.
  sem findTypeParameterInstantiation : Type -> Type -> Instantiation
  sem findTypeParameterInstantiation polyType =
  | instType ->
    let polyType = unwrapType polyType in
    let pt = inspectType polyType in
    let it = unwrapType instType in
    let boundTypes = findBoundTypes (mapEmpty nameCmp) (pt, it) in
    constructInstantiationMapping boundTypes (emptyInstantiation ()) polyType

  sem constructInstantiationMapping : Map Name Type -> Instantiation -> Type -> Instantiation
  sem constructInstantiationMapping inst acc =
  | TyAll {ident = ident, ty = innerTy, info = info} ->
    let ty =
      match mapLookup ident inst with Some ty then
        match ty with TyUnknown {info = info} then
          TyRecord {fields = mapEmpty cmpSID, info = info}
        else ty
      else
        -- NOTE(larshum, 2023-08-01): We reach this case if the type parameter is
        -- never used. In this case, we choose to use the unit type (empty
        -- record). Note that any type would be valid in this case.
        TyRecord {fields = mapEmpty cmpSID, info = info}
    in
    constructInstantiationMapping inst (mapInsert ident ty acc) innerTy
  | _ ->
    acc

  sem findBoundTypes : Map Name Type -> (Type, Type) -> Map Name Type
  sem findBoundTypes acc =
  | (TyVar {ident = ident}, monoType) ->
    -- NOTE(larshum, 2023-08-01): We assume the instantiated type is well-typed
    -- with respect to the polymorphic type assigned to the type variable.
    mapInsert ident monoType acc
  | (TyArrow {from = f1, to = t1}, TyArrow {from = f2, to = t2}) ->
    let acc = findBoundTypes acc (f1, f2) in
    findBoundTypes acc (t1, t2)
  | (TySeq {ty = lty}, TySeq {ty = rty}) ->
    findBoundTypes acc (lty, rty)
  | (TyTensor {ty = lty}, TyTensor {ty = rty}) ->
    findBoundTypes acc (lty, rty)
  | (TyRecord {fields = lfields}, TyRecord {fields = rfields}) ->
    let mergefn = lam lval. lam rval.
      match (lval, rval) with (Some lty, Some rty) then
        Some (lty, rty)
      else
        error "Monomorphization error: Record field mismatch"
    in
    let f = lam acc. lam. lam tyPair.
      findBoundTypes acc tyPair
    in
    mapFoldWithKey f acc (mapMerge mergefn lfields rfields)
  | (TyApp {lhs = ll, rhs = lr}, TyApp {lhs = rl, rhs = rr}) ->
    let acc = findBoundTypes acc (ll, rl) in
    findBoundTypes acc (lr, rr)
  | (lty, rty) ->
    -- NOTE(larshum, 2023-08-01): In other cases, we accept the type and ignore
    -- its contents if both types have the same constructor tag.
    if eqi (constructorTag lty) (constructorTag rty) then acc
    else
      dprintLn lty;
      dprintLn rty;
      error "Monomorphization error: Unsupported polymorphic type instantiation"

  sem instantiateExpr : Instantiation -> Expr -> Expr
  sem instantiateExpr instMap =
  | t ->
    let t = smap_Expr_Type (instantiateType instMap) t in
    smap_Expr_Expr (instantiateExpr instMap) t

  sem instantiateType : Instantiation -> Type -> Type
  sem instantiateType instMap =
  | TyVar t ->
    match mapLookup t.ident instMap with Some ty then
      ty
    else TyVar t
  | ty ->
    smap_Type_Type (instantiateType instMap) ty
end

lang MonomorphizeCollect = Monomorphize
  sem collectPolymorphic : MonoState -> Expr -> MonoState
  sem collectPolymorphic inst =
  | TmLet t ->
    let inst =
      match t.tyBody with TyAll _ then
        mapInsert t.ident (mapEmpty cmpInstantiation) inst
      else inst
    in
    collectPolymorphic inst t.inexpr
  | TmRecLets t ->
    let collectBind = lam inst. lam bind.
      match bind.tyBody with TyAll _ then
        mapInsert bind.ident (mapEmpty cmpInstantiation) inst
      else inst
    in
    let inst = foldl collectBind inst t.bindings in
    collectPolymorphic inst t.inexpr
  | TmType t ->
    let inst =
      if null t.params then inst
      else mapInsert t.ident (mapEmpty cmpInstantiation) inst
    in
    collectPolymorphic inst t.inexpr
  | t ->
    sfold_Expr_Expr collectPolymorphic inst t
end

lang MonomorphizePropagate = Monomorphize + MonomorphizeTypeInstantiation
  sem propagateMonomorphicInstantiations : MonoState -> Expr -> MonoState
  sem propagateMonomorphicInstantiations state =
  | TmLet t ->
    let state = propagateMonomorphicInstantiations state t.inexpr in
    match mapLookup t.ident state with Some instMap then
      -- NOTE(larshum, 2023-08-01): For each monomorphic instantiation of the
      -- the current binding, we propagate this to polymorphic functions used
      -- within the body of this binding.
      let typeInstantiations = mapKeys instMap in
      propagateInstantiationsExpr typeInstantiations state t.body
    else
      -- NOTE(larshum, 2023-08-01): We use an empty instantiation to represent
      -- a monomorphic binding.
      propagateInstantiationsExpr [emptyInstantiation ()] state t.body
  | ast -> state

  sem propagateInstantiationsExpr : [Instantiation] -> MonoState -> Expr -> MonoState
  sem propagateInstantiationsExpr typeInstantiations state =
  | TmVar t ->
    match mapLookup t.ident state with Some instMap then
      let f : Instantiation -> Instantiation = lam inst.
        -- NOTE(larshum, 2023-08-01): We instantiate the variable type once for
        -- each monomorphic version of the outer function. Then, we extract the
        -- type variables of each instantiated type, and store these.
        let monoTy = instantiateType inst t.ty in
        findTypeParameterInstantiation t.ty monoTy
      in
      foldl
        (lam instMap. lam inst.
          if mapMem inst instMap then instMap
          else mapInsert inst (nameSetNewSym t.ident) instMap)
        instMap
        (map f typeInstantiations)
    else
      TmVar t
  | t ->
    sfold_Expr_Expr (propagateInstantiationsExpr typeInstantiations) state t
end

lang MonomorphizeApply = Monomorphize
  sem applyMonomorphization : MonoState -> Expr -> Expr
  sem applyMonomorphization state =
  | ast -> ast
end

lang MExprMonomorphize =
  MonomorphizeTypeInstantiation + MonomorphizeCollect + MonomorphizePropagate +
  MonomorphizeApply

  sem collectBoundTypeParameters : [(Name, VarSort)] -> Type -> [(Name, VarSort)]
  sem collectBoundTypeParameters btp =
  | TyAll {ident = ident, sort = sort, ty = ty} ->
    let btp = snoc (ident, sort) in
    collectBoundTypeParameters btp ty
  | _ ->
    btp

  sem monomorphize : MOptions -> Expr -> Expr
  sem monomorphize options =
  | ast ->
    ast
end

lang MExprMonomorphizeTest =
  MExprMonomorphize + MExprSym + MExprTypeCheck + MExprEq + MExprPrettyPrint

  sem isMonomorphic : Expr -> Bool
  sem isMonomorphic =
  | ast -> isMonomorphicExpr true ast

  sem isMonomorphicExpr : Bool -> Expr -> Bool
  sem isMonomorphicExpr acc =
  | e ->
    let acc = sfold_Expr_Expr isMonomorphicExpr acc e in
    let acc = sfold_Expr_Type isMonomorphicType acc e in
    let acc = sfold_Expr_Pat isMonomorphicPat acc e in
    isMonomorphicType acc (tyTm e)

  sem isMonomorphicType : Bool -> Type -> Bool
  sem isMonomorphicType acc =
  | TyAll _ | TyVar _ -> false
  | ty -> sfold_Type_Type isMonomorphicType acc ty

  sem isMonomorphicPat : Bool -> Pat -> Bool
  sem isMonomorphicPat acc =
  | p ->
    let acc = sfold_Pat_Pat isMonomorphicPat acc p in
    sfold_Pat_Type isMonomorphicType acc p
end

mexpr

use MExprMonomorphizeTest in

let preprocess = lam ast.
  typeCheck (symbolize ast)
in
let mm = lam ast.
  monomorphize (monomorphizeDefaultOptions ()) ast
in

-- Tests that we can correctly extract the type parameter mapping of a
-- monomorphic type given the polymorphic declaration type.

let nMapTy = lam fromTy. lam toTy.
  tyarrows_ [ tyint_, tyarrow_ fromTy toTy, tyseq_ fromTy, tyseq_ toTy ]
in
let polyNMapTy = tyall_ "a" (tyall_ "b" (nMapTy (tyvar_ "a") (tyvar_ "b"))) in

utest mapValues (findTypeParameterInstantiation polyNMapTy (nMapTy tyint_ tyfloat_))
with [tyint_, tyfloat_] using eqSeq eqType in

utest mapValues (findTypeParameterInstantiation polyNMapTy (nMapTy (tyseq_ tychar_) tyint_))
with [tyseq_ tychar_, tyint_] using eqSeq eqType in

utest mapValues (findTypeParameterInstantiation polyNMapTy (nMapTy tyunknown_ tyint_))
with [tyunit_, tyint_] using eqSeq eqType in

let someTy = lam tyArg. tyarrow_ tyArg (tyapp_ (tycon_ "Option") tyArg) in
let polySomeTy = tyall_ "a" (someTy (tyvar_ "a")) in
utest mapValues (findTypeParameterInstantiation polySomeTy (someTy tyint_))
with [tyint_] using eqSeq eqType in

let lenTy = lam elemTy.
  tyarrow_ (tyseq_ elemTy) tyint_
in
let polyLenTy = tyall_ "a" (lenTy (tyvar_ "a")) in
utest mapValues (findTypeParameterInstantiation polyLenTy (lenTy tyint_))
with [tyint_] using eqSeq eqType in

let polyTensorLenTy = tyall_ "a" (tyarrow_ (tytensor_ (tyvar_ "a")) tyint_) in
utest mapValues (findTypeParameterInstantiation polyTensorLenTy (tyarrow_ (tytensor_ tyint_) tyint_))
with [tyint_] using eqSeq eqType in

let projIdTy = lam poly.
  tyarrows_ [tyrecord_ [("a", poly), ("b", tyint_)], tyint_]
in
let polyProjTy = tyall_ "a" (projIdTy (tyvar_ "a")) in
utest mapValues (findTypeParameterInstantiation polyProjTy (projIdTy (tyseq_ tyfloat_)))
with [tyseq_ tyfloat_] using eqSeq eqType in

let polyty = tyall_ "a" (tyapp_ (tycon_ "Unknown") (tyvar_ "a")) in
let monoty = tyapp_ (tycon_ "Unknown") tyint_ in
utest mapValues (findTypeParameterInstantiation polyty monoty)
with [tyint_] using eqSeq eqType in

let accMapTy = lam a. lam b. lam c.
  tyarrows_ [tyarrows_ [a, b, tytuple_ [a, c]], a, tyseq_ b, tytuple_ [a, tyseq_ c]]
in
let polyAccMapTy =
  tyall_ "a" (tyall_ "b" (tyall_ "c" (accMapTy (tyvar_ "a") (tyvar_ "b") (tyvar_ "c"))))
in
let intAccMapTy = accMapTy tyint_ tyint_ tyint_ in
utest mapValues (findTypeParameterInstantiation polyAccMapTy intAccMapTy)
with [tyint_, tyint_, tyint_] using eqSeq eqType in

let leftPolyTy =
  tyall_ "a" (tyall_ "b" (tyarrow_ (tyvar_ "a") (tyapps_ (tycon_ "Either") [tyvar_ "a", tyvar_ "b"])))
in
let rightPolyTy =
  tyall_ "a" (tyall_ "b" (tyarrow_ (tyvar_ "b") (tyapps_ (tycon_ "Either") [tyvar_ "a", tyvar_ "b"])))
in
let leftTy = lam tyArg. tyarrow_ tyArg (tyapps_ (tycon_ "Either") [tyArg, tyunknown_]) in
let rightTy = lam tyArg. tyarrow_ tyArg (tyapps_ (tycon_ "Either") [tyunknown_, tyArg]) in
utest mapValues (findTypeParameterInstantiation leftPolyTy (leftTy tyint_))
with [tyint_, tyunit_] using eqSeq eqType in
utest mapValues (findTypeParameterInstantiation rightPolyTy (rightTy tyint_))
with [tyunit_, tyint_] using eqSeq eqType in

-- Tests that the propagation of monomorphic instantiations works as expected.

-- TODO: add tests for the above category

-- Tests that the monomorphization is correctly applied given the monomorphic
-- instantiations to apply to a given expression.

-- TODO: add tests for the above category

-- Tests for the entire monomorphization pass.

-- TODO: start enabling the below tests once all passes are ready to go

--let monoFun = preprocess (bindall_ [
--  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
--  app_ (var_ "addOne") (int_ 3)
--]) in
--utest isMonomorphic monoFun with true in
--
--let idPoly = preprocess (bindall_ [
--  ulet_ "id" (ulam_ "x" (var_ "x")),
--  utuple_ [app_ (var_ "id") (int_ 2), app_ (var_ "id") (float_ 2.5)]
--]) in
--let expected = preprocess (bindall_ [
--  let_ "id_int" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
--  let_ "id_float" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
--  utuple_ [app_ (var_ "id_int") (int_ 2), app_ (var_ "id_float") (float_ 2.5)]
--]) in
--let result = mm idPoly in
--utest isMonomorphic idPoly with false in
--utest isMonomorphic result with true in -- fails
--utest isMonomorphic expected with true in
--utest result with expected using eqExpr in -- fails
--
--let mapPoly = preprocess (bindall_ [
--  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
--  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
--  ulet_ "x1" (map_ (var_ "addOne") (seq_ [int_ 2])),
--  ulet_ "x2" (map_ (var_ "addHalf") (seq_ [float_ 2.5]))
--]) in
--let result = mm mapPoly in
--let expected = preprocess (bindall_ [
--  let_ "mapInt" (tyarrows_ [tyarrow_ tyint_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
--    (ulam_ "f" (ulam_ "s" (map_ (var_ "f") (var_ "s")))),
--  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
--  ulet_ "x1" (appf2_ (var_ "mapInt") (var_ "addOne") (seq_ [int_ 2])),
--  let_ "mapFloat" (tyarrows_ [tyarrow_ tyfloat_ tyfloat_, tyseq_ tyfloat_, tyseq_ tyfloat_])
--    (ulam_ "f" (ulam_ "s" (map_ (var_ "f") (var_ "s")))),
--  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
--  ulet_ "x2" (appf2_ (var_ "mapFloat") (var_ "addHalf") (seq_ [float_ 2.5]))
--]) in
--utest result with expected using eqExpr in -- fails
--
--let seqPoly = preprocess (bindall_ [
--  ulet_ "g" (ulam_ "x" (var_ "x")),
--  ulet_ "f" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
--  utuple_ [app_ (var_ "f") (int_ 2), app_ (var_ "f") (float_ 2.5)]
--]) in
--let result = mm seqPoly in
--let expected = preprocess (bindall_ [
--  let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
--  let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
--  let_ "fInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (app_ (var_ "gInt") (var_ "x"))),
--  let_ "fFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (app_ (var_ "gFloat") (var_ "x"))),
--  utuple_ [app_ (var_ "fInt") (int_ 2), app_ (var_ "fFloat") (float_ 2.5)]
--]) in
--utest isMonomorphic seqPoly with false in
--utest isMonomorphic result with true in -- fails
--utest isMonomorphic expected with true in
--utest result with expected using eqExpr in -- fails
--
--let nestedPoly = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "g" (ulam_ "s" (bindall_ [
--    ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
--    map_ (var_ "h") (var_ "s")
--  ]))),
--  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
--  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
--  utuple_ [
--    appf2_ (var_ "f") (var_ "addOne") (seq_ [int_ 2]),
--    appf2_ (var_ "f") (var_ "addHalf") (seq_ [float_ 2.5])]
--]) in
--let result = mm nestedPoly in
--let expected = preprocess (bindall_ [
--  let_ "fInt"
--    (tyarrows_ [tyarrow_ tyint_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
--    (ulam_ "g" (ulam_ "s" (bindall_ [
--      ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
--      map_ (var_ "h") (var_ "s")
--  ]))),
--  let_ "fFloat"
--    (tyarrows_ [tyarrow_ tyfloat_ tyfloat_, tyseq_ tyfloat_, tyseq_ tyfloat_])
--    (ulam_ "g" (ulam_ "s" (bindall_ [
--      ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
--      map_ (var_ "h") (var_ "s")
--  ]))),
--  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
--  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
--  utuple_ [
--    appf2_ (var_ "fInt") (var_ "addOne") (seq_ [int_ 2]),
--    appf2_ (var_ "fFloat") (var_ "addHalf") (seq_ [float_ 2.5])]
--]) in
--utest isMonomorphic nestedPoly with false in
--utest isMonomorphic result with true in -- fails
--utest isMonomorphic expected with true in
--utest result with expected using eqExpr in -- fails
--
--let innerPoly = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "x" (ulam_ "y" (bindall_ [
--    ulet_ "g" (ulam_ "z" (var_ "z")),
--    utuple_ [app_ (var_ "g") (var_ "x"), app_ (var_ "g") (var_ "y")]
--  ]))),
--  appf2_ (var_ "f") (int_ 2) (float_ 2.5)
--]) in
--let result = mm innerPoly in
--let expected = preprocess (bindall_ [
--  let_ "f" (tyarrows_ [tyint_, tyfloat_, tytuple_ [tyint_, tyfloat_]])
--    (ulam_ "x" (ulam_ "y" (bindall_ [
--      let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "z" (var_ "z")),
--      let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "z" (var_ "z")),
--      utuple_ [app_ (var_ "gInt") (var_ "x"), app_ (var_ "gFloat") (var_ "y")]
--  ]))),
--  appf2_ (var_ "f") (int_ 2) (float_ 2.5)
--]) in
--utest isMonomorphic innerPoly with false in
--utest isMonomorphic result with true in -- fails
--utest isMonomorphic expected with true in
--utest result with expected using eqExpr in -- fails
--
--let higherOrderPoly = preprocess (bindall_ [
--  let_ "g" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a"))) (ulam_ "x" (var_ "x")),
--  ulet_ "f" (lam_ "g" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")))
--    (ulam_ "x" (ulam_ "y" (bindall_ [
--      ulet_ "a" (app_ (var_ "g") (var_ "x")),
--      ulet_ "b" (app_ (var_ "g") (var_ "y")),
--      utuple_ [var_ "a", var_ "b"]
--  ])))),
--  ulet_ "x1" (int_ 2),
--  ulet_ "x2" (float_ 2.5),
--  ulet_ "y" (appf3_ (var_ "f") (freeze_ (var_ "g")) (var_ "x1") (var_ "x2"))
--]) in
--let result = mm higherOrderPoly in
--let expected = preprocess (bindall_ [
--  let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
--  let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
--  ulet_ "x1" (int_ 2),
--  ulet_ "x2" (float_ 2.5),
--  let_ "fIntFloat"
--    (tyarrows_ [tyarrow_ tyint_ tyint_, tyarrow_ tyfloat_ tyfloat_, tyint_, tyfloat_, tytuple_ [tyint_, tyfloat_]])
--    (ulam_ "gInt" (ulam_ "gFloat" (ulam_ "x" (ulam_ "y" (bindall_ [
--      ulet_ "a" (app_ (var_ "gInt") (var_ "x")),
--      ulet_ "b" (app_ (var_ "gFloat") (var_ "y")),
--      utuple_ [var_ "a", var_ "b"]
--  ]))))),
--  ulet_ "y" (appf4_ (var_ "fIntFloat") (var_ "gInt") (var_ "gFloat") (var_ "x1") (var_ "x2"))
--]) in
--utest isMonomorphic higherOrderPoly with false in
--utest isMonomorphic result with true in -- fails
--utest isMonomorphic expected with true in
--utest result with expected using eqExpr in -- fails
--
--let polyVariant = preprocess (bindall_ [
--  type_ "Option" ["a"] (tyvariant_ []),
--  condef_ "Some" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyapp_ (tycon_ "Option") (tyvar_ "a")))),
--  condef_ "None" (tyall_ "a" (tyarrow_ (tytuple_ []) (tyapp_ (tycon_ "Option") (tyvar_ "a")))),
--  ulet_ "isSome" (ulam_ "o" (
--    match_ (var_ "o") (pcon_ "Some" pvarw_) true_ false_)),
--  utuple_ [
--    app_ (var_ "isSome") (conapp_ "Some" (int_ 2)),
--    app_ (var_ "isSome") (conapp_ "Some" (float_ 2.5)),
--    app_ (var_ "isSome") (conapp_ "None" uunit_)
--  ]
--]) in
--let result = mm polyVariant in
---- NOTE(larshum, 2023-06-28): When type parameters are not used, they are set
---- to unknown. In this case, when constructing a None, we don't use the type
---- parameter. The monomorphization should replace it with the Unit type (empty
---- record).
--let expected = preprocess (bindall_ [
--  type_ "OptionInt" [] (tyvariant_ []),
--  condef_ "SomeInt" (tyarrow_ tyint_ (tycon_ "OptionInt")),
--  condef_ "NoneInt" (tyarrow_ (tytuple_ []) (tycon_ "OptionInt")),
--  let_ "isSomeInt" (tyarrow_ (tycon_ "OptionInt") tybool_)
--    (ulam_ "o" (
--      match_ (var_ "o") (pcon_ "SomeInt" pvarw_) true_ false_)),
--  type_ "OptionFloat" [] (tyvariant_ []),
--  condef_ "SomeFloat" (tyarrow_ tyfloat_ (tycon_ "OptionFloat")),
--  condef_ "NoneFloat" (tyarrow_ (tytuple_ []) (tycon_ "OptionFloat")),
--  let_ "isSomeFloat" (tyarrow_ (tycon_ "OptionFloat") tybool_)
--    (ulam_ "o" (
--      match_ (var_ "o") (pcon_ "SomeFloat" pvarw_) true_ false_)),
--  type_ "OptionUnit" [] (tyvariant_ []),
--  condef_ "SomeUnit" (tyarrow_ tyunit_ (tycon_ "OptionUnit")),
--  condef_ "NoneUnit" (tyarrow_ (tytuple_ []) (tycon_ "OptionUnit")),
--  let_ "isSomeUnit" (tyarrow_ (tycon_ "OptionUnit") tybool_)
--    (ulam_ "o" (
--      match_ (var_ "o") (pcon_ "SomeUnit" pvarw_) true_ false_)),
--  utuple_ [
--    app_ (var_ "isSomeInt") (conapp_ "SomeInt" (int_ 2)),
--    app_ (var_ "isSomeFloat") (conapp_ "SomeFloat" (float_ 2.5)),
--    app_ (var_ "isSomeUnit") (conapp_ "NoneUnit" uunit_)
--  ]
--]) in
--utest isMonomorphic polyVariant with false in
--utest isMonomorphic result with true in -- fails
--utest isMonomorphic expected with true in
--utest mexprToString result with mexprToString expected using eqString in -- fails

()
