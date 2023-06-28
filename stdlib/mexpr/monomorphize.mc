-- Eliminates occurrences of polymorphic types in the provided (typed) MExpr
-- AST, by replacing polymorphic functions by multiple monomorphic functions
-- (one for each distinct combination of types used to invoke the function).

include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"

lang Monomorphize
  type MOptions = {
    -- Enable monomorphization of intrinsic functions. This means that distinct
    -- uses of, e.g., map will be bound to different let-bindings which use
    -- monomorphic types. For example, we may get
    --
    --   let mapIntInt : (Int -> Int) -> [Int] -> [Int] = lam f. lam s. map f s
    intrinsics : Bool,

    -- Enable monomorphization of regular type variables.
    variables : Bool,

    -- Enable monomorphization of row polymorphism on record types.
    records : Bool
  }

  sem monomorphizeDefaultOptions : () -> MOptions
  sem monomorphizeDefaultOptions =
  | _ -> { intrinsics = true, variables = true, records = false }
end

lang MExprTestMonomorphic = MExprAst
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

lang MExprMonomorphize = Monomorphize + MExprTestMonomorphic
  sem monomorphize : MOptions -> Expr -> Expr
  sem monomorphize options =
  | ast ->
    if options.records then
      error "Row type monomorphization is not implemented yet"
    else
      -- TODO
      ast
end

lang TestLang =
  MExprMonomorphize + MExprSym + MExprTypeCheck + MExprEq + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam ast.
  typeCheck (symbolize ast)
in
let mm = lam ast.
  monomorphize (monomorphizeDefaultOptions ()) ast
in

let monoFun = preprocess (bindall_ [
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "addOne") (int_ 3)
]) in
utest isMonomorphic monoFun with true in

let idPoly = preprocess (bindall_ [
  ulet_ "id" (ulam_ "x" (var_ "x")),
  utuple_ [app_ (var_ "id") (int_ 2), app_ (var_ "id") (float_ 2.5)]
]) in
let expected = preprocess (bindall_ [
  let_ "id_int" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
  let_ "id_float" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
  utuple_ [app_ (var_ "id_int") (int_ 2), app_ (var_ "id_float") (float_ 2.5)]
]) in
let result = mm idPoly in
utest isMonomorphic idPoly with false in
utest isMonomorphic result with true in -- fails
utest isMonomorphic expected with true in
utest result with expected using eqExpr in -- fails

let mapPoly = preprocess (bindall_ [
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
  ulet_ "x1" (map_ (var_ "addOne") (seq_ [int_ 2])),
  ulet_ "x2" (map_ (var_ "addHalf") (seq_ [float_ 2.5]))
]) in
let result = mm mapPoly in
let expected = preprocess (bindall_ [
  let_ "mapInt" (tyarrows_ [tyarrow_ tyint_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
    (ulam_ "f" (ulam_ "s" (map_ (var_ "f") (var_ "s")))),
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "x1" (appf2_ (var_ "mapInt") (var_ "addOne") (seq_ [int_ 2])),
  let_ "mapFloat" (tyarrows_ [tyarrow_ tyfloat_ tyfloat_, tyseq_ tyfloat_, tyseq_ tyfloat_])
    (ulam_ "f" (ulam_ "s" (map_ (var_ "f") (var_ "s")))),
  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
  ulet_ "x2" (appf2_ (var_ "mapFloat") (var_ "addHalf") (seq_ [float_ 2.5]))
]) in
utest result with expected using eqExpr in -- fails

let seqPoly = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (var_ "x")),
  ulet_ "f" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
  utuple_ [app_ (var_ "f") (int_ 2), app_ (var_ "f") (float_ 2.5)]
]) in
let result = mm seqPoly in
let expected = preprocess (bindall_ [
  let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
  let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
  let_ "fInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (app_ (var_ "gInt") (var_ "x"))),
  let_ "fFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (app_ (var_ "gFloat") (var_ "x"))),
  utuple_ [app_ (var_ "fInt") (int_ 2), app_ (var_ "fFloat") (float_ 2.5)]
]) in
utest isMonomorphic seqPoly with false in
utest isMonomorphic result with true in -- fails
utest isMonomorphic expected with true in
utest result with expected using eqExpr in -- fails

let nestedPoly = preprocess (bindall_ [
  ulet_ "f" (ulam_ "g" (ulam_ "s" (bindall_ [
    ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
    map_ (var_ "h") (var_ "s")
  ]))),
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
  utuple_ [
    appf2_ (var_ "f") (var_ "addOne") (seq_ [int_ 2]),
    appf2_ (var_ "f") (var_ "addHalf") (seq_ [float_ 2.5])]
]) in
let result = mm nestedPoly in
let expected = preprocess (bindall_ [
  let_ "fInt"
    (tyarrows_ [tyarrow_ tyint_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
    (ulam_ "g" (ulam_ "s" (bindall_ [
      ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
      map_ (var_ "h") (var_ "s")
  ]))),
  let_ "fFloat"
    (tyarrows_ [tyarrow_ tyfloat_ tyfloat_, tyseq_ tyfloat_, tyseq_ tyfloat_])
    (ulam_ "g" (ulam_ "s" (bindall_ [
      ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
      map_ (var_ "h") (var_ "s")
  ]))),
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
  utuple_ [
    appf2_ (var_ "fInt") (var_ "addOne") (seq_ [int_ 2]),
    appf2_ (var_ "fFloat") (var_ "addHalf") (seq_ [float_ 2.5])]
]) in
utest isMonomorphic nestedPoly with false in
utest isMonomorphic result with true in -- fails
utest isMonomorphic expected with true in
utest result with expected using eqExpr in -- fails

let innerPoly = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (ulam_ "y" (bindall_ [
    ulet_ "g" (ulam_ "z" (var_ "z")),
    utuple_ [app_ (var_ "g") (var_ "x"), app_ (var_ "g") (var_ "y")]
  ]))),
  appf2_ (var_ "f") (int_ 2) (float_ 2.5)
]) in
let result = mm innerPoly in
let expected = preprocess (bindall_ [
  let_ "f" (tyarrows_ [tyint_, tyfloat_, tytuple_ [tyint_, tyfloat_]])
    (ulam_ "x" (ulam_ "y" (bindall_ [
      let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "z" (var_ "z")),
      let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "z" (var_ "z")),
      utuple_ [app_ (var_ "gInt") (var_ "x"), app_ (var_ "gFloat") (var_ "y")]
  ]))),
  appf2_ (var_ "f") (int_ 2) (float_ 2.5)
]) in
utest isMonomorphic innerPoly with false in
utest isMonomorphic result with true in -- fails
utest isMonomorphic expected with true in
utest result with expected using eqExpr in -- fails

let higherOrderPoly = preprocess (bindall_ [
  let_ "g" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a"))) (ulam_ "x" (var_ "x")),
  ulet_ "f" (lam_ "g" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")))
    (ulam_ "x" (ulam_ "y" (bindall_ [
      ulet_ "a" (app_ (var_ "g") (var_ "x")),
      ulet_ "b" (app_ (var_ "g") (var_ "y")),
      utuple_ [var_ "a", var_ "b"]
  ])))),
  ulet_ "x1" (int_ 2),
  ulet_ "x2" (float_ 2.5),
  ulet_ "y" (appf3_ (var_ "f") (freeze_ (var_ "g")) (var_ "x1") (var_ "x2"))
]) in
let result = mm higherOrderPoly in
let expected = preprocess (bindall_ [
  let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
  let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
  ulet_ "x1" (int_ 2),
  ulet_ "x2" (float_ 2.5),
  let_ "fIntFloat"
    (tyarrows_ [tyarrow_ tyint_ tyint_, tyarrow_ tyfloat_ tyfloat_, tyint_, tyfloat_, tytuple_ [tyint_, tyfloat_]])
    (ulam_ "gInt" (ulam_ "gFloat" (ulam_ "x" (ulam_ "y" (bindall_ [
      ulet_ "a" (app_ (var_ "gInt") (var_ "x")),
      ulet_ "b" (app_ (var_ "gFloat") (var_ "y")),
      utuple_ [var_ "a", var_ "b"]
  ]))))),
  ulet_ "y" (appf4_ (var_ "fIntFloat") (var_ "gInt") (var_ "gFloat") (var_ "x1") (var_ "x2"))
]) in
utest isMonomorphic higherOrderPoly with false in
utest isMonomorphic result with true in -- fails
utest isMonomorphic expected with true in
utest result with expected using eqExpr in -- fails

let polyVariant = preprocess (bindall_ [
  type_ "Option" ["a"] (tyvariant_ []),
  condef_ "Some" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyapp_ (tycon_ "Option") (tyvar_ "a")))),
  condef_ "None" (tyall_ "a" (tyarrow_ (tytuple_ []) (tyapp_ (tycon_ "Option") (tyvar_ "a")))),
  ulet_ "isSome" (ulam_ "o" (
    match_ (var_ "o") (pcon_ "Some" pvarw_) true_ false_)),
  utuple_ [
    app_ (var_ "isSome") (conapp_ "Some" (int_ 2)),
    app_ (var_ "isSome") (conapp_ "Some" (float_ 2.5)),
    app_ (var_ "isSome") (conapp_ "None" uunit_)
  ]
]) in
let result = mm polyVariant in
-- NOTE(larshum, 2023-06-28): When type parameters are not used, they are set
-- to unknown. In this case, when constructing a None, we don't use the type
-- parameter. The monomorphization should replace it with the Unit type (empty
-- record).
let expected = preprocess (bindall_ [
  type_ "OptionInt" [] (tyvariant_ []),
  condef_ "SomeInt" (tyarrow_ tyint_ (tycon_ "OptionInt")),
  condef_ "NoneInt" (tyarrow_ (tytuple_ []) (tycon_ "OptionInt")),
  let_ "isSomeInt" (tyarrow_ (tycon_ "OptionInt") tybool_)
    (ulam_ "o" (
      match_ (var_ "o") (pcon_ "SomeInt" pvarw_) true_ false_)),
  type_ "OptionFloat" [] (tyvariant_ []),
  condef_ "SomeFloat" (tyarrow_ tyfloat_ (tycon_ "OptionFloat")),
  condef_ "NoneFloat" (tyarrow_ (tytuple_ []) (tycon_ "OptionFloat")),
  let_ "isSomeFloat" (tyarrow_ (tycon_ "OptionFloat") tybool_)
    (ulam_ "o" (
      match_ (var_ "o") (pcon_ "SomeFloat" pvarw_) true_ false_)),
  type_ "OptionUnit" [] (tyvariant_ []),
  condef_ "SomeUnit" (tyarrow_ tyunit_ (tycon_ "OptionUnit")),
  condef_ "NoneUnit" (tyarrow_ (tytuple_ []) (tycon_ "OptionUnit")),
  let_ "isSomeUnit" (tyarrow_ (tycon_ "OptionUnit") tybool_)
    (ulam_ "o" (
      match_ (var_ "o") (pcon_ "SomeUnit" pvarw_) true_ false_)),
  utuple_ [
    app_ (var_ "isSomeInt") (conapp_ "SomeInt" (int_ 2)),
    app_ (var_ "isSomeFloat") (conapp_ "SomeFloat" (float_ 2.5)),
    app_ (var_ "isSomeUnit") (conapp_ "NoneUnit" uunit_)
  ]
]) in
utest isMonomorphic polyVariant with false in
utest isMonomorphic result with true in -- fails
utest isMonomorphic expected with true in
utest mexprToString result with mexprToString expected using eqString in -- fails

()
