include "pmexpr/well-formed.mc"

lang FutharkWellFormed = WellFormed + PMExprAst
  syn WFError =
  | FutharkFunctionInArray Info
  | FutharkFunctionFromIf Info
  | FutharkFunctionFromCreate Info
  | FutharkFunctionFromFold Info
  | FutharkFunctionFromMap Info
  | FutharkRecLet Info

  sem wellFormednessBackendName =
  | () -> "Futhark"

  sem pprintWellFormedError =
  | FutharkFunctionInArray info ->
    (info, "Sequences of function-type elements are not supported")
  | FutharkFunctionFromCreate info ->
    (info, "Creating sequences of functions is not supported")
  | FutharkFunctionFromMap info ->
    (info, "Map functions producing functions is not supported")
  | FutharkFunctionFromIf info ->
    (info, "Conditionals returning functions are not supported")
  | FutharkFunctionFromFold info ->
    (info, "Folds with accumulator of function type are not supported")
  | FutharkRecLet info ->
    (info, "Recursive let-expressions are not supported")

  sem containsFunctionType : Bool -> Type -> Bool
  sem containsFunctionType acc =
  | TyArrow _ -> true
  | t -> if acc then acc else sfold_Type_Type containsFunctionType acc t

  sem futharkWellFormedType : Info -> [WFError] -> Type -> [WFError]
  sem futharkWellFormedType info acc =
  | TySeq t ->
    -- NOTE(larshum, 2021-12-13): An array may not contain elements of a
    -- functional type.
    if containsFunctionType false t.ty then
      cons (FutharkFunctionInArray info) acc
    else acc
  | t -> sfold_Type_Type (futharkWellFormedType info) acc t

  sem futharkWellFormedExpr : [WFError] -> Expr -> [WFError]
  sem futharkWellFormedExpr acc =
  | TmLet t ->
    let acc = futharkWellFormedExpr acc t.body in
    let acc = futharkWellFormedExpr acc t.inexpr in
    futharkWellFormedType t.info acc t.ty
  | TmRecLets t ->
    let acc = cons (FutharkRecLet t.info) acc in
    futharkWellFormedExpr acc t.inexpr
  | TmMatch t ->
    -- NOTE(larshum, 2021-12-13): An if-expression may not result in a
    -- functional type.
    if containsFunctionType false t.ty then
      cons (FutharkFunctionFromIf t.info) acc
    else sfold_Expr_Expr futharkWellFormedExpr acc (TmMatch t)
  | TmConst ({val = CCreate _} & t) ->
    -- NOTE(larshum, 2021-12-13): A create expression may not produce a
    -- sequence with elements of functional type.
    match t.ty with TyArrow {to = TyArrow {to = TySeq {ty = TyArrow _}}} then
      cons (FutharkFunctionFromCreate t.info) acc
    else sfold_Expr_Expr futharkWellFormedExpr acc (TmConst t)
  | TmConst ({val = CFoldl _} & t) ->
    -- NOTE(larshum, 2021-12-13): A fold-expression may not have an accumulator
    -- of functional type.
    match t.ty with TyArrow {to = TyArrow {from = TyArrow _}} then
      cons (FutharkFunctionFromFold t.info) acc
    else sfold_Expr_Expr futharkWellFormedExpr acc (TmConst t)
  | TmConst ({val = CMap _} & t) ->
    -- NOTE(larshum, 2021-12-13): A map-expression may not produce a sequence
    -- containing elements of functional type.
    match t.ty with TyArrow {to = TyArrow {to = TySeq {ty = TyArrow _}}} then
      cons (FutharkFunctionFromMap t.info) acc
    else sfold_Expr_Expr futharkWellFormedExpr acc (TmConst t)
  | TmParallelReduce t ->
    -- NOTE(larshum, 2021-12-13): A parallel reduce requires that the
    -- accumulator has the same type as the elements of the provided sequence.
    -- In addition, this type must not be a functional type.
    match t.ty with TyArrow _ then
      cons (FutharkFunctionFromFold t.info) acc
    else sfold_Expr_Expr futharkWellFormedExpr acc (TmParallelReduce t)
  | t ->
    let info = infoTm t in
    let acc = futharkWellFormedType info acc (tyTm t) in
    let acc = sfold_Expr_Type (futharkWellFormedType info) acc t in
    sfold_Expr_Expr futharkWellFormedExpr acc t

  sem wellFormedExprH : [WFError] -> Expr -> [WFError]
  sem wellFormedExprH acc =
  | t -> futharkWellFormedExpr acc t

  sem wellFormedTypeH : [WFError] -> Type -> [WFError]
  sem wellFormedTypeH acc =
  | t -> futharkWellFormedType (NoInfo ()) acc t
end

mexpr

use FutharkWellFormed in

let i = Info {filename = "", row1 = 0, row2 = 0, col1 = 0, col2 = 0} in
let arrowType = TyArrow {from = tyint_, to = tyint_, info = i} in

let functionInArray = TmSeq {
  tms = [withType arrowType (ulam_ "x" (var_ "x"))],
  ty = tyseq_ arrowType, info = i} in
utest wellFormedExpr functionInArray with [FutharkFunctionInArray i] in

let functionFromIf =
  withInfo i
    (withType arrowType
      (if_ true_ (ulam_ "x" (var_ "x")) (ulam_ "x" (int_ 1)))) in
utest wellFormedExpr functionFromIf with [FutharkFunctionFromIf i] in

let createType = tyarrows_ [tyint_, tyarrow_ tyint_ arrowType, tyseq_ arrowType] in
let createTerm = withInfo i (const_ createType (CCreate ())) in
let createFunctionResult =
  appSeq_ createTerm [int_ 2, var_ "f"] in
utest wellFormedExpr createFunctionResult with [FutharkFunctionFromCreate i] in

let foldType =
  let ty = arrowType in
  tyarrows_ [tyarrows_ [ty, ty, ty], ty, tyseq_ ty] in
let foldTerm = withInfo i (const_ foldType (CFoldl ())) in
let functionFoldParameter =
  appSeq_ foldTerm [var_ "f", ulam_ "x" (var_ "x"), seq_ []] in
utest wellFormedExpr functionFoldParameter with [FutharkFunctionFromFold i] in

let mapType =
  tyarrows_ [tyarrow_ tyint_ arrowType, tyseq_ tyint_, tyseq_ arrowType] in
let mapTerm = withInfo i (const_ mapType (CMap ())) in
let mapFunctionResult =
  appSeq_ mapTerm [var_ "f", seq_ [int_ 1]] in
utest wellFormedExpr mapFunctionResult with [FutharkFunctionFromMap i] in

let functionInArrayVar = withInfo i (withType (tyseq_ arrowType) (var_ "x")) in
utest wellFormedExpr functionInArrayVar with [FutharkFunctionInArray i] in

let sumf = ulam_ "a" (ulam_ "b" (addi_ (var_ "a") (var_ "b"))) in
let sumFold = foldl_ sumf (int_ 0) (seq_ [int_ 1, int_ 2, int_ 3]) in
utest wellFormedExpr sumFold with [] in

utest wellFormedExpr foldTerm with [FutharkFunctionFromFold i] in

let parallelReduceFunctionType = TmParallelReduce {
  f = var_ "f", ne = ulam_ "x" (var_ "x"), as = seq_ [],
  ty = foldType, info = i} in
utest wellFormedExpr parallelReduceFunctionType
with [FutharkFunctionFromFold i] in

()
