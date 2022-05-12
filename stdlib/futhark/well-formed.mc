include "pmexpr/well-formed.mc"

lang FutharkWellFormed = WellFormed + PMExprAst
  syn WellFormedError =
  | FutharkFunctionInArray Info
  | FutharkFunctionFromIf Info
  | FutharkFunctionFromCreate Info
  | FutharkFunctionFromFold Info
  | FutharkFunctionFromMap Info
  | FutharkRecLet Info

  sem pprintWellFormedError =
  | FutharkFunctionInArray info ->
    infoErrorString info "Cannot accelerate arrays containing functions"
  | FutharkFunctionFromIf info ->
    infoErrorString info (join ["Cannot accelerate conditional expressions ",
                                "where the result is a higher-order function"])
  | FutharkFunctionFromCreate info ->
    infoErrorString info (join ["Cannot accelerate create where the result ",
                                "is a sequence of higher-order functions"])
  | FutharkFunctionFromFold info ->
    infoErrorString info
      "Cannot accelerate folds with higher-order function accumulator"
  | FutharkFunctionFromMap info ->
    infoErrorString info (join ["Cannot accelerate map where the result is a ",
                                "sequence of higher-order functions"])
  | FutharkRecLet info ->
    infoErrorString info (join ["Cannot accelerate recursive let-expressions"])

  sem containsFunctionType =
  | t -> containsFunctionTypeH false t

  sem containsFunctionTypeH (acc : Bool) =
  | TyArrow _ -> true
  | t -> if acc then acc else sfold_Type_Type containsFunctionTypeH acc t

  sem futharkWellFormedType (acc : [WellFormedError]) =
  | TySeq t ->
    -- NOTE(larshum, 2021-12-13): An array may not contain elements of a
    -- functional type.
    if containsFunctionType t.ty then
      cons (FutharkFunctionInArray (infoTy t.ty)) acc
    else acc
  | t -> sfold_Type_Type futharkWellFormedType acc t

  sem futharkWellFormedExpr (acc : [WellFormedError]) =
  | TmLet t ->
    let acc = futharkWellFormedType acc t.tyBody in
    let acc = futharkWellFormedExpr acc t.body in
    let acc = futharkWellFormedExpr acc t.inexpr in
    futharkWellFormedType acc t.ty
  | TmRecLets t -> cons (FutharkRecLet t.info) acc
  | TmMatch t ->
    -- NOTE(larshum, 2021-12-13): An if-expression may not result in a
    -- functional type.
    if containsFunctionType t.ty then
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
    let acc = futharkWellFormedType acc (tyTm t) in
    let acc = sfold_Expr_Type futharkWellFormedType acc t in
    sfold_Expr_Expr futharkWellFormedExpr acc t

  sem wellFormedExprH (acc : [WellFormedError]) =
  | t -> futharkWellFormedExpr acc t

  sem wellFormedTypeH (acc : [WellFormedError]) =
  | t -> futharkWellFormedType acc t
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
