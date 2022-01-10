-- Performs a well-formed check of a PMExpr AST. This ensures that:
-- * Sequences do not contain elements of functional type.
-- * The accumulator of a foldl and parallelReduce is not of functional type.
-- * The accumulator and the sequence elements of parallelReduce have the same
--   type.
--
-- These type checks assume that the provided AST is valid according to the
-- MExpr type checking.

include "pmexpr/ast.mc"

lang PMExprWellFormed = PMExprAst
  syn PMExprWellFormedError =
  | FunctionInArray Info
  | FunctionFromIf Info
  | FunctionFromCreate Info
  | FunctionFromFold Info
  | FunctionFromMap Info
  | ParallelReduceType Info

  sem pprintPMExprWellFormedError =
  | FunctionInArray info ->
    infoErrorString info "Cannot accelerate arrays containing functions"
  | FunctionFromIf info ->
    infoErrorString info (join ["Cannot accelerate conditional expressions ",
                                "where the result is a higher-order function"])
  | FunctionFromCreate info ->
    infoErrorString info (join ["Cannot accelerate create where the result ",
                                "is a sequence of higher-order functions"])
  | FunctionFromFold info ->
    infoErrorString info
      "Cannot accelerate folds with higher-order function accumulator"
  | FunctionFromMap info ->
    infoErrorString info (join ["Cannot accelerate map where the result is a ",
                                "sequence of higher-order functions"])
  | ParallelReduceType info ->
    infoErrorString info (join ["Cannot accelerate parallelReduce where the ",
                                "accumulator and sequence elements have ",
                                "different types"])

  sem containsFunctionType =
  | t -> containsFunctionTypeH false t

  sem containsFunctionTypeH (acc : Bool) =
  | TyArrow _ -> true
  | t -> if acc then acc else sfold_Type_Type containsFunctionTypeH acc t

  sem pmexprWellFormedType (info : Info) (acc : [PMExprWellFormedError]) =
  | TySeq t ->
    -- NOTE(larshum, 2021-12-13): An array may not contain elements of a
    -- functional type.
    if containsFunctionType t.ty then
      cons (FunctionInArray info) acc
    else acc
  | t -> sfold_Type_Type (pmexprWellFormedType info) acc t

  sem pmexprWellFormedExpr (acc : [PMExprWellFormedError]) =
  | TmLet t ->
    let acc = pmexprWellFormedType t.info acc t.tyBody in
    let acc = pmexprWellFormedExpr acc t.body in
    let acc = pmexprWellFormedExpr acc t.inexpr in
    pmexprWellFormedType t.info acc t.ty
  | TmMatch t ->
    -- NOTE(larshum, 2021-12-13): An if-expression may not result in a
    -- functional type.
    if containsFunctionType t.ty then
      cons (FunctionFromIf t.info) acc
    else sfold_Expr_Expr pmexprWellFormedExpr acc t
  | TmConst ({val = CCreate _} & t) ->
    -- NOTE(larshum, 2021-12-13): A create expression may not produce a
    -- sequence with elements of functional type.
    match t.ty with TyArrow {to = TyArrow {to = TySeq {ty = TyArrow _}}} then
      cons (FunctionFromCreate t.info) acc
    else sfold_Expr_Expr pmexprWellFormed acc (TmConst t)
  | TmConst ({val = CFoldl _} & t) ->
    -- NOTE(larshum, 2021-12-13): A fold-expression may not have an accumulator
    -- of functional type.
    match t.ty with TyArrow {to = TyArrow {from = TyArrow _}} then
      cons (FunctionFromFold t.info) acc
    else sfold_Expr_Expr pmexprWellFormed acc (TmConst t)
  | TmConst ({val = CMap _} & t) ->
    -- NOTE(larshum, 2021-12-13): A map-expression may not produce a sequence
    -- containing elements of functional type.
    match t.ty with TyArrow {to = TyArrow {to = TySeq {ty = TyArrow _}}} then
      cons (FunctionFromMap t.info) acc
    else sfold_Expr_Expr pmexprWellFormed acc (TmConst t)
  | TmParallelReduce t ->
    -- NOTE(larshum, 2021-12-13): A parallel reduce requires that the
    -- accumulator has the same type as the elements of the provided sequence.
    -- In addition, this type must not be a functional type.
    match t.ty with TyArrow _ then
      cons (FunctionFromFold t.info) acc
    else
      let accTy = tyTm t.ne in
      let elemTy =
        match tyTm t.as with TySeq {ty = ty} then ty
        else infoErrorExit (infoTm t.as) "Invalid type of sequence argument" in
      if eqType accTy elemTy then acc
      else cons (ParallelReduceType t.info) acc
  | t ->
    let acc = pmexprWellFormedType (infoTm t) acc (tyTm t) in
    sfold_Expr_Expr pmexprWellFormedExpr acc t

  sem pmexprWellFormedGetErrors =
  | t -> reverse (pmexprWellFormedExpr [] t)

  sem pmexprWellFormed =
  | t ->
    let errors = pmexprWellFormedGetErrors t in
    if null errors then ()
    else
      let msg = strJoin "\n" (map pprintPMExprWellFormedError errors) in
      error (join ["Well-formedness check failed\n", msg])
end

mexpr

use PMExprWellFormed in

let i = Info {filename = "", row1 = 0, row2 = 0, col1 = 0, col2 = 0} in
let arrowType = TyArrow {from = tyint_, to = tyint_, info = i} in

let functionInArray = TmSeq {
  tms = [withType arrowType (ulam_ "x" (var_ "x"))],
  ty = tyseq_ arrowType, info = i} in
utest pmexprWellFormedGetErrors functionInArray with [FunctionInArray i] in

let functionFromIf =
  withInfo i
    (withType arrowType
      (if_ true_ (ulam_ "x" (var_ "x")) (ulam_ "x" (int_ 1)))) in
utest pmexprWellFormedGetErrors functionFromIf with [FunctionFromIf i] in

let createType = tyarrows_ [tyint_, tyarrow_ tyint_ arrowType, tyseq_ arrowType] in
let createTerm = withInfo i (const_ createType (CCreate ())) in
let createFunctionResult =
  appSeq_ createTerm [int_ 2, var_ "f"] in
utest pmexprWellFormedGetErrors createFunctionResult with [FunctionFromCreate i] in

let foldType =
  let ty = arrowType in
  tyarrows_ [tyarrows_ [ty, ty, ty], ty, tyseq_ ty] in
let foldTerm = withInfo i (const_ foldType (CFoldl ())) in
let functionFoldParameter =
  appSeq_ foldTerm [var_ "f", ulam_ "x" (var_ "x"), seq_ []] in
utest pmexprWellFormedGetErrors functionFoldParameter with [FunctionFromFold i] in

let mapType =
  tyarrows_ [tyarrow_ tyint_ arrowType, tyseq_ tyint_, tyseq_ arrowType] in
let mapTerm = withInfo i (const_ mapType (CMap ())) in
let mapFunctionResult =
  appSeq_ mapTerm [var_ "f", seq_ [int_ 1]] in
utest pmexprWellFormedGetErrors mapFunctionResult with [FunctionFromMap i] in

let functionInArrayVar = withInfo i (withType (tyseq_ arrowType) (var_ "x")) in
utest pmexprWellFormedGetErrors functionInArrayVar with [FunctionInArray i] in

let sumf = ulam_ "a" (ulam_ "b" (addi_ (var_ "a") (var_ "b"))) in
let sumFold = foldl_ sumf (int_ 0) (seq_ [int_ 1, int_ 2, int_ 3]) in
utest pmexprWellFormedGetErrors sumFold with [] in

utest pmexprWellFormedGetErrors foldTerm with [FunctionFromFold i] in

let parallelReduceFunctionType = TmParallelReduce {
  f = var_ "f", ne = ulam_ "x" (var_ "x"), as = seq_ [],
  ty = foldType, info = i} in
utest pmexprWellFormedGetErrors parallelReduceFunctionType
with [FunctionFromFold i] in

let parallelReduceTypeMismatch = TmParallelReduce {
  f = var_ "f", ne = withType tyint_ (var_ "ne"),
  as = withType (tyseq_ tyfloat_) (seq_ []),
  ty = tyunknown_, info = i} in
utest pmexprWellFormedGetErrors parallelReduceTypeMismatch
with [ParallelReduceType i] in

()
