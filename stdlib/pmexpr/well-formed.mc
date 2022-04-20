-- Performs a well-formed check of a PMExpr AST. This ensures that:
-- * Sequences do not contain elements of functional type.
-- * The accumulator of a foldl and parallelReduce is not of functional type.
-- * The accumulator and the sequence elements of parallelReduce have the same
--   type.
--
-- These type checks assume that the provided AST is valid according to the
-- MExpr type checking.

include "pmexpr/ast.mc"

-- An extensible language fragment for defining well-formedness rules on
-- expressions.
lang WellFormed
  syn WellFormedError =

  -- Translates a well-formedness error node to a string by pretty-printing it.
  sem pprintWellFormedError =

  -- Defines the well-formedness relation for an expression. A well-formed
  -- expression will return the accumulated sequence of errors, while one that
  -- is ill-formed will return the accumulator extended with errors
  -- corresponding to the failed well-formedness checks.
  sem wellFormedExprH (acc : [WellFormedError]) =

  -- Checks well-formedness within an AST node. The result is a possibly empty
  -- sequence of well-formedness errors.
  sem wellFormedExpr =
  | t -> reverse (wellFormedExprH [] t)

  sem wellFormedTypeH (acc : [WellFormedError]) =

  sem wellFormedType =
  | t -> reverse (wellFormedTypeH [] t)

  sem wellFormed =
  | t ->
    let errors = wellFormedExpr t in
    if null errors then ()
    else
      let msg = strJoin "\n" (map pprintWellFormedError errors) in
      error (join ["Well-formedness check failed\n", msg])
end

-- Defines the well-formedness rules for the PMExpr AST, which are shared by
-- all accelerate backends.
lang PMExprWellFormed = WellFormed + PMExprAst
  syn WellFormedError =
  | PMExprFunctionInArray Info
  | PMExprFunctionFromIf Info
  | PMExprFunctionFromCreate Info
  | PMExprFunctionFromFold Info
  | PMExprFunctionFromMap Info
  | PMExprParallelReduceType Info

  sem pprintWellFormedError =
  | PMExprFunctionInArray info ->
    infoErrorString info "Cannot accelerate arrays containing functions"
  | PMExprFunctionFromIf info ->
    infoErrorString info (join ["Cannot accelerate conditional expressions ",
                                "where the result is a higher-order function"])
  | PMExprFunctionFromCreate info ->
    infoErrorString info (join ["Cannot accelerate create where the result ",
                                "is a sequence of higher-order functions"])
  | PMExprFunctionFromFold info ->
    infoErrorString info
      "Cannot accelerate folds with higher-order function accumulator"
  | PMExprFunctionFromMap info ->
    infoErrorString info (join ["Cannot accelerate map where the result is a ",
                                "sequence of higher-order functions"])
  | PMExprParallelReduceType info ->
    infoErrorString info (join ["Cannot accelerate parallelReduce where the ",
                                "accumulator and sequence elements have ",
                                "different types"])

  sem containsFunctionType =
  | t -> containsFunctionTypeH false t

  sem containsFunctionTypeH (acc : Bool) =
  | TyArrow _ -> true
  | t -> if acc then acc else sfold_Type_Type containsFunctionTypeH acc t

  sem pmexprWellFormedType (acc : [WellFormedError]) =
  | TySeq t ->
    -- NOTE(larshum, 2021-12-13): An array may not contain elements of a
    -- functional type.
    if containsFunctionType t.ty then
      cons (PMExprFunctionInArray (infoTy t.ty)) acc
    else acc
  | t -> sfold_Type_Type pmexprWellFormedType acc t

  sem pmexprWellFormedExpr (acc : [WellFormedError]) =
  | TmLet t ->
    let acc = pmexprWellFormedType acc t.tyBody in
    let acc = pmexprWellFormedExpr acc t.body in
    let acc = pmexprWellFormedExpr acc t.inexpr in
    pmexprWellFormedType acc t.ty
  | TmMatch t ->
    -- NOTE(larshum, 2021-12-13): An if-expression may not result in a
    -- functional type.
    if containsFunctionType t.ty then
      cons (PMExprFunctionFromIf t.info) acc
    else sfold_Expr_Expr pmexprWellFormedExpr acc (TmMatch t)
  | TmConst ({val = CCreate _} & t) ->
    -- NOTE(larshum, 2021-12-13): A create expression may not produce a
    -- sequence with elements of functional type.
    match t.ty with TyArrow {to = TyArrow {to = TySeq {ty = TyArrow _}}} then
      cons (PMExprFunctionFromCreate t.info) acc
    else sfold_Expr_Expr pmexprWellFormedExpr acc (TmConst t)
  | TmConst ({val = CFoldl _} & t) ->
    -- NOTE(larshum, 2021-12-13): A fold-expression may not have an accumulator
    -- of functional type.
    match t.ty with TyArrow {to = TyArrow {from = TyArrow _}} then
      cons (PMExprFunctionFromFold t.info) acc
    else sfold_Expr_Expr pmexprWellFormedExpr acc (TmConst t)
  | TmConst ({val = CMap _} & t) ->
    -- NOTE(larshum, 2021-12-13): A map-expression may not produce a sequence
    -- containing elements of functional type.
    match t.ty with TyArrow {to = TyArrow {to = TySeq {ty = TyArrow _}}} then
      cons (PMExprFunctionFromMap t.info) acc
    else sfold_Expr_Expr pmexprWellFormedExpr acc (TmConst t)
  | TmParallelReduce t ->
    -- NOTE(larshum, 2021-12-13): A parallel reduce requires that the
    -- accumulator has the same type as the elements of the provided sequence.
    -- In addition, this type must not be a functional type.
    match t.ty with TyArrow _ then
      cons (PMExprFunctionFromFold t.info) acc
    else
      let accTy = tyTm t.ne in
      let elemTy =
        match tyTm t.as with TySeq {ty = ty} then ty
        else infoErrorExit (infoTm t.as) "Invalid type of sequence argument" in
      if eqType accTy elemTy then acc
      else cons (PMExprParallelReduceType t.info) acc
  | t ->
    let info = infoTm t in
    let acc = pmexprWellFormedType acc (tyTm t) in
    let acc = sfold_Expr_Type pmexprWellFormedType acc t in
    sfold_Expr_Expr pmexprWellFormedExpr acc t

  sem wellFormedExprH (acc : [WellFormedError]) =
  | t -> pmexprWellFormedExpr acc t

  sem wellFormedTypeH (acc : [WellFormedError]) =
  | t -> pmexprWellFormedType acc t
end

mexpr

use PMExprWellFormed in

let i = Info {filename = "", row1 = 0, row2 = 0, col1 = 0, col2 = 0} in
let arrowType = TyArrow {from = tyint_, to = tyint_, info = i} in

let functionInArray = TmSeq {
  tms = [withType arrowType (ulam_ "x" (var_ "x"))],
  ty = tyseq_ arrowType, info = i} in
utest wellFormedExpr functionInArray with [PMExprFunctionInArray i] in

let functionFromIf =
  withInfo i
    (withType arrowType
      (if_ true_ (ulam_ "x" (var_ "x")) (ulam_ "x" (int_ 1)))) in
utest wellFormedExpr functionFromIf with [PMExprFunctionFromIf i] in

let createType = tyarrows_ [tyint_, tyarrow_ tyint_ arrowType, tyseq_ arrowType] in
let createTerm = withInfo i (const_ createType (CCreate ())) in
let createFunctionResult =
  appSeq_ createTerm [int_ 2, var_ "f"] in
utest wellFormedExpr createFunctionResult with [PMExprFunctionFromCreate i] in

let foldType =
  let ty = arrowType in
  tyarrows_ [tyarrows_ [ty, ty, ty], ty, tyseq_ ty] in
let foldTerm = withInfo i (const_ foldType (CFoldl ())) in
let functionFoldParameter =
  appSeq_ foldTerm [var_ "f", ulam_ "x" (var_ "x"), seq_ []] in
utest wellFormedExpr functionFoldParameter with [PMExprFunctionFromFold i] in

let mapType =
  tyarrows_ [tyarrow_ tyint_ arrowType, tyseq_ tyint_, tyseq_ arrowType] in
let mapTerm = withInfo i (const_ mapType (CMap ())) in
let mapFunctionResult =
  appSeq_ mapTerm [var_ "f", seq_ [int_ 1]] in
utest wellFormedExpr mapFunctionResult with [PMExprFunctionFromMap i] in

let functionInArrayVar = withInfo i (withType (tyseq_ arrowType) (var_ "x")) in
utest wellFormedExpr functionInArrayVar with [PMExprFunctionInArray i] in

let sumf = ulam_ "a" (ulam_ "b" (addi_ (var_ "a") (var_ "b"))) in
let sumFold = foldl_ sumf (int_ 0) (seq_ [int_ 1, int_ 2, int_ 3]) in
utest wellFormedExpr sumFold with [] in

utest wellFormedExpr foldTerm with [PMExprFunctionFromFold i] in

let parallelReduceFunctionType = TmParallelReduce {
  f = var_ "f", ne = ulam_ "x" (var_ "x"), as = seq_ [],
  ty = foldType, info = i} in
utest wellFormedExpr parallelReduceFunctionType
with [PMExprFunctionFromFold i] in

let parallelReduceTypeMismatch = TmParallelReduce {
  f = var_ "f", ne = withType tyint_ (var_ "ne"),
  as = withType (tyseq_ tyfloat_) (seq_ []),
  ty = tyunknown_, info = i} in
utest wellFormedExpr parallelReduceTypeMismatch
with [PMExprParallelReduceType i] in

()
