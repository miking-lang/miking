include "pmexpr/utils.mc"
include "pmexpr/well-formed.mc"
include "pmexpr/pprint.mc"

lang FutharkWellFormed = WellFormed + PMExprAst
  syn WFError =
  | FutharkFunctionInArray Type
  | FutharkFunctionInRecord Type
  | FutharkFunctionFromIf Expr
  | FutharkFunctionFromCreate Expr
  | FutharkFunctionFromFold Expr
  | FutharkFunctionFromMap Expr
  | FutharkRecLet Expr
  | FutharkExprError Expr
  | FutharkTypeError Type
  | FutharkPatternError Pat
  | FutharkConstantError Info

  sem wellFormednessBackendName =
  | () -> "Futhark"

  sem pprintWellFormedError =
  | FutharkFunctionInArray ty ->
    (infoTy ty, "Sequences of function-type elements are not supported")
  | FutharkFunctionInRecord ty ->
    (infoTy ty, "Records containing function-type fields are not supported")
  | FutharkFunctionFromCreate expr ->
    (infoTm expr, "Creating sequences of functions is not supported")
  | FutharkFunctionFromMap expr ->
    (infoTm expr, "Map functions producing functions is not supported")
  | FutharkFunctionFromIf expr ->
    (infoTm expr, "Conditionals returning functions are not supported")
  | FutharkFunctionFromFold expr ->
    (infoTm expr, "Folds with accumulator of function type are not supported")
  | FutharkRecLet expr ->
    (infoTm expr, "Recursive let-expressions are not supported")
  | FutharkExprError expr ->
    (infoTm expr, "Expression is not supported")
  | FutharkTypeError ty ->
    (infoTy ty, "Type is not supported")
  | FutharkPatternError pat ->
    (infoPat pat, "Pattern is not supported")
  | FutharkConstantError info ->
    (info, "Constant is not supported")

  sem futharkWellFormedExpr : [WFError] -> Expr -> [WFError]
  sem futharkWellFormedExpr acc =
  | e ->
    let acc = futharkWellFormedType acc (tyTm e) in
    futharkWellFormedExprH acc e

  sem futharkWellFormedExprH : [WFError] -> Expr -> [WFError]
  sem futharkWellFormedExprH acc =
  | TmVar t -> acc
  | (TmApp t) & app ->
    let wellFormedApp = lam fun. lam args.
      let acc = futharkWellFormedExpr acc fun in
      foldl futharkWellFormedExpr acc args in
    match collectAppArguments app with (fun, args) in
    match fun with TmConst {val = CFoldl _, ty = ty} then
      match ty with TyArrow {to = TyArrow {from = TyArrow _}} then
        cons (FutharkFunctionFromFold app) acc
      else wellFormedApp fun args
    else wellFormedApp fun args
  | TmLam t -> futharkWellFormedExpr acc t.body
  | TmLet t ->
    let acc = futharkWellFormedExpr acc t.body in
    futharkWellFormedExpr acc t.inexpr
  | TmRecLets t ->
    let acc = cons (FutharkRecLet (TmRecLets t)) acc in
    futharkWellFormedExpr acc t.inexpr
  | TmConst t ->
    if isFutharkSupportedConstant t.val then acc
    else cons (FutharkConstantError t.info) acc
  | TmMatch t ->
    let acc = futharkWellFormedExpr acc t.target in
    let acc = futharkWellFormedPattern acc t.pat in
    let acc = futharkWellFormedExpr acc t.thn in
    let acc = futharkWellFormedExpr acc t.els in
    match t.ty with TyArrow _ then cons (FutharkFunctionFromIf (TmMatch t)) acc
    else acc
  | TmNever _ -> acc
  | TmRecord t ->
    mapFoldWithKey
      (lam acc. lam. lam expr. futharkWellFormedExpr acc expr)
      acc t.bindings
  | TmRecordUpdate t ->
    let acc = futharkWellFormedExpr acc t.rec in
    futharkWellFormedExpr acc t.value
  | TmSeq {tms = tms} -> foldl futharkWellFormedExpr acc tms
  | TmExt t -> futharkWellFormedExpr acc t.inexpr
  | TmType t ->
    let acc = futharkWellFormedType acc t.tyIdent in
    futharkWellFormedExpr acc t.inexpr
  | TmFlatten t -> futharkWellFormedExpr acc t.e
  | TmMap2 t ->
    let acc = futharkWellFormedExpr acc t.f in
    let acc = futharkWellFormedExpr acc t.as in
    futharkWellFormedExpr acc t.bs
  | TmParallelReduce t ->
    -- NOTE(larshum, 2021-12-13): A parallel reduce requires that the
    -- accumulator has the same type as the elements of the provided sequence.
    -- In addition, this type must not be a functional type.
    match t.ty with TyArrow _ then
      cons (FutharkFunctionFromFold (TmParallelReduce t)) acc
    else sfold_Expr_Expr futharkWellFormedExpr acc (TmParallelReduce t)
  | TmParallelSizeCoercion t -> futharkWellFormedExpr acc t.e
  | TmParallelSizeEquality t -> acc
  | expr -> cons (FutharkExprError expr) acc

  sem futharkWellFormedType : [WFError] -> Type -> [WFError]
  sem futharkWellFormedType acc =
  | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> acc
  | TyArrow {from = from, to = to} ->
    let acc = futharkWellFormedType acc from in
    futharkWellFormedType acc to
  | (TyRecord {fields = fields}) & recTy ->
    let isArrowType = lam ty. match ty with TyArrow _ then true else false in
    let acc =
      if any isArrowType (mapValues fields) then
        cons (FutharkFunctionInRecord recTy) acc
      else acc in
    mapFoldWithKey
      (lam acc. lam. lam ty. futharkWellFormedType acc ty) acc fields
  | TySeq {ty = ty & !(TyArrow _)} -> futharkWellFormedType acc ty
  | (TySeq _) & seqTy -> cons (FutharkFunctionInArray seqTy) acc
  | TyCon _ -> acc
  | TyVar _ -> acc
  | TyAlias t -> futharkWellFormedType acc t.content
  | ty -> cons (FutharkTypeError ty) acc

  sem futharkWellFormedPattern : [WFError] -> Pat -> [WFError]
  sem futharkWellFormedPattern acc =
  | PatNamed _ | PatBool _ -> acc
  | PatRecord {bindings = bindings} ->
    mapFoldWithKey
      (lam acc. lam. lam pat. futharkWellFormedPattern acc pat)
      acc bindings
  | pat -> cons (FutharkPatternError pat) acc

  sem isFutharkSupportedConstant : Const -> Bool
  sem isFutharkSupportedConstant =
  | CInt _ | CFloat _ | CChar _ | CBool _ -> true
  | CAddi _ | CAddf _ | CSubi _ | CSubf _ | CMuli _ | CMulf _ | CDivi _
  | CDivf _ | CModi _ | CNegi _ | CNegf _ | CEqi _ | CEqf _ | CLti _ | CLtf _
  | CGti _ | CGtf _ | CLeqi _ | CLeqf _ | CGeqi _ | CGeqf _ | CNeqi _
  | CNeqf _ | CFloorfi _ | CInt2float _ -> true
  | CCreate _ | CLength _ | CReverse _ | CConcat _ | CHead _ | CTail _
  | CNull _ | CSubsequence _ | CMap _ | CFoldl _ | CGet _ | CSet _ -> true
  | _ -> false

  sem wellFormedExprH : [WFError] -> Expr -> [WFError]
  sem wellFormedExprH acc =
  | t -> futharkWellFormedExpr acc t

  sem wellFormedTypeH : [WFError] -> Type -> [WFError]
  sem wellFormedTypeH acc =
  | t -> futharkWellFormedType acc t
end

lang TestLang = FutharkWellFormed + PMExprAst
end

mexpr

use TestLang in

let eqFutError = lam lerr. lam rerr.
  use MExprEq in
  let t = (lerr, rerr) in
  match t with (FutharkFunctionInArray lty, FutharkFunctionInArray rty) then
    eqType lty rty
  else match t with (FutharkFunctionInRecord lty, FutharkFunctionInRecord rty) then
    eqType lty rty
  else match t with (FutharkFunctionFromIf le, FutharkFunctionFromIf re) then
    eqExpr le re
  else match t with (FutharkFunctionFromFold le, FutharkFunctionFromFold re) then
    eqExpr le re
  else match t with (FutharkRecLet le, FutharkRecLet re) then
    eqExpr le re
  else match t with (FutharkExprError le, FutharkExprError re) then
    eqExpr le re
  else match t with (FutharkTypeError lty, FutharkTypeError rty) then
    eqType lty rty
  else match t with (FutharkPatternError lpat, FutharkPatternError rpat) then
    let empty = {varEnv = biEmpty, conEnv = biEmpty} in
    optionIsSome (eqPat empty empty biEmpty lpat rpat)
  else match t with (FutharkConstantError li, FutharkConstantError ri) then
    eqi (infoCmp li ri) 0
  else false
in

let preprocess = lam t. typeCheck (symbolize t) in
let checkWellFormedExpr = lam t.
  wellFormedExpr (preprocess t)
in
let checkWellFormedType = lam ty.
  wellFormedTypeH [] ty
in

let seqTy = tyseq_ (tyarrow_ tyint_ tyint_) in
utest checkWellFormedType seqTy with [FutharkFunctionInArray seqTy]
using eqSeq eqFutError in

let recTy = tyrecord_ [("a", tyarrow_ tyint_ tyint_)] in
utest checkWellFormedType recTy with [FutharkFunctionInRecord recTy]
using eqSeq eqFutError in

let functionFromIf =
  if_ true_ (ulam_ "x" (var_ "x")) (ulam_ "x" (int_ 1)) in
utest checkWellFormedExpr functionFromIf with [FutharkFunctionFromIf functionFromIf]
using eqSeq eqFutError in

let funType = tyarrow_ tyint_ tyint_ in
let foldExpr = foldl_ (var_ "f") (lam_ "x" tyint_ (var_ "x")) (seq_ []) in
let expr = bindall_ [
  ulet_ "f" (lam_ "x" funType (lam_ "y" funType (var_ "y"))),
  foldExpr] in
utest checkWellFormedExpr expr with [FutharkFunctionFromFold foldExpr]
using eqSeq eqFutError in

let sumf = ulam_ "a" (ulam_ "b" (addi_ (var_ "a") (var_ "b"))) in
let sumFold = foldl_ sumf (int_ 0) (seq_ [int_ 1, int_ 2, int_ 3]) in
utest checkWellFormedExpr sumFold with [] using eqSeq eqFutError in

()
