-- Defines a well-formedness check specific for the CUDA accelerate backend.

include "cuda/pmexpr-ast.mc"
include "cuda/pmexpr-pprint.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "pmexpr/pprint.mc"
include "pmexpr/well-formed.mc"

lang CudaWellFormed = WellFormed + CudaPMExprAst
  syn WFError =
  | CudaExprError Expr
  | CudaTypeError Type
  | CudaConstantError Info
  | CudaPatternError Pat

  sem wellFormednessBackendName =
  | () -> "CUDA"

  sem pprintWellFormedError =
  | CudaExprError expr ->
    (infoTm expr, "Expression is not supported")
  | CudaTypeError ty ->
    (infoTy ty, "Type is not supported")
  | CudaConstantError info ->
    (info, "Constant is not supported")
  | CudaPatternError pat ->
    (infoPat pat, "Pattern is not supported")

  -- NOTE(larshum, 2022-03-01): Lambda expressions may only be used at the top
  -- of the body of a let-expression or a recursive binding.
  sem checkLambdasInBody : [WFError] -> Expr -> ([WFError], Expr)
  sem checkLambdasInBody acc =
  | TmLam t ->
    let acc = cudaWellFormedType acc t.tyIdent in
    checkLambdasInBody acc t.body
  | t -> (acc, t)

  sem cudaWellFormedExpr : [WFError] -> Expr -> [WFError]
  sem cudaWellFormedExpr acc =
  | TmVar t -> acc
  | TmApp {lhs = TmConst {val = CError _}} ->
    -- NOTE(larshum, 2022-03-29): Special case to avoid giving well-formedness
    -- error due to unknown type. Needed to support semantic functions.
    acc
  | TmApp t ->
    recursive let checkApp = lam acc : [WFError]. lam e : Expr.
      match e with TmApp t then
        let acc = cudaWellFormedExpr acc t.rhs in
        checkApp acc t.lhs
      else cudaWellFormedExpr acc e
    in
    let acc = cudaWellFormedType acc t.ty in
    checkApp acc (TmApp t)
  | TmLet t ->
    match checkLambdasInBody acc t.body with (acc, body) in
    let acc = cudaWellFormedExpr acc body in
    cudaWellFormedExpr acc t.inexpr
  | TmRecLets t ->
    let checkLambdasInBinding : [WFError] -> RecLetBinding -> [WFError] =
      lam acc. lam binding.
      match checkLambdasInBody acc binding.body with (acc, body) in
      cudaWellFormedExpr acc body
    in
    let acc = foldl checkLambdasInBinding acc t.bindings in
    cudaWellFormedExpr acc t.inexpr
  | TmConst t -> cudaWellFormedConstant t.info acc t.val
  | TmMatch t ->
    let acc = cudaWellFormedPattern acc t.pat in
    let acc = cudaWellFormedType acc t.ty in
    sfold_Expr_Expr cudaWellFormedExpr acc (TmMatch t)
  | TmSeqFoldl t ->
    let acc = cudaWellFormedExpr acc t.acc in
    cudaWellFormedExpr acc t.s
  | TmTensorSliceExn t ->
    let acc = cudaWellFormedExpr acc t.t in
    cudaWellFormedExpr acc t.slice
  | TmTensorSubExn t ->
    let acc = cudaWellFormedExpr acc t.t in
    let acc = cudaWellFormedExpr acc t.ofs in
    cudaWellFormedExpr acc t.len
  -- NOTE(larshum, 2022-03-08): The following expressions are PMExpr
  -- extensions, which are allowed to contain an expression of function type.
  -- This is allowed because they are handled differently from other terms.
  | (TmLoop _ | TmParallelLoop _ | TmLoopAcc _ | TmParallelReduce _) & t -> acc
  | t ->
    let info = infoTm t in
    let acc =
      if isCudaSupportedExpr t then acc
      else cons (CudaExprError t) acc in
    let acc = sfold_Type_Type cudaWellFormedType acc (tyTm t) in
    sfold_Expr_Expr cudaWellFormedExpr acc t

  sem cudaWellFormedType : [WFError] -> Type -> [WFError]
  sem cudaWellFormedType acc =
  | ty ->
    if isCudaSupportedType ty then
      sfold_Type_Type cudaWellFormedType acc ty
    else
      cons (CudaTypeError ty) acc

  sem cudaWellFormedConstant : Info -> [WFError] -> Const -> [WFError]
  sem cudaWellFormedConstant info acc =
  | c ->
    if isCudaSupportedConstant c then acc
    else cons (CudaConstantError info) acc

  sem cudaWellFormedPattern : [WFError] -> Pat -> [WFError]
  sem cudaWellFormedPattern acc =
  | pat ->
    if isCudaSupportedPattern pat then
      sfold_Pat_Pat cudaWellFormedPattern acc pat
    else
      cons (CudaPatternError pat) acc

  sem isCudaSupportedExpr : Expr -> Bool
  sem isCudaSupportedExpr =
  | TmVar _ | TmApp _ | TmLet _ | TmRecLets _ | TmConst _ | TmMatch _
  | TmNever _ | TmSeq _ | TmRecord _ | TmType _ | TmExt _ -> true
  | TmLoop _ | TmLoopAcc _ | TmParallelLoop _ | TmPrintFloat _ -> true
  | _ -> false

  sem isCudaSupportedType : Type -> Bool
  sem isCudaSupportedType =
  | TyInt _ | TyFloat _ | TyBool _ | TyChar _ | TyCon _
  | TyTensor {ty = TyInt _ | TyFloat _} -> true
  | TySeq {ty = ty} -> isCudaSupportedType ty
  | TyRecord {fields = fields} -> forAll isCudaSupportedType (mapValues fields)
  | _ -> false

  sem isCudaSupportedConstant : Const -> Bool
  sem isCudaSupportedConstant =
  | CInt _ | CFloat _ | CChar _ | CBool _ -> true
  | CAddi _ | CAddf _ | CSubi _ | CSubf _ | CMuli _ | CMulf _ | CDivi _
  | CDivf _ | CModi _ | CNegi _ | CNegf _ | CEqi _ | CEqf _ | CLti _ | CLtf _
  | CGti _ | CGtf _ | CLeqi _ | CLeqf _ | CGeqi _ | CGeqf _ | CNeqi _
  | CNeqf _ -> true
  | CPrint _ | CDPrint _ | CInt2float _ | CFloorfi _ | CGet _ | CLength _
  | CFoldl _ | CError _ -> true
  | CTensorGetExn _ | CTensorSetExn _ | CTensorLinearGetExn _
  | CTensorLinearSetExn _ | CTensorRank _ | CTensorShape _
  | CTensorSliceExn _ | CTensorSubExn _ -> true
  | _ -> false

  sem isCudaSupportedPattern : Pat -> Bool
  sem isCudaSupportedPattern =
  | PatNamed _ | PatBool _ | PatRecord _ | PatCon _ -> true
  | _ -> false

  sem wellFormedExprH acc =
  | e -> cudaWellFormedExpr acc e

  sem wellFormedTypeH acc =
  | ty -> cudaWellFormedType acc ty
end

mexpr

use CudaWellFormed in

let eqCudaError = lam lerr : WFError. lam rerr : WFError.
  use MExprEq in
  let t = (lerr, rerr) in
  match t with (CudaExprError le, CudaExprError re) then
    eqExpr le re
  else match t with (CudaTypeError lty, CudaTypeError rty) then
    eqType lty rty
  else match t with (CudaConstantError li, CudaConstantError ri) then
    eqi (infoCmp li ri) 0
  else match t with (CudaPatternError lpat, CudaPatternError rpat) then
    let empty = {varEnv = biEmpty, conEnv = biEmpty} in
    optionIsSome (eqPat empty empty biEmpty lpat rpat)
  else false
in

let preprocess = lam t. typeCheck (symbolize t) in

utest wellFormedExpr (bind_ (ulet_ "x" (int_ 2)) (var_ "x")) with []
using eqSeq eqCudaError in

let t = preprocess
  (bind_
    (let_ "f" (tyarrow_ tyint_ tyint_)
      (lam_ "x" tyint_ (addi_ (var_ "x") (int_ 1))))
    (app_ (var_ "f") (int_ 4))) in
utest wellFormedExpr t with [] using eqSeq eqCudaError in

let rec = preprocess
  (bind_
    (reclet_ "f" (tyarrow_ tyint_ tyint_)
      (lam_ "n" tyint_
        (if_ (eqi_ (var_ "n") (int_ 0))
          (int_ 1)
          (muli_ (app_ (var_ "f") (subi_ (var_ "n") (int_ 1))) (var_ "n")))))
    (app_ (var_ "f") (int_ 4))) in
utest wellFormedExpr rec with [] using eqSeq eqCudaError in

let seqLit = preprocess (seq_ [int_ 1, int_ 2, int_ 3]) in
utest wellFormedExpr seqLit with [] using eqSeq eqCudaError in

let i = Info {filename = "", row1 = 0, row2 = 0, col1 = 0, col2 = 0} in
let arrowType = tyWithInfo i (tyarrow_ tyint_ tyint_) in
let seqLitArrowType = preprocess
  (bind_
    (let_ "id" (tyarrow_ tyint_ tyint_) (lam_ "x" tyint_ (var_ "x")))
    (seq_ [withType arrowType (var_ "id")])) in
utest wellFormedExpr seqLitArrowType with [CudaTypeError arrowType]
using eqSeq eqCudaError in

let tensorSeqTy = tyseq_ (tytensor_ tyint_) in
utest wellFormedType tensorSeqTy with []
using eqSeq eqCudaError in

let recLit =
  record_
    (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
    [("a", int_ 0), ("b", float_ 0.0)] in
utest wellFormedExpr recLit with [] using eqSeq eqCudaError in

let recTy = tyrecord_ [("a", arrowType)] in
utest wellFormedType recTy with [CudaTypeError recTy]
using eqSeq eqCudaError in

let recordUpdateExpr = recordupdate_ (var_ "r") "a" (int_ 4) in
let recUpdate = preprocess
  (bind_
    (let_ "r" (tyrecord_ [("a", tyint_)]) (urecord_ [("a", int_ 3)]))
    recordUpdateExpr) in
utest wellFormedExpr recUpdate with [CudaExprError recordUpdateExpr]
using eqSeq eqCudaError in

let t = nameSym "Tree" in
let recursiveConstructorExpr = condef_ "Con" (tyarrow_ (ntyvar_ t) (ntyvar_ t)) in
let conDef = preprocess (bindall_ [
  ntype_ t (tyvariant_ []),
  recursiveConstructorExpr,
  int_ 0]) in
let expectedExpr = preprocess (bind_ recursiveConstructorExpr (int_ 0)) in
utest wellFormedExpr conDef with [CudaExprError expectedExpr]
using eqSeq eqCudaError in

let ext = preprocess (ext_ "sin" false (tyarrow_ tyfloat_ tyfloat_)) in
utest wellFormedExpr ext with []
using eqSeq eqCudaError in

let utestTerm = utest_ (int_ 1) (int_ 2) (int_ 0) in
utest wellFormedExpr utestTerm with [CudaExprError utestTerm]
using eqSeq eqCudaError in

let c = CFileRead () in
let fileRead = preprocess
  (app_
    (withInfo i (const_ (tyarrow_ tystr_ tystr_) c))
    (str_ "test.txt")) in
utest wellFormedExpr fileRead with [CudaConstantError i]
using eqSeq eqCudaError in

let matchBoolPat = preprocess
  (bind_
    (let_ "x" tyint_ (int_ 3))
    (match_ (gti_ (var_ "x") (int_ 0)) ptrue_ (int_ 1) (int_ 0))) in
utest wellFormedExpr matchBoolPat with []
using eqSeq eqCudaError in

let pat = pint_ 4 in
let matchIntPat = preprocess
  (bind_
    (let_ "x" tyint_ (int_ 3))
    (match_ (var_ "x") pat (int_ 1) (int_ 0))) in
utest wellFormedExpr matchIntPat with [CudaPatternError pat]
using eqSeq eqCudaError in

let pat = pchar_ 'x' in
let matchCharPat = preprocess
  (bind_
    (let_ "c" tychar_ (char_ 'x'))
    (match_ (var_ "c") pat (int_ 1) (int_ 0))) in
utest wellFormedExpr matchCharPat with [CudaPatternError pat]
using eqSeq eqCudaError in

let recTy = tyrecord_ [("a", tyint_), ("b", tyfloat_)] in
let matchRecordPat = preprocess
  (bind_
    (let_ "r" recTy (record_ recTy [("a", int_ 2), ("b", float_ 3.0)]))
    (match_ (var_ "r") (prec_ [("a", pvar_ "a"), ("b", pvarw_)]) (int_ 1) (int_ 0))) in
utest wellFormedExpr matchRecordPat with []
using eqSeq eqCudaError in

()
