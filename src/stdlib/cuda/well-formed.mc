-- Defines a well-formedness check specific for the CUDA accelerate backend.

include "cuda/pmexpr-ast.mc"
include "cuda/pmexpr-pprint.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "pmexpr/pprint.mc"
include "pmexpr/utils.mc"
include "pmexpr/well-formed.mc"

lang CudaWellFormed = WellFormed + CudaPMExprAst
  syn WFError =
  | CudaExprError Expr
  | CudaTypeError Type
  | CudaPatternError Pat
  | CudaConstantError Info
  | CudaAppArgTypeError Expr
  | CudaAppResultTypeError Expr
  | CudaFunctionDefError Expr
  | CudaFunctionInMatch Expr
  | CudaHigherOrderArgument Expr

  sem wellFormednessBackendName =
  | () -> "CUDA"

  sem pprintWellFormedError =
  | CudaExprError expr ->
    (infoTm expr, "Expression is not supported")
  | CudaTypeError ty ->
    (infoTy ty, "Type is not supported")
  | CudaPatternError pat ->
    (infoPat pat, "Pattern is not supported")
  | CudaConstantError info ->
    (info, "Constant is not supported")
  | CudaAppResultTypeError app ->
    (infoTm app, "Return values of function type are not supported")
  | CudaFunctionDefError fun ->
    (infoTm fun, join ["Functions must be defined using explicit lambdas, ",
                       "using one lambda per parameter"])
  | CudaFunctionInMatch e ->
    (infoTm e, join ["Result of conditional expression cannot be a function"])
  | CudaHigherOrderArgument e ->
    (infoTm e, join ["Unsupported higher-order argument"])

  sem cudaWellFormedExpr : [WFError] -> Expr -> [WFError]
  sem cudaWellFormedExpr acc =
  -- NOTE(larshum, 2022-08-09): Currently, the MLang transformation of semantic
  -- functions produce code containing unknown types, which are not allowed.
  -- We add the line below as a hack to allow compiling semantic functions.
  | TmApp {lhs = TmConst {val = CError _}} | TmNever _ -> acc
  | e ->
    let acc = cudaWellFormedType acc (tyTm e) in
    cudaWellFormedExprH acc e

  sem _cudaCheckConstApp : [WFError] -> [Expr] -> Const -> [WFError]
  sem _cudaCheckConstApp acc args =
  | CFoldl _ ->
    let acc = cudaWellFormedHigherOrder acc (get args 0) in
    let acc = cudaWellFormedExpr acc (get args 1) in
    cudaWellFormedExpr acc (get args 2)
  | CTensorSliceExn _ ->
    let acc = cudaWellFormedExpr acc (get args 0) in
    cudaWellFormedExpr acc (get args 1)
  | CTensorSubExn _ ->
    let acc = cudaWellFormedExpr acc (get args 0) in
    let acc = cudaWellFormedExpr acc (get args 1) in
    cudaWellFormedExpr acc (get args 2)
  | _ -> foldl cudaWellFormedExpr acc args

  sem _cudaCheckApp : [WFError] -> Expr -> [WFError]
  sem _cudaCheckApp acc =
  | (TmApp t) & app ->
    match collectAppArguments app with (fun, args) in
    let acc =
      match fun with TmConst {val = c} then _cudaCheckConstApp acc args c
      else foldl cudaWellFormedExpr acc args in
    cudaWellFormedExpr acc fun

  sem cudaWellFormedExprH : [WFError] -> Expr -> [WFError]
  sem cudaWellFormedExprH acc =
  | TmVar t -> acc
  | (TmApp t) & app ->
    match t.ty with TyArrow _ then
      cons (CudaAppResultTypeError app) acc
    else _cudaCheckApp acc app
  | TmLam t -> cudaWellFormedExpr acc t.body
  | TmLet t ->
    let acc =
      if cudaWellFormedLambdas (t.body, t.tyBody) then acc
      else cons (CudaFunctionDefError t.body) acc in
    let acc = cudaWellFormedExpr acc t.body in
    cudaWellFormedExpr acc t.inexpr
  | TmRecLets t ->
    let checkBinding = lam acc. lam bind.
      let acc =
        if cudaWellFormedLambdas (bind.body, bind.tyBody) then acc
        else cons (CudaFunctionDefError bind.body) acc in
      cudaWellFormedExpr acc bind.body
    in
    let acc = foldl checkBinding acc t.bindings in
    cudaWellFormedExpr acc t.inexpr
  | TmConst t ->
    if isCudaSupportedConstant t.val then acc
    else cons (CudaConstantError t.info) acc
  | TmMatch t ->
    let acc = cudaWellFormedExpr acc t.target in
    let acc = cudaWellFormedPattern acc t.pat in
    let acc = cudaWellFormedExpr acc t.thn in
    let acc = cudaWellFormedExpr acc t.els in
    match t.ty with TyArrow _ then cons (CudaFunctionInMatch (TmMatch t)) acc
    else acc
  | TmNever _ -> acc
  | TmRecord {bindings = bindings} ->
    mapFoldWithKey
      (lam acc. lam. lam expr. cudaWellFormedExpr acc expr) acc bindings
  | TmSeq {tms = tms} ->
    foldl (lam acc. lam expr. cudaWellFormedExpr acc expr) acc tms
  | TmExt t -> cudaWellFormedExpr acc t.inexpr
  | TmType t ->
    let acc = cudaWellFormedType acc t.tyIdent in
    cudaWellFormedExpr acc t.inexpr
  | TmConDef t ->
    let acc = cons (CudaExprError (TmConDef t)) acc in
    cudaWellFormedExpr acc t.inexpr
  | TmLoop t | TmParallelLoop t ->
    let acc = cudaWellFormedExpr acc t.n in
    cudaWellFormedHigherOrder acc t.f
  | TmLoopAcc t ->
    let acc = cudaWellFormedExpr acc t.ne in
    let acc = cudaWellFormedExpr acc t.n in
    cudaWellFormedHigherOrder acc t.f
  | TmPrintFloat t -> acc
  | expr -> cons (CudaExprError expr) acc

  sem cudaWellFormedHigherOrder : [WFError] -> Expr -> [WFError]
  sem cudaWellFormedHigherOrder acc =
  | TmVar t -> acc
  | app & (TmApp _) -> _cudaCheckApp acc app
  | t -> cons (CudaHigherOrderArgument t) acc

  sem cudaWellFormedType : [WFError] -> Type -> [WFError]
  sem cudaWellFormedType acc =
  | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> acc
  | TyArrow {from = from, to = to} ->
    let acc = cudaWellFormedType acc from in
    cudaWellFormedType acc to
  | (TyRecord {fields = fields}) & recTy ->
    let containsArrowType = lam ty. containsArrowType false ty in
    let acc =
      if any containsArrowType (mapValues fields) then
        cons (CudaTypeError recTy) acc
      else acc
    in
    mapFoldWithKey
      (lam acc. lam. lam ty. cudaWellFormedType acc ty) acc fields
  | TySeq {ty = ty} & seqTy ->
    if containsArrowType false ty then
      cons (CudaTypeError seqTy) acc
    else
      cudaWellFormedType acc ty
  | TyTensor {ty = TyInt _ | TyFloat _} -> acc
  | TyCon _ -> acc
  | TyAlias t -> cudaWellFormedType acc t.content
  | ty -> cons (CudaTypeError ty) acc

  sem containsArrowType : Bool -> Type -> Bool
  sem containsArrowType acc =
  | TyArrow _ -> true
  | ty -> sfold_Type_Type containsArrowType acc ty

  sem cudaWellFormedPattern : [WFError] -> Pat -> [WFError]
  sem cudaWellFormedPattern acc =
  | PatNamed _ | PatBool _ -> acc
  | PatRecord {bindings = bindings} ->
    mapFoldWithKey
      (lam acc. lam. lam pat. cudaWellFormedPattern acc pat)
      acc bindings
  | pat -> cons (CudaPatternError pat) acc

  sem cudaWellFormedLambdas : (Expr, Type) -> Bool
  sem cudaWellFormedLambdas =
  | (TmLam e, TyArrow ty) ->
    match ty.from with TyArrow _ then false
    else cudaWellFormedLambdas (e.body, ty.to)
  | (e, !(TyArrow _)) -> true
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
let checkWellFormedExpr = lam t.
  wellFormedExpr (preprocess t)
in
let checkWellFormedType = lam ty.
  wellFormedTypeH [] ty
in

utest checkWellFormedExpr (bind_ (ulet_ "x" (int_ 2)) (var_ "x")) with []
using eqSeq eqCudaError in

let t =
  bind_
    (let_ "f" (tyarrow_ tyint_ tyint_)
      (lam_ "x" tyint_ (addi_ (var_ "x") (int_ 1))))
    (app_ (var_ "f") (int_ 4)) in
utest checkWellFormedExpr t with [] using eqSeq eqCudaError in

let rec = preprocess
  (bind_
    (reclet_ "f" (tyarrow_ tyint_ tyint_)
      (lam_ "n" tyint_
        (if_ (eqi_ (var_ "n") (int_ 0))
          (int_ 1)
          (muli_ (app_ (var_ "f") (subi_ (var_ "n") (int_ 1))) (var_ "n")))))
    (app_ (var_ "f") (int_ 4))) in
utest checkWellFormedExpr rec with [] using eqSeq eqCudaError in

let seqLit = preprocess (seq_ [int_ 1, int_ 2, int_ 3]) in
utest checkWellFormedExpr seqLit with [] using eqSeq eqCudaError in

let arrowType = tyarrow_ tyint_ tyint_ in
let seqArrowType = tyseq_ arrowType in
let seqLitArrowType = preprocess
  (bind_
    (let_ "id" (tyarrow_ tyint_ tyint_) (lam_ "x" tyint_ (var_ "x")))
    (seq_ [withType arrowType (var_ "id")])) in
-- NOTE(larshum, 2022-07-12): This test case produces multiple errors of the
-- same kind, so we only look at the first of these.
utest head (checkWellFormedExpr seqLitArrowType) with CudaTypeError seqArrowType
using eqCudaError in

let tensorSeqTy = tyseq_ (tytensor_ tyint_) in
utest checkWellFormedType tensorSeqTy with []
using eqSeq eqCudaError in

let recLit =
  record_
    (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
    [("a", int_ 0), ("b", float_ 0.0)] in
utest checkWellFormedExpr recLit with [] using eqSeq eqCudaError in

let seqTy = tyrecord_ [("a", arrowType)] in
utest checkWellFormedType seqTy with [CudaTypeError seqTy]
using eqSeq eqCudaError in

let recTy = tyrecord_ [("a", arrowType)] in
utest checkWellFormedType recTy with [CudaTypeError recTy]
using eqSeq eqCudaError in

let recordUpdateExpr = recordupdate_ (var_ "r") "a" (int_ 4) in
let recUpdate =
  bind_
    (let_ "r" (tyrecord_ [("a", tyint_)]) (urecord_ [("a", int_ 3)]))
    recordUpdateExpr in
utest checkWellFormedExpr recUpdate with [CudaExprError recordUpdateExpr]
using eqSeq eqCudaError in

let t = nameSym "Tree" in
let recursiveConstructorExpr =
  ncondef_ (nameSym "Con") (tyarrow_ (tytuple_ [ntycon_ t, ntycon_ t]) (ntycon_ t))
in
let conDef = bindall_ [
  ntype_ t [] (tyvariant_ []),
  recursiveConstructorExpr,
  int_ 0] in
let expectedExpr = bind_ recursiveConstructorExpr (int_ 0) in
-- NOTE(larshum, 2022-07-12): Skip the first expression (a type) since we
-- cannot compare those.
utest tail (checkWellFormedExpr conDef) with [CudaExprError expectedExpr]
using eqSeq eqCudaError in

let ext = ext_ "sin" false (tyarrow_ tyfloat_ tyfloat_) in
utest checkWellFormedExpr ext with []
using eqSeq eqCudaError in

let utestTerm = utest_ (int_ 1) (int_ 2) (int_ 0) in
utest checkWellFormedExpr utestTerm with [CudaExprError utestTerm]
using eqSeq eqCudaError in

let i = Info {filename = "", row1 = 0, row2 = 0, col1 = 0, col2 = 0} in
let c = CFileRead () in
let fileRead =
  app_
    (withInfo i (const_ (tyarrow_ tystr_ tystr_) c))
    (str_ "test.txt") in
utest checkWellFormedExpr fileRead with [CudaConstantError i]
using eqSeq eqCudaError in

let matchBoolPat =
  bind_
    (let_ "x" tyint_ (int_ 3))
    (match_ (gti_ (var_ "x") (int_ 0)) ptrue_ (int_ 1) (int_ 0)) in
utest checkWellFormedExpr matchBoolPat with []
using eqSeq eqCudaError in

let pat = pint_ 4 in
let matchIntPat =
  bind_
    (let_ "x" tyint_ (int_ 3))
    (match_ (var_ "x") pat (int_ 1) (int_ 0)) in
utest checkWellFormedExpr matchIntPat with [CudaPatternError pat]
using eqSeq eqCudaError in

let pat = pchar_ 'x' in
let matchCharPat =
  bind_
    (let_ "c" tychar_ (char_ 'x'))
    (match_ (var_ "c") pat (int_ 1) (int_ 0)) in
utest checkWellFormedExpr matchCharPat with [CudaPatternError pat]
using eqSeq eqCudaError in

let recTy = tyrecord_ [("a", tyint_), ("b", tyfloat_)] in
let matchRecordPat =
  bind_
    (let_ "r" recTy (record_ recTy [("a", int_ 2), ("b", float_ 3.0)]))
    (match_ (var_ "r") (prec_ [("a", pvar_ "a"), ("b", pvarw_)]) (int_ 1) (int_ 0)) in
utest checkWellFormedExpr matchRecordPat with []
using eqSeq eqCudaError in

()
