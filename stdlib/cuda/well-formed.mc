-- Defines a well-formedness check specific for the CUDA accelerate backend.

include "cuda/pmexpr-ast.mc"
include "cuda/pmexpr-pprint.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "pmexpr/pprint.mc"
include "pmexpr/well-formed.mc"

lang CudaWellFormed = WellFormed + CudaPMExprAst + CudaPMExprPrettyPrint
  syn WellFormedError =
  | CudaExprError Expr
  | CudaTypeError Type
  | CudaConstantError (Const, Info)
  | CudaPatternError Pat
  | CudaConDefError Expr
  | CudaLoopError Expr
  | CudaReduceError Expr

  sem pprintWellFormedError =
  | CudaExprError expr ->
    let info = infoTm expr in
    let exprStr = expr2str expr in
    infoErrorString info (join ["Expression\n", exprStr, "\nnot supported by CUDA backend"])
  | CudaTypeError ty ->
    let info = infoTy ty in
    let tyStr = type2str ty in
    infoErrorString info (join ["Type '", tyStr, "' not supported by CUDA backend"])
  | CudaConstantError (c, info) ->
    let constStr = getConstStringCode 0 c in
    infoErrorString info (join ["Constant '", constStr, "' not supported by CUDA backend"])
  | CudaPatternError pat ->
    let info = infoPat pat in
    match getPatStringCode 0 pprintEnvEmpty pat with (_, patStr) in
    infoErrorString info (join ["Pattern '", patStr, "' not supported by CUDA backend"])
  | CudaConDefError (expr & (TmConDef t)) ->
    let info = infoTm expr in
    infoErrorString info (join [
      "Constructor definition\n",
      "\nwith ident   : ", nameGetStr t.ident,
      "\nwith tyIdent : ", type2str t.tyIdent,
      "\nnot supported by CUDA backend"])
  | CudaLoopError (expr & (TmLoopAcc t)) ->
    let info = infoTm expr in
    infoErrorString info (join [
      "Loop expression\n", expr2str expr,
      "\nwith ne : ", type2str (tyTm t.ne),
      "\nwith n  : ", type2str (tyTm t.n),
      "\nwith f  : ", type2str (tyTm t.f)])
  | CudaReduceError (expr & (TmParallelReduce t)) ->
    let info = infoTm expr in
    infoErrorString info (join [
      "Reduce expression\n", expr2str expr,
      "\nwith f  : ", type2str (tyTm t.f),
      "\nwith ne : ", type2str (tyTm t.ne),
      "\nwith as : ", type2str (tyTm t.as),
      "\nnot supported by CUDA backend"])

  -- NOTE(larshum, 2022-03-01): Lambda expressions may only be used at the top
  -- of the body of a let-expression or a recursive binding.
  sem checkLambdasInBody (acc : [WellFormedError]) =
  | TmLam t ->
    let acc = cudaWellFormedType acc t.tyIdent in
    checkLambdasInBody acc t.body
  | t -> (acc, t)

  sem cudaWellFormedExpr (acc : [WellFormedError]) =
  | TmVar t -> acc
  | TmApp {lhs = TmConst {val = CError _}} ->
    -- NOTE(larshum, 2022-03-29): Special case to avoid giving well-formedness
    -- error due to unknown type. Needed to support semantic functions.
    acc
  | TmApp t ->
    recursive let checkApp = lam acc : [WellFormedError]. lam e : Expr.
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
    let checkLambdasInBinding : [WellFormedError] -> RecLetBinding
                             -> [WellFormedError] =
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
  | conDef & (TmConDef t) ->
    -- NOTE(larshum, 2022-03-30): Recursive data types, and those that have an
    -- type identifier of unexpected shape, are not considered to be
    -- well-formed.
    recursive let containsTypeIdentifier : Name -> Bool -> Type -> Bool =
      lam conId. lam acc. lam ty.
      if acc then true
      else match ty with TyCon {ident = id} then
        nameEq conId id
      else sfold_Type_Type (containsTypeIdentifier conId) acc ty
    in
    if
      match t.tyIdent with TyArrow {from = from, to = TyCon {ident = id}} then
        not (containsTypeIdentifier id false from)
      else false
    then acc
    else cons (CudaConDefError conDef) acc
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
  -- NOTE(larshum, 2022-03-08): The following expressions are CUDA PMExpr
  -- extensions, which are allowed to contain an expression of function type.
  -- This is allowed because they are handled differently from other terms.
  | loop & (TmLoop t | TmParallelLoop t) ->
    let addLoopError = lam. cons (CudaLoopError loop) acc in
    let acc = cudaWellFormedExpr acc t.n in
    match tyTm t.f with TyArrow {from = TyInt _, to = TyRecord {labels = []}} then
      match t.ty with TyRecord {labels = []} then acc
      else addLoopError ()
    else addLoopError ()
  | loop & (TmLoopAcc t) ->
    let addLoopError = lam. cons (CudaLoopError loop) acc in
    let acc = cudaWellFormedExpr acc t.ne in
    let acc = cudaWellFormedExpr acc t.n in
    match tyTm t.f with TyArrow {
      from = accTy1,
      to = TyArrow {from = TyInt _, to = accTy2}}
    then
      if and (eqType accTy1 accTy2) (eqType accTy1 (tyTm t.ne)) then acc
      else addLoopError ()
    else addLoopError ()
  | red & (TmParallelReduce t) ->
    let addReduceError = lam. cons (CudaReduceError red) acc in
    let acc = cudaWellFormedExpr acc t.ne in
    let acc = cudaWellFormedExpr acc t.as in
    match tyTm t.f with TyArrow {
      from = accTy1,
      to = TyArrow {from = elemTy, to = accTy2}}
    then
      if and (eqType accTy1 accTy2) (eqType (tyTm t.as) (tyseq_ elemTy)) then
        acc
      else addReduceError ()
    else addReduceError ()
  | t ->
    let info = infoTm t in
    let acc =
      if isCudaSupportedExpr t then acc
      else cons (CudaExprError t) acc in
    let acc = sfold_Type_Type cudaWellFormedType acc (tyTm t) in
    sfold_Expr_Expr cudaWellFormedExpr acc t

  sem cudaWellFormedType (acc : [WellFormedError]) =
  | ty ->
    if isCudaSupportedType ty then
      sfold_Type_Type cudaWellFormedType acc ty
    else
      cons (CudaTypeError ty) acc

  sem cudaWellFormedConstant (info : Info) (acc : [WellFormedError]) =
  | c ->
    if isCudaSupportedConstant c then acc
    else cons (CudaConstantError (c, info)) acc

  sem cudaWellFormedPattern (acc : [WellFormedError]) =
  | pat ->
    if isCudaSupportedPattern pat then
      sfold_Pat_Pat cudaWellFormedPattern acc pat
    else
      cons (CudaPatternError pat) acc

  sem isCudaSupportedExpr =
  | TmVar _ | TmApp _ | TmLet _ | TmRecLets _ | TmConst _ | TmMatch _
  | TmNever _ | TmSeq _ | TmRecord _ | TmType _ | TmConDef _ | TmConApp _
  | TmExt _ -> true
  | TmLoop _ | TmLoopAcc _ | TmParallelLoop _ -> true
  | _ -> false

  sem isCudaSupportedType =
  | TyInt _ | TyFloat _ | TyBool _ | TyChar _ | TyCon _
  | TyTensor {ty = TyInt _ | TyFloat _} -> true
  | TySeq {ty = ty} -> isCudaSupportedType ty
  | TyRecord {fields = fields} -> forAll isCudaSupportedType (mapValues fields)
  | _ -> false

  sem isCudaSupportedConstant =
  | CInt _ | CFloat _ | CChar _ | CBool _ -> true
  | CAddi _ | CAddf _ | CSubi _ | CSubf _ | CMuli _ | CMulf _ | CDivi _
  | CDivf _ | CModi _ | CNegi _ | CNegf _ | CEqi _ | CEqf _ | CLti _ | CLtf _
  | CGti _ | CGtf _ | CLeqi _ | CLeqf _ | CGeqi _ | CGeqf _ | CNeqi _
  | CNeqf _ -> true
  | CPrint _ | CDPrint _ | CInt2float _ | CFloorfi _ | CGet _ | CLength _
  | CFoldl _ | CError _ -> true
  | CTensorGetExn _ | CTensorSetExn _ | CTensorRank _ | CTensorShape _
  | CTensorSliceExn _ | CTensorSubExn _ -> true
  | _ -> false

  sem isCudaSupportedPattern =
  | PatNamed _ | PatBool _ | PatRecord _ | PatCon _ -> true
  | _ -> false

  sem wellFormedExprH (acc : [WellFormedError]) =
  | t -> cudaWellFormedExpr acc t

  sem wellFormedTypeH (acc : [WellFormedError]) =
  | t -> cudaWellFormedType acc t
end

mexpr

use CudaWellFormed in

let eqCudaError = lam lerr : WellFormedError. lam rerr : WellFormedError.
  use MExprEq in
  let t = (lerr, rerr) in
  match t with (CudaExprError le, CudaExprError re) then
    eqExpr le re
  else match t with (CudaTypeError lty, CudaTypeError rty) then
    eqType lty rty
  else match t with (CudaConstantError (lc, li), CudaConstantError (rc, ri)) then
    and (eqConst lc rc) (eqi (infoCmp li ri) 0)
  else match t with (CudaPatternError lpat, CudaPatternError rpat) then
    let empty = {varEnv = biEmpty, conEnv = biEmpty} in
    optionIsSome (eqPat empty empty biEmpty lpat rpat)
  else match t with (CudaConDefError lc, CudaConDefError rc) then
    eqExpr lc rc
  else false
in

let preprocess = lam t. typeAnnot (symbolize t) in

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
utest wellFormedExpr conDef with [CudaConDefError expectedExpr]
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
utest wellFormedExpr fileRead with [CudaConstantError (c, i)]
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
