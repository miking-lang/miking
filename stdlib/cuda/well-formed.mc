-- Defines a well-formedness check specific for the CUDA accelerate backend.

include "cuda/pmexpr-ast.mc"
include "pmexpr/well-formed.mc"

lang CudaWellFormed = WellFormed + CudaPMExprAst
  syn WellFormedError =
  | CudaExprError Info
  | CudaTypeError Info
  | CudaConstantError Info
  | CudaPatternError Info

  sem pprintWellFormedError =
  | CudaExprError info ->
    infoErrorString info "Expression not supported by CUDA backend"
  | CudaTypeError info ->
    infoErrorString info "Type not supported by CUDA backend"
  | CudaConstantError info ->
    infoErrorString info "Constant not supported by CUDA backend"
  | CudaPatternError info ->
    infoErrorString info "Pattern not supported by CUDA backend"

  -- NOTE(larshum, 2022-03-01): Lambda expressions may only be used at the top
  -- of the body of a let-expression or a recursive binding.
  sem checkLambdasInBody (acc : [WellFormedError]) =
  | TmLam t ->
    let acc = cudaWellFormedType t.info acc t.tyIdent in
    checkLambdasInBody acc t.body
  | t -> (acc, t)

  sem cudaWellFormedExpr (acc : [WellFormedError]) =
  | TmVar t -> acc
  | TmApp t ->
    let acc = cudaWellFormedType t.info acc t.ty in
    let acc = cudaWellFormedExpr acc t.rhs in
    -- NOTE(larshum, 2022-03-01): We only check the well-formedness of the
    -- left-hand side if it is not another application - otherwise we will find
    -- a type error (the left-hand side will have an arrow type).
    match t.lhs with TmApp _ then acc
    else cudaWellFormedExpr acc t.lhs
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
    let acc = cudaWellFormedPattern t.info acc t.pat in
    let acc = cudaWellFormedType t.info acc t.ty in
    sfold_Expr_Expr cudaWellFormedExpr acc (TmMatch t)
  | t ->
    let info = infoTm t in
    let acc =
      if isCudaSupportedExpr t then acc
      else cons (CudaExprError info) acc in
    let acc = sfold_Type_Type (cudaWellFormedType info) acc (tyTm t) in
    sfold_Expr_Expr cudaWellFormedExpr acc t

  sem cudaWellFormedType (info : Info) (acc : [WellFormedError]) =
  | ty ->
    if isCudaSupportedType ty then
      sfold_Type_Type (cudaWellFormedType info) acc ty
    else
      let typeInfo = match infoTy ty with Info i then Info i else info in
      cons (CudaTypeError typeInfo) acc

  sem cudaWellFormedConstant (info : Info) (acc : [WellFormedError]) =
  | c ->
    if isCudaSupportedConstant c then acc
    else cons (CudaConstantError info) acc

  sem cudaWellFormedPattern (info : Info) (acc : [WellFormedError]) =
  | pat ->
    if isCudaSupportedPattern pat then
      sfold_Pat_Pat (cudaWellFormedPattern info) acc pat
    else
      let patInfo = match infoPat pat with Info i then Info i else info in
      cons (CudaPatternError patInfo) acc

  sem isCudaSupportedExpr =
  | TmVar _ | TmApp _ | TmLet _ | TmRecLets _ | TmConst _ | TmMatch _
  | TmNever _ | TmSeq _ | TmRecord _ -> true
  | _ -> false

  sem isCudaSupportedType =
  | TyInt _ | TyFloat _ | TyBool _ | TyChar _ | TyCon _ | TyRecord _
  | TySeq {ty = !TySeq _} | TyTensor {ty = TyInt _ | TyFloat _} -> true
  | _ -> false

  sem isCudaSupportedConstant =
  | CInt _ | CFloat _ | CChar _ | CBool _ -> true
  | CAddi _ | CAddf _ | CSubi _ | CSubf _ | CMuli _ | CMulf _ | CDivi _
  | CDivf _ | CModi _ | CEqi _ | CEqf _ | CLti _ | CLtf _ | CGti _ | CGtf _
  | CLeqi _ | CLeqf _ | CGeqi _ | CGeqf _ | CNeqi _ | CNeqf _ -> true
  | CPrint _ | CInt2float _ | CFloorfi _ | CGet _ | CLength _ -> true
  | _ -> false

  sem isCudaSupportedPattern =
  | PatNamed _ | PatBool _ | PatRecord _ | PatCon _ -> true
  | _ -> false

  sem wellFormedExprH (acc : [WellFormedError]) =
  | t -> cudaWellFormedExpr acc t
end

mexpr

use CudaWellFormed in

let checkWellFormed = lam t. wellFormedExpr (typeAnnot (symbolize t)) in

utest checkWellFormed (bind_ (ulet_ "x" (int_ 2)) (var_ "x")) with [] in

let t =
  bind_
    (let_ "f" (tyarrow_ tyint_ tyint_)
      (lam_ "x" tyint_ (addi_ (var_ "x") (int_ 1))))
    (app_ (var_ "f") (int_ 4)) in
utest checkWellFormed t with [] in

let rec =
  bind_
    (reclet_ "f" (tyarrow_ tyint_ tyint_)
      (lam_ "n" tyint_
        (if_ (eqi_ (var_ "n") (int_ 0))
          (int_ 1)
          (muli_ (app_ (var_ "f") (subi_ (var_ "n") (int_ 1))) (var_ "n")))))
    (app_ (var_ "f") (int_ 4)) in
utest checkWellFormed rec with [] in

let seqLit = seq_ [int_ 1, int_ 2, int_ 3] in
utest checkWellFormed seqLit with [] in

let i = Info {filename = "", row1 = 0, row2 = 0, col1 = 0, col2 = 0} in
let arrowType = tyWithInfo i (tyarrow_ tyint_ tyint_) in
let seqLitArrowType =
  bind_
    (let_ "id" (tyarrow_ tyint_ tyint_) (lam_ "x" tyint_ (var_ "x")))
    (seq_ [withType arrowType (var_ "id")]) in
utest checkWellFormed seqLitArrowType with [CudaTypeError i] in

let tensorSeqTy = tyseq_ (tytensor_ tyint_) in
let seqLitTensor = withType tensorSeqTy (withInfo i (seq_ [])) in
utest checkWellFormed seqLitTensor with [CudaTypeError i] in

let recLit =
  record_
    (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
    [("a", int_ 0), ("b", float_ 0.0)] in
utest checkWellFormed recLit with [] in

let recLitArrowType =
  bind_
    (let_ "id" (tyarrow_ tyint_ tyint_) (lam_ "x" tyint_ (var_ "x")))
    (record_ (tyrecord_ [("a", arrowType)])
             [("a", withType arrowType (var_ "id"))]) in
utest checkWellFormed recLitArrowType with [CudaTypeError i] in

let recUpdate =
  bind_
    (let_ "r" (tyrecord_ [("a", tyint_)]) (urecord_ [("a", int_ 3)]))
    (withInfo i (recordupdate_ (var_ "r") "a" (int_ 4))) in
utest checkWellFormed recUpdate with [CudaExprError i] in

let optionType = withInfo i (type_ "Option" tyunknown_) in
utest checkWellFormed optionType with [CudaExprError i] in

let conDef = bindall_ [
  withInfo i (type_ "Option" tyunknown_),
  withInfo i (condef_ "Some" (tyarrow_ tyint_ (tyvar_ "Option"))),
  int_ 0] in
utest checkWellFormed conDef with [CudaExprError i, CudaExprError i] in

let ext = withInfo i (ext_ "sin" false (tyarrow_ tyfloat_ tyfloat_)) in
utest checkWellFormed ext with [CudaExprError i] in

let utestTerm = withInfo i (utest_ (int_ 1) (int_ 2) (int_ 0)) in
utest checkWellFormed ext with [CudaExprError i] in

let fileRead =
  app_
    (withInfo i (const_ (tyarrow_ tystr_ tystr_) (CFileRead ())))
    (str_ "test.txt") in
utest checkWellFormed fileRead with [CudaConstantError i] in

let matchBoolPat =
  bind_
    (let_ "x" tyint_ (int_ 3))
    (match_ (gti_ (var_ "x") (int_ 0)) ptrue_ (int_ 1) (int_ 0)) in
utest checkWellFormed matchBoolPat with [] in

let matchIntPat =
  bind_
    (let_ "x" tyint_ (int_ 3))
    (withInfo i (match_ (var_ "x") (pint_ 4) (int_ 1) (int_ 0))) in
utest checkWellFormed matchIntPat with [CudaPatternError i] in

let matchCharPat =
  bind_ 
    (let_ "c" tychar_ (char_ 'x'))
    (withInfo i (match_ (var_ "c") (pchar_ 'x') (int_ 1) (int_ 0))) in
utest checkWellFormed matchCharPat with [CudaPatternError i] in

let recTy = tyrecord_ [("a", tyint_), ("b", tyfloat_)] in
let matchRecordPat =
  bind_
    (let_ "r" recTy (record_ recTy [("a", int_ 2), ("b", float_ 3.0)]))
    (match_ (var_ "r") (prec_ [("a", pvar_ "a"), ("b", pvarw_)]) (int_ 1) (int_ 0)) in
utest checkWellFormed matchRecordPat with [] in

()
