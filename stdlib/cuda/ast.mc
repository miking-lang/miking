include "c/ast.mc"
include "mexpr/ast.mc"

lang CudaAst = CAst + MExprAst
  syn CudaDimension =
  | CuDX ()
  | CuDY ()
  | CuDZ ()

  syn CudaAttribute =
  | CuAHost ()
  | CuADevice ()
  | CuAGlobal ()
  | CuAExternC ()
  | CuAManaged ()

  syn CType =
  | CTyConst {ty : CType}

  sem smapAccumLCTypeCType f acc =
  | CTyConst t ->
    match f acc t.ty with (acc, ty) in
    (acc, CTyConst {t with ty = ty})

  syn CExpr =
  | CESeqMap {f : CExpr, s : CExpr, sTy : CType, ty : CType}
  | CESeqFoldl {f : CExpr, acc : CExpr, s : CExpr, sTy : CType,
                argTypes : [CType], ty : CType}
  | CESeqLoop {n : CExpr, f : CExpr, argTypes : [CType]}
  | CESeqLoopAcc {ne : CExpr, n : CExpr, f : CExpr, neTy : CType, argTypes : [CType]}
  | CETensorSliceExn {t : CExpr, slice : CExpr, ty : CType}
  | CETensorSubExn {t : CExpr, ofs : CExpr, len : CExpr, ty : CType}
  | CEThreadIdx {dim : CudaDimension}
  | CEBlockIdx {dim : CudaDimension}
  | CEBlockDim {dim : CudaDimension}
  | CEGridDim {dim : CudaDimension}
  | CEMapKernel {f : CExpr, s : CExpr, opsPerThread : Int, sTy : CType, ty : CType}
  | CELoopKernel {n : CExpr, f : CExpr, argTypes : [CType], opsPerThread : Int}
  | CEKernelApp {fun : Name, gridSize : CExpr, blockSize : CExpr,
                 args : [CExpr]}

  sem smapAccumLCExprCExpr f acc =
  | CESeqMap t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, CESeqMap {{t with f = tf} with s = s})
  | CESeqFoldl t ->
    match f acc t.f with (acc, tf) in
    match f acc t.acc with (acc, tacc) in
    match f acc t.s with (acc, s) in
    (acc, CESeqFoldl {{{t with f = tf} with acc = tacc} with s = s})
  | CESeqLoop t ->
    match f acc t.n with (acc, n) in
    match f acc t.f with (acc, tf) in
    (acc, CESeqLoop {{t with n = n} with f = tf})
  | CESeqLoopAcc t ->
    match f acc t.ne with (acc, ne) in
    match f acc t.n with (acc, n) in
    match f acc t.f with (acc, tf) in
    (acc, CESeqLoopAcc {{{t with ne = ne} with n = n} with f = tf})
  | CEMapKernel t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, CEMapKernel {{t with f = tf} with s = s})
  | CELoopKernel t ->
    match f acc t.n with (acc, n) in
    match f acc t.f with (acc, tf) in
    (acc, CELoopKernel {{t with n = n} with f = tf})
  | CEKernelApp t ->
    match f acc t.gridSize with (acc, gridSize) in
    match f acc t.blockSize with (acc, blockSize) in
    match mapAccumL f acc t.args with (acc, args) in
    (acc, CEKernelApp {{{t with gridSize = gridSize}
                           with blockSize = blockSize}
                           with args = args})
  | expr & (CEThreadIdx _ | CEBlockIdx _ | CEBlockDim _) -> (acc, expr)

  syn CStmt =
  | CSIfMacro {cond : CExpr, thn : [CStmt], els : [CStmt]}

  sem smapAccumLCStmtCStmt f acc =
  | CSIfMacro t ->
    match mapAccumL f acc t.thn with (acc, thn) in
    match mapAccumL f acc t.els with (acc, els) in
    (acc, CSIfMacro {{t with thn = thn} with els = els})

  syn CuTop =
  | CuTTop {attrs : [CudaAttribute], top : CTop}

  syn CudaProg =
  | CuPProg {includes : [String], tops : [CuTop]}
end
