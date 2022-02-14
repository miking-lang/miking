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

  syn CType =
  | CTyDecltype {e : CExpr}
  | CTyRmPtr {ty : CType}

  sem smapAccumLCTypeCType (f : acc -> CType -> (acc, b)) (acc : acc) =
  | CTyRmPtr t ->
    match f acc t.ty with (acc, ty) in
    (acc, CTyRmPtr {t with ty = ty})

  syn CExpr =
  | CEMap {f : CExpr, s : CExpr}
  | CEFoldl {f : CExpr, acc : CExpr, s : CExpr}
  | CEThreadIdx {dim : CudaDimension}
  | CEBlockIdx {dim : CudaDimension}
  | CEBlockDim {dim : CudaDimension}
  | CEGridDim {dim : CudaDimension}
  | CEMapKernel {f : CExpr, s : CExpr, outTy : CType, opsPerThread : Int}
  | CEKernelApp {fun : Name, gridSize : CExpr, blockSize : CExpr,
                 args : [CExpr]}

  sem smapAccumLCExprCExpr (f : acc -> a -> (acc, b)) (acc : acc) =
  | CEMap t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, CEMap {{t with f = tf} with s = s})
  | CEFoldl t ->
    match f acc t.f with (acc, tf) in
    match f acc t.acc with (acc, tacc) in
    match f acc t.s with (acc, s) in
    (acc, CEFoldl {{{t with f = tf} with acc = tacc} with s = s})
  | CEMapKernel t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, CEMapKernel {{t with f = tf} with s = s})
  | CEKernelApp t ->
    match f acc t.gridSize with (acc, gridSize) in
    match f acc t.blockSize with (acc, blockSize) in
    match mapAccumL f acc t.args with (acc, args) in
    (acc, CEKernelApp {{{t with gridSize = gridSize}
                           with blockSize = blockSize}
                           with args = args})
  | expr & (CEThreadIdx _ | CEBlockIdx _ | CEBlockDim _) -> (acc, expr)

  syn CuTop =
  | CuTTop {templates : [Name], attrs : [CudaAttribute], top : CTop}

  syn CudaProg =
  | CuPProg {includes : [String], tops : [CuTop]}
end
