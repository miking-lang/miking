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

  syn CExpr =
  | CEMap {f : CExpr, s : CExpr}
  | CEThreadIdx {dim : CudaDimension}
  | CEBlockIdx {dim : CudaDimension}
  | CEBlockDim {dim : CudaDimension}
  | CEGridDim {dim : CudaDimension}
  | CEMapKernel {f : CExpr, s : CExpr, sTy : CType, retTy : CType,
                 opsPerThread : Int}
  | CEKernelApp {fun : Name, gridSize : CExpr, blockSize : CExpr,
                 args : [CExpr]}

  sem smapAccumLCExprCExpr (f : acc -> a -> (acc, b)) (acc : acc) =
  | CEMap t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, CEMap {{t with f = tf} with s = s})
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
  | CuTTop {attrs : [CudaAttribute], top : CTop}

  syn CudaProg =
  | CuPProg {includes : [String], tops : [CuTop]}
end
