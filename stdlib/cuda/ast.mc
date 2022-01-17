include "c/ast.mc"
include "mexpr/ast.mc"

lang CudaAst = CAst + MExprAst
  syn CudaDimension =
  | DimX ()
  | DimY ()
  | DimZ ()

  syn CExpr =
  | CEMap {f : CExpr, s : CExpr}
  | CEThreadIdx {dim : CudaDimension}
  | CEBlockIdx {dim : CudaDimension}
  | CEBlockDim {dim : CudaDimension}
  | CEKernelApp {fun : Name, gridSize : (CExpr, CExpr, CExpr),
                 blockSize : (CExpr, CExpr, CExpr), sharedMem : CExpr,
                 args : [CExpr]}

  syn CTop =
  | CTGlobalAttr {top : CTop}
  | CTDeviceAttr {top : CTop}
end
