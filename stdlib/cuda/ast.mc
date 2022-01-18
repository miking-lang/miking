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

  syn CExpr =
  | CEMap {f : CExpr, s : CExpr}
  | CEThreadIdx {dim : CudaDimension}
  | CEBlockIdx {dim : CudaDimension}
  | CEBlockDim {dim : CudaDimension}
  | CEKernelApp {fun : Name, gridSize : (CExpr, CExpr, CExpr),
                 blockSize : (CExpr, CExpr, CExpr), sharedMem : CExpr,
                 args : [CExpr]}

  syn CuTop =
  | CuTTop {attrs : [CudaAttribute], top : CTop}

  syn CudaProg =
  | CuPProg {includes : [String], tops : [CuTop]}
end
