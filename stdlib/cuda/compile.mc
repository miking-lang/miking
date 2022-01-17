include "c/compile.mc"
include "cuda/ast.mc"

lang CudaCompile = MExprCCompileAlloc + CudaAst
  sem compileOp (t: Expr) (args: [CExpr]) =
  | CMap _ ->
    CEMap {f = get args 0, s = get args 1}
end
