include "c/ast.mc"
include "c/pprint.mc"

lang CudaAST = CAst
 syn CExpr =
 | CEMap {f : Expr, s : Expr}
end

lang CudaPrettyPrint = CPrettyPrint + CProgPrettyPrint
