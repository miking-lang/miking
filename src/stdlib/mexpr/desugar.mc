include "mexpr/ast.mc"

lang Desugar = Ast
  sem desugarExpr: Expr -> Expr
  sem desugarExpr =
  | tm -> smap_Expr_Expr desugarExpr tm
end
