include "javascript/ast.mc"


-------------------------------
-- OPERATOR HELPER FUNCTIONS --
-------------------------------

let _binOp : JSBinOp -> [JSExpr] -> JSEBinOp = use JSExprAst in
  lam op. lam args. JSEBinOp { op = op, lhs = head args, rhs = last args }

let _unOp : JSUnOp -> [JSExpr] -> JSEUnOp = use JSExprAst in
  lam op. lam args. JSEUnOp { op = op, rhs = head args }

let _assign : JSExpr -> JSExpr -> JSEBinOp = use JSExprAst in
  lam lhs. lam rhs. JSEBinOp { op  = JSOAssign {}, lhs = lhs, rhs = rhs }
