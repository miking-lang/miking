
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/parser.mc"

lang MExpr = MExprAst + MExprEval


mexpr

use MExpr in

-- Evaluation shorthand used in tests below
let eval =
  lam t. eval {env = assocEmpty} (symbolize assocEmpty t) in

utest eval (app_ (ulam_ "x" (var_ "x")) (int_ 1)) with int_ 1 in
utest eval (addi_ (int_ 1) (int_ 2)) with int_ 3 in



()
