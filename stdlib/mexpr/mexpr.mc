-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/parser.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"

lang MExpr = MExprAst + MExprParser + MExprEval + MExprPrettyPrint


-- BUG: eval and evalStr should be possible to have at the top level instead of
-- under mexpr, but we get an error in such a case. It might be a bug in the name mangling
--let eval =
--  use MExpr in lam t. eval {env = assocEmpty} (symbolize assocEmpty t)

--let evalStr = lam str.
--  use MExpr in expr2str (eval (parseExpr (initPos "") str).val)


mexpr

use MExpr in

let eval =
  lam t. eval {env = assocEmpty} (symbolize assocEmpty t) in

let evalStr = lam str.
  expr2str (eval (parseExpr (initPos "") str).val) in

-- Evaluation shorthand used in tests below


utest eval (app_ (ulam_ "x" (var_ "x")) (int_ 1)) with int_ 1 in
utest eval (addi_ (int_ 1) (int_ 2)) with int_ 3 in

-- Evaluate parsed strings

utest evalStr "true" with "true" in
utest evalStr "false" with "false" in
utest evalStr "0" with "0" in
utest evalStr "3421" with "3421" in
utest evalStr "if true then 10 else 20" with "10" in
utest evalStr "if false then 10 else 20" with "20" in
utest evalStr "if false then true else if true then 1 else 2" with "1" in
utest evalStr "if true then if false then 1 else 2 else 3" with "2" in


()
