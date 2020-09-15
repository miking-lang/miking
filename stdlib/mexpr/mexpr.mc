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


-- Evaluate an expression into a value expression
let evalExpr : Expr -> Expr =
  use MExpr in lam t. eval {env = assocEmpty} (symbolize assocEmpty t)

-- Parse a string and then evaluate into a value expression
let evalStr : String -> Expr =
  lam str. use MExpr in evalExpr (parseExpr (initPos "") str).val

-- Parse a string and then evaluate into a value, and pretty print
-- as a string.
let evalStrToStr : String -> String =
  lam str. expr2str (evalStr str)


utest evalStrToStr "true" with "true"
utest evalStrToStr "false" with "false"
utest evalStrToStr "0" with "0"
utest evalStrToStr "3421" with "3421"
utest evalStrToStr "if true then 10 else 20" with "10"
utest evalStrToStr "if false then 10 else 20" with "20"
utest evalStrToStr "if false then true else if true then 1 else 2" with "1"
utest evalStrToStr "if true then if false then 1 else 2 else 3" with "2"
utest evalStrToStr "if true then (if false then 1 else 2) else 3" with "2"
