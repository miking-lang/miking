-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/parser.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"
include "seq.mc"

lang MExpr = MExprAst + MExprParser + MExprEval + MExprPrettyPrint


-- Evaluate an expression into a value expression
let evalExpr : Expr -> Expr =
  use MExpr in lam t. eval {env = assocEmpty} (symbolize assocEmpty t)

-- Parse a string and then evaluate into a value expression
let evalStr : String -> Expr =
  lam str. use MExpr in evalExpr (parseExpr (initPos "") 0 str).val

-- Parse a string and then evaluate into a value, and pretty print
-- as a string.
let evalStrToStr : String -> String =
  lam str. expr2str (evalStr str)

-- Same as evalStrToStr, but removes all white space. Good for testing.
let evalTest : String -> String = lam str. 
  filter (lam x. not (or (or (eqchar x ' ') (eqchar x '\n')) (eqchar x '\t')))
  (evalStrToStr str)

utest evalTest "true" with "true"
utest evalTest "false" with "false"
utest evalTest "0" with "0"
utest evalTest "3421" with "3421"
utest evalTest "if true then 10 else 20" with "10"
utest evalTest "if false then 10 else 20" with "20"
utest evalTest "if false then true else if true then 1 else 2" with "1"
utest evalTest "if true then if false then 1 else 2 else 3" with "2"
utest evalTest "if true then (if false then 1 else 2) else 3" with "2"
utest evalTest " [ ] " with "\"\""
utest evalTest " [ 12 ] " with "[12]"
utest evalTest " [ 12 , ( 17 ), 789 ] " with "[12,17,789]"
utest evalTest " \"hi\" " with "\"hi\""
utest evalStrToStr " \" f\\\\  \\n \\\" \" " with "\" f\\  \n \" \""
utest evalTest " [ 'a' , 'b' , 'c'] " with "\"abc\""

