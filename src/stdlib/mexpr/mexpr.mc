-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "ast.mc"
include "ast-builder.mc"
include "eval.mc"
include "parser.mc"
include "info.mc"
include "pprint.mc"
include "seq.mc"

lang MExpr = MExprAst + MExprParser + MExprEval + MExprPrettyPrint + MExprSym
end

-- Evaluate an expression into a value expression
let evalExpr : use MExpr in Expr -> Expr =
  use MExpr in lam t. eval (evalCtxEmpty ()) (symbolize t)

-- Parse a string and then evaluate into a value expression
let evalStr : use MExpr in String -> Expr =
  lam str. use MExpr in evalExpr (parseExpr (initPos "") str)

-- Parse a string and then evaluate into a value, and pretty print
-- as a string.
let evalStrToStr : String -> String =
  use MExpr in lam str. expr2str (evalStr str)

-- Same as evalStrToStr, but removes all white space. Good for testing.
let evalTest : String -> String = lam str.
  filter (lam x. not (or (or (eqChar x ' ') (eqChar x '\n')) (eqChar x '\t')))
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
utest evalStrToStr " \" f\\\\  \\n \\\" \" " with "\" f\\\\  \\n \\\" \""
utest evalTest " [ 'a' , 'b' , 'c'] " with "\"abc\""
utest evalTest " let x = 73 in x" with "73"
utest evalTest " let foo1 = 19 in \n let foo2 = 22 in [foo1,foo2]" with "[19,22]"
utest evalTest " let iftrue = 5 in iftrue" with "5"
