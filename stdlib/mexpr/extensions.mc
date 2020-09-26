----------------------------------------------------
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- This file adds syntactic sugar to MExpr by
-- extending the MExpr parser and transforming the
-- code into standard MExpr.
---------------------------------------------------- 

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/parser.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"


-- Fragment for constructing constant binary opertors. Used by InfixArithParser
lang MExprMakeConstBinOp = ArithIntAst + AppAst
  sem makeConstBinOp (n: Int) (p: Pos) (xs: String)
                     (assoc: Associativity) (prec: Int) =
  | op ->
    let p2 = advanceCol p 1 in
    Some {
      val = lam x. lam y.
        let op = TmConst {val = op, fi = makeInfo p p2} in
        let app = lam x. lam y. 
                TmApp {lhs = x, rhs = y, fi = NoInfo ()} in
                --TmApp {lhs = x, rhs = y, fi = mergeInfo (info x) (info y)} in
		--
		--BUG: the above should work, but the info function does not exist
		-- for TmApp, altough languge fragment AppAst is included.
        let resx = (app op x) in
        let res = (app (app op x) y) in
        res, 
      pos = p2, str = xs, assoc = assoc, prec = prec}
end


-- Demonstrates the use of infix operators. The syntax is not part of basic MCore
lang ExprInfixArithParser =  ExprInfixParser + ArithIntAst + MExprMakeConstBinOp 
  sem parseInfixImp (p: Pos) =
  | "+" ++ xs -> makeConstBinOp 1 p xs (LeftAssoc ()) 10 (CAddi {})
  | "-" ++ xs -> makeConstBinOp 1 p xs (LeftAssoc ()) 10 (CSubi {})
  | "*" ++ xs -> makeConstBinOp 1 p xs (LeftAssoc ()) 20 (CMuli {})
end


lang MExprParserExt = MExprParserBase + ExprInfixArithParser + ExprInfixParserClosed

lang MExprExt = MExprAst + MExprParserExt + MExprEval + MExprPrettyPrint


-- Evaluate an expression into a value expression
let evalExpr : Expr -> Expr =
  use MExprExt in lam t. eval {env = assocEmpty} (symbolize assocEmpty t)

-- Parse a string and then evaluate into a value expression
let evalStr : String -> Expr =
  lam str. use MExprExt in evalExpr (parseExpr (initPos "") 0 str).val

-- Parse a string and then evaluate into a value, and pretty print
-- as a string.
let evalStrToStr : String -> String =
  lam str. expr2str (evalStr str)


utest evalStrToStr "true" with "true"
utest evalStrToStr "1+2" with "3"
utest evalStrToStr " 2 * 3" with "6"
utest evalStrToStr " 2 + 3 * 4 " with "14"
utest evalStrToStr " 2 + 3 + 4 " with "9"
utest evalStrToStr " (2 + 3) * 4 " with "20"
utest evalStrToStr " 1 + 2 * 3 + 4 " with "11"
utest evalStrToStr " 1 + 2 * ( 3 + 4 ) " with "15"
utest evalStrToStr " 10 - 7 - 2" with "1"
utest evalStrToStr " 10 - (7 - 2)" with "5"
