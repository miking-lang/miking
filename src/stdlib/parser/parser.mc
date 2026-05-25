include "lexer.mc"
include "mexpr/info.mc"
include "mexpr/eq.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"

lang AstParser = Lexer
  sem parseExpr: NextTokenResult -> (Expr, NextTokenResult)
  sem parseDecl: NextTokenResult -> (Decl, NextTokenResult)
  sem parseType: NextTokenResult -> (Type, NextTokenResult)
  sem parseKind: NextTokenResult -> (Kind, NextTokenResult)
  sem parsePat:  NextTokenResult -> (Pat,  NextTokenResult)
end

lang IntParser = AstParser + IntAst
  sem parseExpr =
  | { token = IntTok { val = val, info = info }, stream = stream } ->
    let expr = TmConst {
      val = CInt { val = val },
      ty = tyint_,
      info = info
    } in
    (expr, nextToken stream)
end

lang BoolParser = AstParser + BoolAst
  sem parseExpr =
  | { token = LIdentTok { val = "true", info = info}, stream = stream} ->
    let expr = TmConst {
      val = CBool { val = true },
      ty = tybool_,
      info = info
    } in
    (expr, nextToken stream)
  | { token = LIdentTok { val = "false", info = info}, stream = stream} ->
    let expr = TmConst {
      val = CBool { val = false },
      ty = tybool_,
      info = info
    } in
    (expr, nextToken stream)
end


lang TestParser = IntParser + BoolParser + MExprPrettyPrint + Eq end

mexpr

use TestParser in

let lex = lam str. nextToken {pos = initPos "test", str = str} in
let parse = lam str. match parseExpr (lex str) with (expr, next) in expr in

let expr = parse "5" in

utest match expr with TmConst { val = CInt { val = val }} in val with 5 in
utest match expr with TmConst { info = info} in info with infoVal "test" 1 0 1 1 in

match parseExpr (lex "true") with (expr, next) in
utest match expr with TmConst { val = CBool { val = val }} in val with true in

match parseExpr (lex "false") with (expr, next) in
utest match expr with TmConst { val = CBool { val = val }} in val with false in


use BootParser in

let bootArg = _defaultBootParserParseMExprStringArg () in
let parseBoot = lam str.
  match parseMExprString bootArg str with (ResultOk { value = bootExpr}) in bootExpr in

let expr = parse "5" in
let bootExpr = parseBoot "5" in

utest expr with bootExpr using eqExpr in

()
