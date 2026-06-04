include "lexer.mc"
include "mexpr/info.mc"
include "mexpr/eq.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/json-debug.mc"
include "json.mc"
include "seq.mc"

lang AstParserBase = Lexer
  sem parseExpr: NextTokenResult -> (Expr, NextTokenResult)
  sem parseDecl: NextTokenResult -> (Decl, NextTokenResult)
  sem parseType: NextTokenResult -> (Type, NextTokenResult)
  sem parseKind: NextTokenResult -> (Kind, NextTokenResult)
  sem parsePat:  NextTokenResult -> (Pat,  NextTokenResult)
end

lang IntParser = AstParserBase + IntAst
  sem parseExpr =
  | { token = IntTok { val = val, info = info }, stream = stream } ->
    let expr = TmConst {
      val = CInt { val = val },
      ty = ityunknown_ info,
      info = info
    } in
    (expr, nextToken stream)
end

lang FloatParser = AstParserBase + FloatAst
  sem parseExpr =
  | { token = FloatTok { val = val, info = info }, stream = stream } ->
    let expr = TmConst {
      val = CFloat { val = val },
      ty = ityunknown_ info,
      info = info
    } in
    (expr, nextToken stream)
end

lang NegParser = AstParserBase + IntAst + FloatAst
  sem parseExpr =
  | { token = OperatorTok { val = "-", info = info }, stream = stream } ->
    match parseExpr (nextToken stream) with (expr, next) in
    let val = switch expr
      case TmConst { val = CInt { val = val } } then CInt { val = negi val }
      case TmConst { val = CFloat { val = val } } then CFloat { val = negf val }
    end in
    let info = mergeInfo info (infoTm expr) in
    let expr = TmConst {
      val = val,
      ty = ityunknown_ info,
      info = info
    } in
    (expr, nextToken next.stream)
end

lang BoolParser = AstParserBase + BoolAst
  sem parseExpr =
  | { token = LIdentTok { val = "true", info = info}, stream = stream} ->
    let expr = TmConst {
      val = CBool { val = true },
      ty = ityunknown_ info,
      info = info
    } in
    (expr, nextToken stream)
  | { token = LIdentTok { val = "false", info = info}, stream = stream} ->
    let expr = TmConst {
      val = CBool { val = false },
      ty = ityunknown_ info,
      info = info
    } in
    (expr, nextToken stream)
end

lang CharParser = AstParserBase + CharAst
  sem parseExpr =
  | { token = CharTok { val = val, info = info }, stream = stream } ->
    let expr = TmConst {
      val = CChar { val = val },
      ty = ityunknown_ info,
      info = info
    } in
    (expr, nextToken stream)
end

lang StringParser = AstParserBase + SeqAst + CharAst
  sem parseExpr =
  | { token = StringTok { val = val, info = info }, stream = stream } ->
    let expr = TmSeq {
      tms = map (lam ch. TmConst {
        val = CChar { val = ch },
        ty = ityunknown_ info,
        info = info
      }) val,
      ty = ityunknown_ info,
      info = info
    } in
    (expr, nextToken stream)
end

lang NotImplementedParser = AstParserBase
  sem parseExpr =
  | { token = token } ->
    let str = concat "Not implemented: " (tokToStr token) in
    error str
end

lang AstParser = IntParser + FloatParser + BoolParser + CharParser + StringParser + NegParser end

lang TestParser = AstParser + NotImplementedParser + MExprPrettyPrint + MExprEq + MExprToJson end

mexpr

use TestParser in
use BootParser in

let lex = lam str. nextToken {pos = initPos "internal", str = str} in
let parse = lam str. match parseExpr (lex str) with (expr, next) in expr in

let bootArg = _defaultBootParserParseMExprStringArg () in
let parseBoot = lam str.
  match parseMExprString bootArg str with (ResultOk { value = bootExpr}) in bootExpr in

let jsonStr = lam expr. json2string (exprToJson expr) in

-- let compare = lam str. eqExpr (parse str) (parseBoot str) in
let compare = lam str. eqString (jsonStr (parse str)) (jsonStr (parseBoot str)) in

let printAst = lam expr. printLn (jsonStr expr) in

-- printAst (parseBoot "\"test\"");

utest compare "0" with true in
utest compare "1" with true in
utest compare "-1" with true in

utest compare "0.0" with true in
utest compare "1.0" with true in
utest compare "-1.0" with true in

utest compare "true" with true in
utest compare "false" with true in

utest compare "'a'" with true in
utest compare "'😊'" with true in

utest compare "\"test\"" with true in

()
