include "lexer.mc"
include "mexpr/info.mc"
include "mexpr/eq.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/json-debug.mc"
include "json.mc"
include "seq.mc"
include "parser/breakable.mc"
include "name.mc"

type BreakableOp lstyle rstyle
con OpAtom: use Ast in Expr -> BreakableOp LClosed RClosed
con OpNeg: Info -> BreakableOp LClosed ROpen
con OpApp: Info -> BreakableOp LOpen ROpen

type ParseResult a = Result (Info, String) (Info, String) a

let parseOk:  all a. a              -> ParseResult a = lam a. result.ok a
let parseErr: all a. (Info, String) -> ParseResult a = lam e. result.err e

lang AstParserBase = Lexer
  sem config: () -> Config BreakableOp

  sem topAllowed: TopAllowedFunc BreakableOp
  sem leftAllowed: LeftAllowedFunc BreakableOp
  sem rightAllowed: RightAllowedFunc BreakableOp
  sem parenAllowed: ParenAllowedFunc BreakableOp
  sem groupingsAllowed: GroupingsAllowedFunc BreakableOp

  sem constructPrefix: (BreakableOp LClosed ROpen, Expr) -> Expr
  sem constructInfix: (BreakableOp LOpen ROpen, Expr, Expr) -> Expr
  sem constructPostfix: (BreakableOp LOpen RClosed, Expr) -> Expr

  sem canStartExpr: NextTokenResult -> Bool

  sem parseExpr: NextTokenResult -> ParseResult (Expr, NextTokenResult)
  sem parseExprRClosed:  State BreakableOp RClosed -> NextTokenResult -> ParseResult (Expr, NextTokenResult)
  sem parseExprROpen:    State BreakableOp ROpen   -> NextTokenResult -> ParseResult (Expr, NextTokenResult)
  sem finalizeParseExpr: State BreakableOp RClosed -> NextTokenResult -> ParseResult (Expr, NextTokenResult)

  sem parseDecl: NextTokenResult -> ParseResult (Decl, NextTokenResult)
  sem parseType: NextTokenResult -> ParseResult (Type, NextTokenResult)
  sem parseKind: NextTokenResult -> ParseResult (Kind, NextTokenResult)
  sem parsePat:  NextTokenResult -> ParseResult (Pat,  NextTokenResult)

  sem config =
  | _ ->
    {
      topAllowed = #frozen"topAllowed",
      leftAllowed = #frozen"leftAllowed",
      rightAllowed = #frozen"rightAllowed",
      parenAllowed = #frozen"parenAllowed",
      groupingsAllowed = #frozen"groupingsAllowed"
    }

  sem topAllowed =
  | _ -> true

  sem leftAllowed =
  | _ -> true

  sem rightAllowed =
  | _ -> true

  sem parenAllowed =
  | _ -> GNeither ()

  sem groupingsAllowed =
  | _ -> GLeft ()

  sem canStartExpr =
  | { token = EOFTok {} } -> false
  | _ -> true

  sem parseExpr =
  | next ->
    let state = breakableInitState () in
    parseExprROpen state next

  sem parseExprRClosed state =
  | next ->
    finalizeParseExpr state next

  sem finalizeParseExpr state =
  | next ->
    match breakableFinalizeParse (config ()) state with Some sppf then
      -- breakableReportAmbiguities ?
      let expr = breakableConstructSimple {
        constructAtom = lam op. match op with OpAtom expr in expr,
        constructInfix = lam op. lam lhs. lam rhs. constructInfix (op, lhs, rhs),
        constructPrefix = lam op. lam rhs. constructPrefix (op, rhs),
        constructPostfix = lam op. lam lhs. constructPostfix (op, lhs)
      } sppf in
      parseOk (expr, next)
    else
      parseErr (next.info, "Breakable parse error")
end

lang IntParser = AstParserBase + IntAst
  sem parseExprROpen state =
  | { token = IntTok { val = val, info = info }, stream = stream } ->
    let expr = TmConst {
      val = CInt { val = val },
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken stream)
end

lang FloatParser = AstParserBase + FloatAst
  sem parseExprROpen state =
  | { token = FloatTok { val = val, info = info }, stream = stream } ->
    let expr = TmConst {
      val = CFloat { val = val },
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken stream)
end

lang NegParser = AstParserBase + ArithIntAst + ArithFloatAst + AppAst
  sem parseExprROpen state =
  | { token = OperatorTok { val = "-", info = info }, stream = stream } ->
    let state = breakableAddPrefix (config ()) (OpNeg info) state in
    parseExprROpen state (nextToken stream)

  sem constructPrefix =
  | (OpNeg info, TmConst { val = CInt { val = val }, info = info2 }) ->
    let info = mergeInfo info info2 in
    TmConst {
      val = CInt { val = negi val },
      ty = ityunknown_ info,
      info = info
    }

  | (OpNeg info, TmConst { val = CFloat { val = val }, info = info2 }) ->
    let info = mergeInfo info info2 in
    TmConst {
      val = CFloat { val = negf val },
      ty = ityunknown_ info,
      info = info
    }

  | (OpNeg info, rhs) ->
    let info2 = mergeInfo info (infoTm rhs) in
    TmApp {
      lhs = TmConst {
        val = CNegi {},
        ty = ityunknown_ info,
        info = info
      },
      rhs = rhs,
      ty = ityunknown_ info2,
      info = info2
    }
end

lang VarParser = AstParserBase + VarAst
  sem parseExprROpen state =
  | { token = LIdentTok { val = val, info = info }, stream = stream } ->
    let expr = TmVar {
      ident = nameNoSym val,
      ty = ityunknown_ info,
      info = info,
      frozen = false -- TODO
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken stream)
end

lang AppParser = AstParserBase + AppAst
  sem parseExprRClosed state =
  | { token = token, info = info } & next ->
    match canStartExpr next with true then
      match breakableAddInfix (config ()) (OpApp info) state with Some(state) then
        parseExprROpen state next
      else
        parseErr (info, "Breakable add infix error")
    else
      finalizeParseExpr state next

  sem constructInfix =
  | (OpApp info, lhs, rhs) ->
    let info = mergeInfo (infoTm lhs) (infoTm rhs) in
    TmApp {
      lhs = lhs,
      rhs = rhs,
      ty = ityunknown_ info,
      info = info
    }
end

lang ParenParser = AstParserBase
  sem canStartExpr =
  | { token = RParenTok {} } -> false

  sem parseExprROpen state =
  | { token = LParenTok {}, stream = stream } ->
    result.bind (parseExpr (nextToken stream)) (lam a.
      match a with (expr, next) in
      match next with { token = RParenTok {}, stream = stream } then
        let state = breakableAddAtom (config ()) (OpAtom expr) state in
        parseExprRClosed state (nextToken stream)
      else
        parseErr (next.info, "Missing closing parenthesis")
    )
end

lang BoolParser = AstParserBase + BoolAst
  sem parseExprROpen state =
  | { token = LIdentTok { val = "true", info = info}, stream = stream} ->
    let expr = TmConst {
      val = CBool { val = true },
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken stream)
  | { token = LIdentTok { val = "false", info = info}, stream = stream} ->
    let expr = TmConst {
      val = CBool { val = false },
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken stream)
end

lang CharParser = AstParserBase + CharAst
  sem parseExprROpen state =
  | { token = CharTok { val = val, info = info }, stream = stream } ->
    let expr = TmConst {
      val = CChar { val = val },
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken stream)
end

lang StringParser = AstParserBase + SeqAst + CharAst
  sem parseExprROpen state =
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
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken stream)
end

lang NotImplementedParser = AstParserBase
  sem parseExprROpen state =
  | next ->
    let str = concat "Not implemented: " (tokToStr next.token) in
    parseErr (next.info, str)
end

lang AstParser =
    IntParser
  + FloatParser
  + BoolParser
  + CharParser
  + StringParser
  + NegParser
  + VarParser
  + AppParser
  + ParenParser
end

lang TestParser =
    AstParser
  + NotImplementedParser
  + MExprPrettyPrint
  + MExprEq
  + MExprToJson
end

mexpr

use TestParser in
use BootParser in

let lex = lam str. nextToken {pos = initPos "internal", str = str} in
let parse = lam str. result.map (lam a. a.0) (parseExpr (lex str)) in

let bootArg = { _defaultBootParserParseMExprStringArg () with builtin = [] } in
let parseBoot = lam str. parseMExprString bootArg str in

let jsonStr = lam expr. json2string (exprToJson expr) in

let compare = lam str.
  let a = parse str in
  let b = parseBoot str in

  match (result.toOption a, result.toOption b) with (Some a, Some b) then
    eqString (jsonStr a) (jsonStr b)
  else
    false
  in

let printAst = lam expr. printLn (jsonStr expr) in

-- printLn "";
-- printAst (parseBoot "addi (addi 1 2) 3");
-- printAst (parse "addi (addi 1 2) 3");

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

utest compare "addi 1 2" with true in
utest compare "addi 1 2 3" with true in
utest compare "addi addi 1 2 3" with true in
utest compare "addi (addi 1 2) 3" with true in
utest compare "addi 1 (addi 2 3)" with true in

()
