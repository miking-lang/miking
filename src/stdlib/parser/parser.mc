/-

This will be a parser for MCore.
It is work in progress.

The parser is designed to be as extensible as possible.
It is built on top of the breakable libarary.

The new parser is simply tested against the ocaml boot parser.
The tests checks that the parsed AST is identical.

-/

include "lexer.mc"
include "mexpr/info.mc"
include "mexpr/eq.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/json-debug.mc"
include "json.mc"
include "seq.mc"
include "map.mc"
include "parser/breakable.mc"
include "name.mc"

type BreakableOp lstyle rstyle
con OpAtom: use Ast in Expr -> BreakableOp LClosed RClosed
con OpNeg: Info -> BreakableOp LClosed ROpen
con OpApp: Info -> BreakableOp LOpen ROpen

type ParseResult w a = Result w (Info, String) a

let parseOk:  all w. all a. a              -> ParseResult w a = lam a. result.ok a
let parseErr: all w. all a. (Info, String) -> ParseResult w a = lam e. result.err e
let parseErrs: all w. all a. [(Info, String)] -> ParseResult w a = lam errs.
  foldl1 result.withAnnotations (map result.err errs)

lang AstParserBase = Lexer + Ast
  -- breakable related stuff
  sem config: () -> Config BreakableOp
  sem topAllowed: TopAllowedFunc BreakableOp
  sem leftAllowed: LeftAllowedFunc BreakableOp
  sem rightAllowed: RightAllowedFunc BreakableOp
  sem parenAllowed: ParenAllowedFunc BreakableOp
  sem groupingsAllowed: GroupingsAllowedFunc BreakableOp
  sem terminalInfos: all lstyle. all rstyle. BreakableOp lstyle rstyle -> [Info]
  sem getInfo: all lstyle. all rstyle. BreakableOp lstyle rstyle -> Info
  sem constructPrefix: (BreakableOp LClosed ROpen, Expr) -> Expr
  sem constructInfix: (BreakableOp LOpen ROpen, Expr, Expr) -> Expr
  sem constructPostfix: (BreakableOp LOpen RClosed, Expr) -> Expr

  -- used to deal with function applications
  sem canStartExpr: NextTokenResult -> Bool

  sem parseExpr: all w. NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseExprRClosed:  all w. State BreakableOp RClosed -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseExprROpen:    all w. State BreakableOp ROpen   -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem finalizeParseExpr: all w. State BreakableOp RClosed -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)

  sem parseDecl: all w. NextTokenResult -> ParseResult w (Decl, NextTokenResult)
  sem parseType: all w. NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem parseKind: all w. NextTokenResult -> ParseResult w (Kind, NextTokenResult)
  sem parsePat:  all w. NextTokenResult -> ParseResult w (Pat,  NextTokenResult)

  sem config =
  | _ ->
    {
      topAllowed = #frozen"topAllowed",
      leftAllowed = #frozen"leftAllowed",
      rightAllowed = #frozen"rightAllowed",
      parenAllowed = #frozen"parenAllowed",
      groupingsAllowed = #frozen"groupingsAllowed"
    }


  -- Default breakable config

  sem topAllowed =
  | _ -> true

  sem leftAllowed =
  | _ -> true

  sem rightAllowed =
  | _ -> true

  sem parenAllowed =
  | _ -> GEither ()

  sem groupingsAllowed =
  | _ -> GLeft ()

  sem terminalInfos =
  | op -> [getInfo op]

  sem canStartExpr =
  | { token = EOFTok {} } -> false
  | _ -> true


  -- The main entry point
  sem parseExpr =
  | cur ->
    let state = breakableInitState () in
    parseExprROpen state cur

  sem parseExprRClosed state =
  | cur ->
    finalizeParseExpr state cur

  sem finalizeParseExpr state =
  | cur ->
    match breakableFinalizeParse (config ()) state with Some sppf then
      let config: BreakableErrorHighlightConfig BreakableOp = {
        parenAllowed = #frozen"parenAllowed",
        topAllowed = #frozen"topAllowed",
        terminalInfos = #frozen"terminalInfos",
        getInfo = #frozen"getInfo",
        lpar = "(",
        rpar = ")"
      } in
      let errs = breakableDefaultHighlight config cur.stream.str sppf in
      match errs with [first] ++ _ then
        parseErrs errs
      else
        let expr = breakableConstructSimple {
          constructAtom = lam op. match op with OpAtom expr in expr,
          constructInfix = lam op. lam lhs. lam rhs. constructInfix (op, lhs, rhs),
          constructPrefix = lam op. lam rhs. constructPrefix (op, rhs),
          constructPostfix = lam op. lam lhs. constructPostfix (op, lhs)
        } sppf in
        parseOk (expr, cur)
    else
      parseErr (cur.info, "Breakable parse error")
end

lang IntParser = AstParserBase + IntAst
  sem parseExprROpen state =
  | { token = IntTok { val = val } } & cur ->
    let expr = TmConst {
      val = CInt { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseType =
  | { token = UIdentTok { val = "Int" } } & cur ->
    let typ = ityint_ cur.info in
    parseOk (typ, nextToken cur.stream)
end

lang FloatParser = AstParserBase + FloatAst
  sem parseExprROpen state =
  | { token = FloatTok { val = val } } & cur ->
    let expr = TmConst {
      val = CFloat { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

lang NegParser = AstParserBase + ArithIntAst + ArithFloatAst + AppAst
  sem parseExprROpen state =
  | { token = OperatorTok { val = "-" } } & cur ->
    let state = breakableAddPrefix (config ()) (OpNeg cur.info) state in
    parseExprROpen state (nextToken cur.stream)

  -- Two special cases if the rhs is a constant int or float
  sem constructPrefix =
  | (OpNeg info, TmConst { val = CInt { val = val } } & expr) ->
    let info = mergeInfo info (infoTm expr) in
    TmConst {
      val = CInt { val = negi val },
      ty = ityunknown_ info,
      info = info
    }

  | (OpNeg info, TmConst { val = CFloat { val = val } } & expr) ->
    let info = mergeInfo info (infoTm expr) in
    TmConst {
      val = CFloat { val = negf val },
      ty = ityunknown_ info,
      info = info
    }

  -- Normal case
  | (OpNeg info, rhs) ->
    let info2 = mergeInfo info (infoTm rhs) in
    TmApp {
      lhs = TmConst {
        val = CNegi {}, -- TODO: What about CNegf?
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
  | { token = LIdentTok { val = val } } & cur ->
    let expr = TmVar {
      ident = nameNoSym val,
      ty = ityunknown_ cur.info,
      info = cur.info,
      frozen = false -- TODO: Always false?
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

lang AppParser = AstParserBase + AppAst
  sem parseExprRClosed state =
  | { token = token } & cur ->
    -- check if the next token can be part of the current expression.
    match canStartExpr cur with true then
      match breakableAddInfix (config ()) (OpApp cur.info) state with Some(state) then
        parseExprROpen state cur
      else
        parseErr (cur.info, "Breakable add infix error")
    else
      finalizeParseExpr state cur

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

lang ParenParser = AstParserBase + RecordAst
  sem canStartExpr =
  | { token = RParenTok {} } -> false

  sem parseExprROpen state =
  | { token = LParenTok {} } & open ->
    match (nextToken open.stream) with { token = RParenTok {} } & close then
      -- this is a unit
      let info = mergeInfo open.info close.info in
      let expr = TmRecord {
        bindings = mapEmpty cmpSID,
        ty = ityunknown_ info,
        info = info
      } in
      let state = breakableAddAtom (config ()) (OpAtom expr) state in
      parseExprRClosed state (nextToken close.stream)
    else
      -- start parsing a new expression at (
      result.bind (parseExpr (nextToken open.stream)) (lam expr.
        match expr with (expr, cur) in
        -- and check for a following )
        match cur with { token = RParenTok {} } & close then
          let state = breakableAddAtom (config ()) (OpAtom expr) state in
          parseExprRClosed state (nextToken close.stream)
        else
          parseErr (cur.info, "Missing closing parenthesis")
      )
end

lang BoolParser = AstParserBase + BoolAst
  sem parseExprROpen state =
  | { token = LIdentTok { val = "true" } } & cur ->
    let expr = TmConst {
      val = CBool { val = true },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
  | { token = LIdentTok { val = "false" } } & cur ->
    let expr = TmConst {
      val = CBool { val = false },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

lang CharParser = AstParserBase + CharAst
  sem parseExprROpen state =
  | { token = CharTok { val = val } } & cur ->
    let expr = TmConst {
      val = CChar { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

lang StringParser = AstParserBase + SeqAst + CharAst
  sem parseExprROpen state =
  | { token = StringTok { val = val } } & cur ->
    let expr = TmSeq {
      tms = map (lam ch. TmConst {
        val = CChar { val = ch },
        ty = ityunknown_ cur.info,
        info = cur.info
      }) val,
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (config ()) (OpAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

lang LetDeclParser = AstParserBase + LetDeclAst
  sem canStartExpr =
  | { token = LIdentTok { val = "let" } } -> false
  | { token = OperatorTok { val = "="} } -> false
  | { token = LIdentTok { val = "in"} } -> false

  sem parseExprROpen state =
  | { token = LIdentTok { val = "let" } } & toklet ->
    let cur = nextToken toklet.stream in

    match cur with { token = LIdentTok { val = ident } } & tokident then
      let cur = nextToken tokident.stream in

      let tyAnnot =
        match cur with { token = OperatorTok { val = ":" } } & tokcol then
          let cur = nextToken tokcol.stream in
          parseType cur
        else
          parseOk (ityunknown_ toklet.info, cur)
      in

      result.bind tyAnnot (lam tyAnnot.
        match tyAnnot with (tyAnnot, cur) in

        match cur with { token = OperatorTok { val = "=" } } & tokeq then
          let cur = nextToken tokeq.stream in

          result.bind (parseExpr cur) (lam body.
            match body with (body, cur) in

            match cur with { token = LIdentTok { val = "in" } } & tokin then
              let cur = nextToken tokin.stream in

              result.bind (parseExpr cur) (lam inexpr.
                match inexpr with (inexpr, cur) in

                let info = mergeInfo toklet.info tokin.info in
                let expr = TmDecl {
                  decl = DeclLet {
                    ident = nameNoSym ident,
                    tyAnnot = tyAnnot,
                    tyBody = ityunknown_ info,
                    body = body,
                    info = info
                  },
                  inexpr = inexpr,
                  ty = ityunknown_ info,
                  info = info
                } in
                let state = breakableAddAtom (config ()) (OpAtom expr) state in
                parseExprRClosed state (nextToken cur.stream)
              )

            else
              parseErr (cur.info, "Missing in expression")
          )

        else
          parseErr (cur.info, "Missing assignment")
      )
    else
      parseErr (cur.info, "Missing identifier")
end

lang UnexpectedTokenParser = AstParserBase
  sem parseExprROpen state =
  | cur ->
    let str = concat "Unexpexted token while parsing expr: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parseDecl =
  | cur ->
    let str = concat "Unexpexted token while parsing decl: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parseType =
  | cur ->
    let str = concat "Unexpexted token while parsing type: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parseKind =
  | cur ->
    let str = concat "Unexpexted token while parsing kind: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parsePat =
  | cur ->
    let str = concat "Unexpexted token while parsing pat: " (tokToStr cur.token) in
    parseErr (cur.info, str)
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
  + LetDeclParser
  + UnexpectedTokenParser
end

lang TestParser =
    AstParser
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
    eqString (jsonStr a) (jsonStr b) -- By comparing strings we also take info fieled into account.
  else
    false
  in

let compareWithoutInfo = lam str.
  let a = parse str in
  let b = parseBoot str in
  match (result.toOption a, result.toOption b) with (Some a, Some b) then
    eqExpr a b
  else
    false
  in

let printAst = lam expr.
  switch result.consume expr
  case (w, Left e) then
    printLn "Parse error:";
    iter (lam e.
      match e with (info, msg) in printLn (infoErrorString info msg)
    ) e
  case (w, Right expr) then
    printLn (jsonStr expr)
  end
in

-- let str = "let a: Int = 1 in a" in
-- printLn "";
-- printAst (parseBoot str);
-- printAst (parse str);

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

utest compareWithoutInfo "()" with true in
utest compareWithoutInfo "(())" with true in
utest compareWithoutInfo "addi () ()" with true in
utest compareWithoutInfo "(addi ()) ()" with true in

utest compare "let a = 1 in a" with true in
utest compare "let a = 1 in let b = 2 in addi a b" with true in
utest compare "let a: Int = 1 in a" with true in

()
