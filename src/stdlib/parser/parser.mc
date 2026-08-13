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

type ParseResult w a = Result w (String -> (Info, String)) a

let parseOk:  all w. all a. a              -> ParseResult w a = lam a. result.ok a
let parseErr: all w. all a. (Info, String) -> ParseResult w a = lam e. result.err (lam src. e)
let parseErrs: all w. all a. [String -> (Info, String)] -> ParseResult w a = lam errs.
  foldl1 result.withAnnotations (map result.err errs)

lang AstParserBase = Lexer + Ast + DeclAst
  syn BrkOpExpr lstyle rstyle =
  | OpExprAtom Expr
  | OpExprDecl Decl

  syn BrkOpType lstyle rstyle =
  | OpTypeAtom Type

  sem parseExpr: all w. NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseDecl: all w. NextTokenResult -> ParseResult w (Decl, NextTokenResult)
  sem parseType: all w. NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem parseKind: all w. NextTokenResult -> ParseResult w (Kind, NextTokenResult)
  sem parsePat:  all w. NextTokenResult -> ParseResult w (Pat,  NextTokenResult)

  sem parseExprRClosed:  all w. State BrkOpExpr RClosed -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseTypeRClosed:  all w. State BrkOpType RClosed -> NextTokenResult -> ParseResult w (Type, NextTokenResult)

  sem parseExprROpen:    all w. State BrkOpExpr ROpen   -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseTypeROpen:    all w. State BrkOpType ROpen   -> NextTokenResult -> ParseResult w (Type, NextTokenResult)

  sem finalizeParseExpr: all w. State BrkOpExpr RClosed -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem finalizeParseType: all w. State BrkOpType RClosed -> NextTokenResult -> ParseResult w (Type, NextTokenResult)

  sem canStartAppArgExpr: NextTokenResult -> Bool
  sem canStartAppArgType: NextTokenResult -> Bool

  sem constructPrefixExpr: (BrkOpExpr LClosed ROpen, Expr) -> Expr
  sem constructPrefixType: (BrkOpType LClosed ROpen, Type) -> Type

  sem constructInfixExpr: (BrkOpExpr LOpen ROpen, Expr, Expr) -> Expr
  sem constructInfixType: (BrkOpType LOpen ROpen, Type, Type) -> Type

  sem constructPostfixExpr: (BrkOpExpr LOpen RClosed, Expr) -> Expr
  sem constructPostfixType: (BrkOpType LOpen RClosed, Type) -> Type

  sem configExpr: () -> Config BrkOpExpr
  sem configType: () -> Config BrkOpType

  sem topAllowedExpr: TopAllowedFunc BrkOpExpr
  sem topAllowedType: TopAllowedFunc BrkOpType

  sem leftAllowedExpr: LeftAllowedFunc BrkOpExpr
  sem leftAllowedType: LeftAllowedFunc BrkOpType

  sem rightAllowedExpr: RightAllowedFunc BrkOpExpr
  sem rightAllowedType: RightAllowedFunc BrkOpType

  sem parenAllowedExpr: ParenAllowedFunc BrkOpExpr
  sem parenAllowedType: ParenAllowedFunc BrkOpType

  sem groupingsAllowedExpr: GroupingsAllowedFunc BrkOpExpr
  sem groupingsAllowedType: GroupingsAllowedFunc BrkOpType

  sem terminalInfosExpr: all lstyle. all rstyle. BrkOpExpr lstyle rstyle -> [Info]
  sem terminalInfosType: all lstyle. all rstyle. BrkOpType lstyle rstyle -> [Info]

  sem getInfoExpr: all lstyle. all rstyle. BrkOpExpr lstyle rstyle -> Info
  sem getInfoType: all lstyle. all rstyle. BrkOpType lstyle rstyle -> Info

  -- The main entry point
  sem parseExpr =
  | cur ->
    let state = breakableInitState () in
    parseExprROpen state cur

  sem parseType =
  | cur ->
    let state = breakableInitState () in
    parseTypeROpen state cur

  sem finalizeParseExpr state =
  | cur ->
    match breakableFinalizeParse (configExpr ()) state with Some sppf then
      let config: BreakableErrorHighlightConfig BrkOpExpr = {
        parenAllowed = #frozen"parenAllowedExpr",
        topAllowed = #frozen"topAllowedExpr",
        terminalInfos = #frozen"terminalInfosExpr",
        getInfo = #frozen"getInfoExpr",
        lpar = "(",
        rpar = ")"
      } in
      let errSpecs = breakableToErrorHighlightSpec config sppf in
      match errSpecs with [first] ++ _ then
        parseErrs (map breakableHighlightOne errSpecs)
      else
        let expr = breakableConstructSimple {
          constructAtom = lam op. match op with OpExprAtom expr in expr,
          constructInfix = lam op. lam lhs. lam rhs. constructInfixExpr (op, lhs, rhs),
          constructPrefix = lam op. lam rhs. constructPrefixExpr (op, rhs),
          constructPostfix = lam op. lam lhs. constructPostfixExpr (op, lhs)
        } sppf in
        parseOk (expr, cur)
    else
      parseErr (cur.info, "Breakable parse error")

  sem finalizeParseType state =
  | cur ->
    match breakableFinalizeParse (configType ()) state with Some sppf then
      let config: BreakableErrorHighlightConfig BrkOpType = {
        parenAllowed = #frozen"parenAllowedType",
        topAllowed = #frozen"topAllowedType",
        terminalInfos = #frozen"terminalInfosType",
        getInfo = #frozen"getInfoType",
        lpar = "(",
        rpar = ")"
      } in
      let errSpecs = breakableToErrorHighlightSpec config sppf in
      match errSpecs with [first] ++ _ then
        parseErrs (map breakableHighlightOne errSpecs)
      else
        let typ = breakableConstructSimple {
          constructAtom = lam op. match op with OpTypeAtom typ in typ,
          constructInfix = lam op. lam lhs. lam rhs. constructInfixType (op, lhs, rhs),
          constructPrefix = lam op. lam rhs. constructPrefixType (op, rhs),
          constructPostfix = lam op. lam lhs. constructPostfixType (op, lhs)
        } sppf in
        parseOk (typ, cur)
    else
      parseErr (cur.info, "Breakable parse error")

  sem canStartAppArgExpr =
  | _ -> false

  sem canStartAppArgType =
  | _ -> false

  sem constructPrefixExpr =
  | (OpExprDecl decl, inexpr) ->
    let info = infoDecl decl in
    TmDecl {
      decl = decl,
      inexpr = inexpr,
      ty = ityunknown_ info,
      info = info
    }

  sem configExpr =
  | _ ->
    {
      topAllowed = #frozen"topAllowedExpr",
      leftAllowed = #frozen"leftAllowedExpr",
      rightAllowed = #frozen"rightAllowedExpr",
      parenAllowed = #frozen"parenAllowedExpr",
      groupingsAllowed = #frozen"groupingsAllowedExpr"
    }

  sem configType =
  | _ ->
    {
      topAllowed = #frozen"topAllowedType",
      leftAllowed = #frozen"leftAllowedType",
      rightAllowed = #frozen"rightAllowedType",
      parenAllowed = #frozen"parenAllowedType",
      groupingsAllowed = #frozen"groupingsAllowedType"
    }

  sem topAllowedExpr =
  | _ -> true

  sem topAllowedType =
  | _ -> true

  sem leftAllowedExpr =
  | _ -> true

  sem leftAllowedType =
  | _ -> true

  sem rightAllowedExpr =
  | _ -> true

  sem rightAllowedType =
  | _ -> true

  sem parenAllowedExpr =
  | _ -> GEither ()

  sem parenAllowedType =
  | _ -> GEither ()

  sem groupingsAllowedExpr =
  | _ -> GEither ()

  sem groupingsAllowedType =
  | _ -> GEither ()

  sem terminalInfosExpr =
  | op -> [getInfoExpr op]

  sem terminalInfosType =
  | op -> [getInfoType op]

  sem getInfoExpr =
  | OpExprAtom expr -> infoTm expr
  | OpExprDecl decl -> infoDecl decl

  sem getInfoType =
  | OpTypeAtom typ -> infoTy typ
end

lang IntParser = AstParserBase + IntAst
  sem canStartAppArgExpr =
  | { token = IntTok { } } -> true

  sem canStartAppArgType =
  | { token = UIdentTok { val = "Int" } } -> true

  sem parseExprROpen state =
  | { token = IntTok { val = val } } & cur ->
    let expr = TmConst {
      val = CInt { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state =
  | { token = UIdentTok { val = "Int" } } & cur ->
    let typ = ityint_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)
end

lang FloatParser = AstParserBase + FloatAst
  sem canStartAppArgExpr =
  | { token = FloatTok { } } -> true

  sem canStartAppArgType =
  | { token = UIdentTok { val = "Float" } } -> true

  sem parseExprROpen state =
  | { token = FloatTok { val = val } } & cur ->
    let expr = TmConst {
      val = CFloat { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state =
  | { token = UIdentTok { val = "Float" } } & cur ->
    let typ = ityfloat_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)
end

lang NegParser = AstParserBase + IntAst + FloatAst
  sem canStartAppArgExpr =
  | { token = OperatorTok { val = "-" } } -> true

  sem parseExprROpen state =
  | { token = OperatorTok { val = "-" } } & tokneg ->
    let cur = nextToken tokneg.stream in

    switch cur
      case { token = IntTok { val = val } } then
        let info = mergeInfo tokneg.info cur.info in
        let expr = TmConst {
          val = CInt { val = negi val },
          ty = ityunknown_ info,
          info = info
        } in
        let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
        parseExprRClosed state (nextToken cur.stream)
      case { token = FloatTok { val = val } } then
        let info = mergeInfo tokneg.info cur.info in
        let expr = TmConst {
          val = CFloat { val = negf val },
          ty = ityunknown_ info,
          info = info
        } in
        let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
        parseExprRClosed state (nextToken cur.stream)
      case _ then
        parseErr (cur.info, "Expected a number")
    end
end

lang VarParser = AstParserBase + VarAst
  sem canStartAppArgExpr =
  | { token = LIdentTok { } } -> true
  | { token = HashStringTok { hash = "frozen" | "var" } } -> true

  sem parseExprROpen state =
  | { token = LIdentTok { val = val } } & cur ->
    let expr = TmVar {
      ident = nameNoSym val,
      ty = ityunknown_ cur.info,
      info = cur.info,
      frozen = false
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  | { token = HashStringTok { hash = "frozen", val = val } } & cur ->
    let expr = TmVar {
        ident = nameNoSym val,
        ty = ityunknown_ cur.info,
        info = cur.info,
        frozen = true
      } in
      let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
      parseExprRClosed state (nextToken cur.stream)

  | { token = HashStringTok { hash = "var", val = val } } & cur ->
    let expr = TmVar {
        ident = nameNoSym val,
        ty = ityunknown_ cur.info,
        info = cur.info,
        frozen = false
      } in
      let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
      parseExprRClosed state (nextToken cur.stream)
end

lang AppParser = AstParserBase + AppAst + AppTypeAst
  syn BrkOpExpr lstyle rstyle =
  | OpExprApp Info

  syn BrkOpType lstyle rstyle =
  | OpTypeApp Info

  sem getInfoExpr =
  | OpExprApp info ->
    info

  sem getInfoType =
  | OpTypeApp info ->
    info

  sem parseExprRClosed state =
  | cur ->
    -- check if the next token can be part of the current expression.
    match canStartAppArgExpr cur with true then
      match breakableAddInfix (configExpr ()) (OpExprApp cur.info) state with Some(state) then
        parseExprROpen state cur
      else
        parseErr (cur.info, "Breakable add infix error")
    else
      finalizeParseExpr state cur

  sem parseTypeRClosed state =
  | cur ->
    -- check if the next token can be part of the current type.
    match canStartAppArgType cur with true then
      match breakableAddInfix (configType ()) (OpTypeApp cur.info) state with Some(state) then
        parseTypeROpen state cur
      else
        parseErr (cur.info, "Breakable add infix error")
    else
      finalizeParseType state cur

  sem constructInfixExpr =
  | (OpExprApp info, lhs, rhs) ->
    let info = mergeInfo (infoTm lhs) (infoTm rhs) in
    TmApp {
      lhs = lhs,
      rhs = rhs,
      ty = ityunknown_ info,
      info = info
    }

  sem constructInfixType =
  | (OpTypeApp info, lhs, rhs) ->
    let info = mergeInfo (infoTy lhs) (infoTy rhs) in
    TyApp {
      lhs = lhs,
      rhs = rhs,
      info = info
    }
end

lang ParenParser = AstParserBase
  sem beginParseExprInParen: all w. State BrkOpExpr ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem beginParseTypeInParen: all w. State BrkOpType ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem endParseExprInParen:   all w. State BrkOpExpr ROpen -> NextTokenResult -> Expr -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem endParseTypeInParen:   all w. State BrkOpType ROpen -> NextTokenResult -> Type -> NextTokenResult -> ParseResult w (Type, NextTokenResult)

  sem canStartAppArgExpr =
  | { token = LParenTok {} } -> true

  sem canStartAppArgType =
  | { token = LParenTok {} } -> true

  sem beginParseExprInParen state open =
  | cur ->
    -- start of new expression in paren
    result.bind (parseExpr cur) (lam expr.
      match expr with (expr, cur) in
      endParseExprInParen state open expr cur
    )

  sem endParseExprInParen state open expr =
  | { token = RParenTok {} } & close ->
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken close.stream)

  | cur -> parseErr (cur.info, "Missing closing parenthesis")

  sem beginParseTypeInParen state open =
  | cur ->
    -- start of new type in paren
    result.bind (parseType cur) (lam typ.
      match typ with (typ, cur) in
      endParseTypeInParen state open typ cur
    )

  sem endParseTypeInParen state open typ =
  | { token = RParenTok {} } & close ->
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken close.stream)

  | cur -> parseErr (cur.info, "Missing closing parenthesis")

  sem parseExprROpen state =
  | { token = LParenTok {} } & open ->
    beginParseExprInParen state open (nextToken open.stream)

  sem parseTypeROpen state =
  | { token = LParenTok {} } & open ->
    beginParseTypeInParen state open (nextToken open.stream)

end

lang UnitParser = ParenParser + RecordAst + RecordTypeAst
  sem beginParseExprInParen state open =
  | { token = RParenTok {} } & close ->
    -- this is a unit
    let info = mergeInfo open.info close.info in
      let expr = TmRecord {
        bindings = mapEmpty cmpSID,
        ty = ityunknown_ info,
        info = info
      } in
      let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
      parseExprRClosed state (nextToken close.stream)

  sem beginParseTypeInParen state open =
  | { token = RParenTok {} } & close ->
    -- this is a unit
    let info = mergeInfo open.info close.info in
    let typ = TyRecord {
      fields = mapEmpty cmpSID,
      info = info
    } in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken close.stream)
end

lang TupleParser = ParenParser + RecordAst + RecordTypeAst
  sem endParseExprInParen state open expr =
  | { token = CommaTok {} } & comma ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parseExpr cur) (lam expr.
        match expr with (expr, cur) in
        let acc = snoc acc expr in
        switch cur
          case { token = RParenTok { } } then
            parseOk (cur, acc)
          case { token = CommaTok { } } then
            let cur = nextToken cur.stream in
            parseItems acc cur
          case _ then
            parseErr (cur.info, "Unexpected token in tuple")
        end
      )
    in

    let cur = nextToken comma.stream in
    let res = parseItems [expr] cur in

    result.bind res (lam res.
      match res with (close, exprs) in
      let info = mergeInfo open.info close.info in
      let expr = TmRecord {
        bindings = foldli (lam acc. lam i. lam expr.
          mapInsert (stringToSid (int2string i)) expr acc
        ) (mapEmpty cmpSID) exprs,
        ty = ityunknown_ info,
        info = info
      } in
      let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
      parseExprRClosed state (nextToken close.stream)
    )

  sem endParseTypeInParen state open typ =
  | { token = CommaTok {} } & comma ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parseType cur) (lam typ.
        match typ with (typ, cur) in
        let acc = snoc acc typ in
        switch cur
          case { token = RParenTok { } } then
            parseOk (cur, acc)
          case { token = CommaTok { } } then
            let cur = nextToken cur.stream in
            parseItems acc cur
          case _ then
            parseErr (cur.info, "Unexpected token in tuple")
        end
      )
    in

    let cur = nextToken comma.stream in
    let res = parseItems [typ] cur in

    result.bind res (lam res.
      match res with (close, typs) in
      let info = mergeInfo open.info close.info in
      let typ = TyRecord {
        fields = foldli (lam acc. lam i. lam typ.
          mapInsert (stringToSid (int2string i)) typ acc
        ) (mapEmpty cmpSID) typs,
        info = info
      } in
      let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
      parseTypeRClosed state (nextToken close.stream)
    )

end

lang BoolParser = AstParserBase + BoolAst
  sem canStartAppArgExpr =
  | { token = LIdentTok { val = "true" | "false" } } -> true

  sem canStartAppArgType =
  | { token = UIdentTok { val = "Bool" } } -> true

  sem parseExprROpen state =
  | { token = LIdentTok { val = "true" } } & cur ->
    let expr = TmConst {
      val = CBool { val = true },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
  | { token = LIdentTok { val = "false" } } & cur ->
    let expr = TmConst {
      val = CBool { val = false },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state =
  | { token = UIdentTok { val = "Bool" } } & cur ->
    let typ = itybool_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)
end

lang CharParser = AstParserBase + CharAst
  sem canStartAppArgExpr =
  | { token = CharTok { } } -> true

  sem canStartAppArgType =
  | { token = UIdentTok { val = "Char" } } -> true

  sem parseExprROpen state =
  | { token = CharTok { val = val } } & cur ->
    let expr = TmConst {
      val = CChar { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state =
  | { token = UIdentTok { val = "Char" } } & cur ->
    let typ = itychar_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)
end

lang StringParser = AstParserBase + SeqAst + CharAst
  sem canStartAppArgExpr =
  | { token = StringTok { } } -> true

  sem canStartAppArgType =
  | { token = UIdentTok { val = "String" } } -> true

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
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state =
  | { token = UIdentTok { val = "String" } } & cur ->
    let typ = itystr_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)
end

lang SeqParser = AstParserBase + SeqAst + SeqTypeAst
  sem canStartAppArgExpr =
  | { token = LBracketTok { } } -> true

  sem canStartAppArgType =
  | { token = LBracketTok { } } -> true

  sem parseExprROpen state =
  | { token = LBracketTok { } } & toklb ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parseExpr cur) (lam expr.
        match expr with (expr, cur) in
        let acc = snoc acc expr in
        switch cur
          case { token = RBracketTok { } } then
            parseOk (cur, acc)
          case { token = CommaTok { } } then
            let cur = nextToken cur.stream in
            parseItems acc cur
          case _ then
            parseErr (cur.info, "Unexpected token in sequence")
        end
      )
    in

    let cur = nextToken toklb.stream in
    let res = switch cur
      case { token = RBracketTok { } } then
        parseOk (cur, [])
      case _ then
        parseItems [] cur
    end in

    result.bind res (lam res.
      match res with (tokrb, tms) in
      let info = mergeInfo toklb.info tokrb.info in
      let expr = TmSeq {
        tms = tms,
        ty = ityunknown_ info,
        info = info
      } in
      let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
      parseExprRClosed state (nextToken tokrb.stream)
    )

  sem parseTypeROpen state =
  | { token = LBracketTok { } } & toklb ->
    let cur = nextToken toklb.stream in
    result.bind (parseType cur) (lam res.
      match res with (ty, cur) in
      match cur with { token = RBracketTok {} } & tokrb then
        let info = mergeInfo toklb.info tokrb.info in
        let typ = TySeq {
          ty = ty,
          info = info
        } in
        let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
        parseTypeRClosed state (nextToken cur.stream)
      else
        parseErr (cur.info, "Missing right bracket")
    )

end

lang BraceParser = AstParserBase
  sem beginParseExprInBrace: all w. State BrkOpExpr ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem beginParseTypeInBrace: all w. State BrkOpType ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  
  sem canStartAppArgExpr =
  | { token = LBraceTok {} } -> true

  sem canStartAppArgType =
  | { token = LBraceTok {} } -> true

  sem parseExprROpen state =
  | { token = LBraceTok {} } & open ->
    beginParseExprInBrace state open (nextToken open.stream)

  sem parseTypeROpen state =
  | { token = LBraceTok {} } & open ->
    beginParseTypeInBrace state open (nextToken open.stream)
end

lang RecordParser = BraceParser + RecordAst + RecordTypeAst
  sem canStartAppArgExpr =
    | { token = LIdentTok { val = "with" } } -> false

  sem beginParseExprInBrace state open =
  | { token = RBraceTok {} } & close ->
    -- this is a empty record
    let info = mergeInfo open.info close.info in
    let expr = TmRecord {
      bindings = mapEmpty cmpSID,
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken close.stream)
  
  | cur ->

    let isNormalRecord =
      match cur with { token = LIdentTok { } | HashStringTok { hash = "label" } } then
        match (nextToken cur.stream) with { token = OperatorTok { val = "=" } } then
          true
        else
          false
      else
        false
    in

    match isNormalRecord with true then
      -- Normal Record
      recursive let parseItems = lam acc. lam cur.
        match cur with { token = LIdentTok { val = field } | HashStringTok { hash = "label", val = field } } & tokfield then
          match nextToken tokfield.stream with { token = OperatorTok { val = "=" } } & tokeq then
            let cur = nextToken tokeq.stream in
            result.bind (parseExpr cur) (lam expr.
              match expr with (expr, cur) in
              let acc = mapInsert (stringToSid field) expr acc in
              switch cur
                case { token = RBraceTok { } } then
                  parseOk (cur, acc)
                case { token = CommaTok { } } then
                  let cur = nextToken cur.stream in
                  parseItems acc cur
                case _ then
                  parseErr (cur.info, "Unexpected token in sequence")
              end
            )
          else
            parseErr (cur.info, "Missing assignment")
        else
          parseErr (cur.info, "Unexpected token in record")
      in

      let res = parseItems (mapEmpty cmpSID) cur in

      result.bind res (lam res.
        match res with (close, bindings) in
        let info = mergeInfo open.info close.info in
        let expr = TmRecord {
          bindings = bindings,
          ty = ityunknown_ info,
          info = info
        } in
        let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
        parseExprRClosed state (nextToken close.stream)
      )
    
    -- Record Update
    else
      let res = parseExpr cur in
      result.bind res (lam res.
        match res with (rec, cur) in
        match cur with { token = LIdentTok { val = "with" } } & tokwith then
          let cur = nextToken tokwith.stream in
          recursive let parseItems = lam rec. lam cur.
            match cur with { token = LIdentTok { val = field } | HashStringTok { hash = "label", val = field } } & tokfield then
              match nextToken tokfield.stream with { token = OperatorTok { val = "=" } } & tokeq then
                let cur = nextToken tokeq.stream in
                result.bind (parseExpr cur) (lam expr.
                  match expr with (expr, cur) in
                  let info = mergeInfo (infoTm rec) (infoTm expr) in
                  let rec = TmRecordUpdate {
                    rec = rec,
                    key = stringToSid field,
                    value = expr,
                    ty = ityunknown_ info,
                    info = info
                  } in
                  switch cur
                    case { token = RBraceTok { } } then
                      parseOk (cur, rec)
                    case { token = CommaTok { } } then
                      let cur = nextToken cur.stream in
                      parseItems rec cur
                    case _ then
                      parseErr (cur.info, "Unexpected token in sequence")
                  end
                )
              else
                parseErr (cur.info, "Missing assignment")
            else
              parseErr (cur.info, "Unexpected token in record update")
          in

          let res = parseItems rec cur in
          
          result.bind res (lam res.
            match res with (close, expr) in
            let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
            parseExprRClosed state (nextToken close.stream)
          )
        else
          parseErr (cur.info, "Unexpected token in record")
      )

  sem beginParseTypeInBrace state open =
  | { token = RBraceTok {} } & close ->
    -- this is a empty record
    let info = mergeInfo open.info close.info in
    let typ = TyRecord {
      fields = mapEmpty cmpSID,
      info = info
    } in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken close.stream)
  
  | cur ->
    recursive let parseItems = lam acc. lam cur.
      match cur with { token = LIdentTok { val = field } } & tokfield then
        match nextToken tokfield.stream with { token = OperatorTok { val = ":" } } & tokcol then
          let cur = nextToken tokcol.stream in
          result.bind (parseType cur) (lam typ.
            match typ with (typ, cur) in
            let acc = mapInsert (stringToSid field) typ acc in
            switch cur
              case { token = RBraceTok { } } then
                parseOk (cur, acc)
              case { token = CommaTok { } } then
                let cur = nextToken cur.stream in
                parseItems acc cur
              case _ then
                parseErr (cur.info, "Unexpected token in sequence")
            end
          )
        else
          parseErr (cur.info, "Missing type assignment")
      else
        parseErr (cur.info, "Unexpected token in record")
    in
    
    let res = parseItems (mapEmpty cmpSID) cur in

    result.bind res (lam res.
      match res with (close, fields) in
      let info = mergeInfo open.info close.info in
      let typ = TyRecord {
        fields = fields,
        info = info
      } in
      let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
      parseTypeRClosed state (nextToken close.stream)
    )
end

lang LetDeclParser = AstParserBase + LetDeclAst
  sem canStartAppArgExpr =
  | { token = LIdentTok { val = "let" | "in" } } -> false

  sem parseExprROpen state =
  | { token = LIdentTok { val = "let" } } & toklet ->
    result.bind (parseDecl toklet) (lam decl.
      match decl with (decl, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in

      match cur with { token = LIdentTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing in expression")
    )

  sem parseDecl =
  | { token = LIdentTok { val = "let" } } & toklet ->
    let cur = nextToken toklet.stream in

    match cur with { token = LIdentTok { val = ident } } & tokident then
      let cur = nextToken tokident.stream in

      let tyAnnot =
        match cur with { token = OperatorTok { val = ":" } } & tokcol then
          let cur = nextToken tokcol.stream in
          parseType cur
        else
          parseOk (ityunknown_ tokident.info, cur)
      in

      result.bind tyAnnot (lam tyAnnot.
        match tyAnnot with (tyAnnot, cur) in

        match cur with { token = OperatorTok { val = "=" } } & tokeq then
          let cur = nextToken tokeq.stream in

          result.bind (parseExpr cur) (lam body.
            match body with (body, cur) in

            let info = mergeInfo toklet.info (infoTm body) in
            let decl = DeclLet {
              ident = nameNoSym ident,
              tyAnnot = tyAnnot,
              tyBody = ityunknown_ info,
              body = body,
              info = info
            } in
            parseOk (decl, cur)
          )
        else
          parseErr (cur.info, "Missing assignment")
      )
    else
      parseErr (cur.info, "Missing identifier")
end

lang RecLetsDeclParser = AstParserBase + RecLetsDeclAst
  sem canStartAppArgExpr =
  | { token = LIdentTok { val = "recursive" | "let" | "in" } } -> false

  sem parseExprROpen state =
  | { token = LIdentTok { val = "recursive" } } & rokrec ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parseDecl cur) (lam decl.
        match decl with (DeclLet decl, cur) in
        let acc = snoc acc decl in
        switch cur
          case { token = LIdentTok { val = "in" } } & tokin then
            let cur = nextToken tokin.stream in
            parseOk (tokin, cur, acc)
          case { token = LIdentTok { val = "let" } } then
            parseItems acc cur
          case _ then
            parseErr (cur.info, "Unexpected token in recursive declaration")
        end
      )
    in

    let cur = nextToken rokrec.stream in
    let res = parseItems [] cur in

    result.bind res (lam res.
      match res with (tokin, cur, bindings) in
      let info = mergeInfo rokrec.info tokin.info in
      let decl = DeclRecLets {
        bindings = bindings,
        info = info
      } in
      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in
      parseExprROpen state (nextToken tokin.stream)
    )
end

lang LamParser = AstParserBase + LamAst + FunTypeAst
  syn BrkOpExpr lstyle rstyle =
  | OpExprLam (Info, String, Type, Type)

  syn BrkOpType lstyle rstyle =
  | OpTypeArrow Info

  sem getInfoExpr =
  | OpExprLam (info, _, _, _) -> info

  sem getInfoType =
  | OpTypeArrow info -> info

  sem canStartAppArgExpr =
  | { token = LIdentTok { val = "lam" } } -> false

  sem parseExprROpen state =
  | { token = LIdentTok { val = "lam" } } & toklam ->
    let cur = nextToken toklam.stream in

    match match cur with { token = LIdentTok { val = ident } } & tokident then
      let cur = nextToken tokident.stream in
      let tyAnnot =
        match cur with { token = OperatorTok { val = ":" } } & tokcol then
          let cur = nextToken tokcol.stream in
          parseType cur
        else
          parseOk (tyunknown_, cur)
      in
      (ident, ityunknown_ tokident.info, tyAnnot)
    else
      ("", tyunknown_, parseOk (tyunknown_, cur))
    with (ident, tyParam, tyAnnot) in

    result.bind tyAnnot (lam res.
      match res with (tyAnnot, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprLam (toklam.info, ident, tyParam, tyAnnot)) state in

      match cur with { token = OperatorTok { val = "." } } & tokdot then
        let cur = nextToken tokdot.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing period")
    )

  sem parseTypeRClosed state =
  | { token = OperatorTok { val = "->" } } & cur ->
    match breakableAddInfix (configType ()) (OpTypeArrow cur.info) state with Some(state) then
      let cur = nextToken cur.stream in
      parseTypeROpen state cur
    else
      parseErr (cur.info, "Breakable add infix error")

  sem constructPrefixExpr =
  | (OpExprLam (beginInfo, ident, tyParam, tyAnnot), body) ->
    let info = mergeInfo beginInfo (infoTm body) in
    TmLam {
      ident = nameNoSym ident,
      tyAnnot = tyAnnot,
      tyParam = tyParam,
      body = body,
      ty = ityunknown_ info,
      info = info
    }

  sem constructInfixType =
  | (OpTypeArrow info, from, to) ->
    let info = mergeInfo (infoTy from) (infoTy to) in
    TyArrow {
      from = from,
      to = to,
      info = info
    }
end

lang NeverParser = AstParserBase + NeverAst
  sem parseExprROpen state =
  | { token = LIdentTok { val = "never" } } & cur ->
    let expr = TmNever {
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

-- TODO: Better solution
lang PrecedenceParser = AppParser + LamParser + LetDeclParser
  sem groupingsAllowedExpr =
  | (OpExprApp _, OpExprApp _) -> GLeft ()
  | (OpExprDecl _, OpExprApp _) -> GRight ()
  | (OpExprLam _, OpExprApp _) -> GRight ()

  sem groupingsAllowedType =
  | (OpTypeApp _, OpTypeApp _)  -> GLeft ()
  | (OpTypeArrow _, OpTypeArrow _) -> GLeft ()
  | (OpTypeApp _, OpTypeArrow _) -> GLeft ()
  | (OpTypeArrow _, OpTypeApp _) -> GRight ()
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

  sem parseTypeROpen state =
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
  + SeqParser
  + NegParser
  + VarParser
  + AppParser
  + ParenParser
  + UnitParser
  + TupleParser
  + RecordParser
  + LetDeclParser
  + RecLetsDeclParser
  + LamParser
  + NeverParser
  + PrecedenceParser
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

let printAstBoot = lam str.
  switch result.consume (parseBoot str)
  case (w, Left e) then
    printLn "Parse error:";
    iter (lam e.
      match e with (info, msg) in printLn (infoErrorString info msg)
    ) e
  case (w, Right expr) then
    printLn (jsonStr expr)
  end
in

let printAst = lam str.
  switch result.consume (parse str)
  case (w, Left e) then
    printLn "Parse error:";
    iter (lam e.
      match e str with (info, msg) in printLn (infoErrorString info msg)
    ) e
  case (w, Right expr) then
    printLn (jsonStr expr)
  end
in

-- let str = "{#label\"a\" = 1, b = 2}" in
-- printLn "\nBoot:";
-- printAstBoot str;
-- printLn "Native:";
-- printAst str;

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

utest compare "a" with true in
utest compare "#frozen\"a\"" with true in
utest compare "#var\"a\"" with true in

utest compareWithoutInfo "()" with true in
utest compareWithoutInfo "(())" with true in
utest compareWithoutInfo "addi () ()" with true in
utest compareWithoutInfo "(addi ()) ()" with true in

utest compareWithoutInfo "let a = 1 in a" with true in
utest compareWithoutInfo "let a = 1 in let b = 2 in addi a b" with true in

utest compareWithoutInfo "let a: Int = 1 in a" with true in
utest compareWithoutInfo "let a: Float = 1.0 in a" with true in
utest compareWithoutInfo "let a: Bool = true in a" with true in
utest compareWithoutInfo "let a: Char = 'a' in a" with true in
utest compareWithoutInfo "let a: String = \"test\" in a" with true in

utest compareWithoutInfo "let a: Int Int = 1 1 in a" with true in

utest compareWithoutInfo "let a: Int -> Int = addi 1 in a" with true in
utest compareWithoutInfo "let a: Int Int -> Int = addi in a" with true in

utest compare "[]" with true in
utest compare "[1]" with true in
utest compare "[1, 2]" with true in
utest compare "[1, [2, 3]]" with true in
utest compare "[[1, 2], 3]" with true in
utest compare "cons 0 [1, 2]" with true in

utest compareWithoutInfo "let a: [Int] = () in a" with true in
utest compareWithoutInfo "let a: [[Int]] = () in a" with true in

utest compareWithoutInfo "lam. ()" with true in
utest compareWithoutInfo "lam a. a" with true in
utest compareWithoutInfo "lam a: Int. a" with true in
utest compareWithoutInfo "lam. lam. ()" with true in
utest compareWithoutInfo "lam a. lam b. addi a b" with true in

utest compare "(1, 2)" with true in
utest compare "(1, (2, 3))" with true in
utest compare "((1, 2), 3)" with true in

utest compareWithoutInfo "let a: ((Int, Bool), String) = () in a" with true in

utest compare "{a = 1, b = 2}" with true in
utest compare "{a = 1, bc = { b = 2, c = 3 } }" with true in
utest compareWithoutInfo "{#label\"a\" = 1, b = 2}" with true in

utest compareWithoutInfo "let a: { a: Int, b: Bool } = () in a" with true in
utest compareWithoutInfo "let a: { a: Int, bc: { b: Bool, c: Char } } = () in a" with true in

utest compareWithoutInfo "{negi 1 with b = 2}" with true in
utest compareWithoutInfo "{negi 1 with b = 2, c = 3}" with true in
utest compareWithoutInfo "{{negi 1 with b = 2} with c = 3}" with true in

utest compare "never" with true in

utest compareWithoutInfo "recursive let a = lam b. 1 in c" with true in

utest compareWithoutInfo "recursive let a = lam b. 1 let c = lam d. 2 in e" with true in

()
