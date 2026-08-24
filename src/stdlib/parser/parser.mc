/-

This will be a parser for MCore.
It is work in progress.

The parser is designed to be as extensible as possible.
It is built on top of the breakable library.

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

  syn BrkOpPat lstyle rstyle =
  | OpPatAtom Pat

  sem parseExpr: all w. NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseDecl: all w. NextTokenResult -> ParseResult w (Decl, NextTokenResult)
  sem parseType: all w. NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem parseKind: all w. NextTokenResult -> ParseResult w (Kind, NextTokenResult)
  sem parsePat:  all w. NextTokenResult -> ParseResult w (Pat,  NextTokenResult)

  sem parseExprRClosed:  all w. State BrkOpExpr RClosed -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseTypeRClosed:  all w. State BrkOpType RClosed -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem parsePatRClosed:   all w. State BrkOpPat  RClosed -> NextTokenResult -> ParseResult w (Pat,  NextTokenResult)

  sem parseExprROpen:    all w. State BrkOpExpr ROpen   -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem parseTypeROpen:    all w. State BrkOpType ROpen   -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem parsePatROpen:     all w. State BrkOpPat  ROpen   -> NextTokenResult -> ParseResult w (Pat,  NextTokenResult)

  sem finalizeParseExpr: all w. State BrkOpExpr RClosed -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem finalizeParseType: all w. State BrkOpType RClosed -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem finalizeParsePat:  all w. State BrkOpPat  RClosed -> NextTokenResult -> ParseResult w (Pat,  NextTokenResult)

  sem canStartAppArgExpr: NextTokenResult -> Bool
  sem canStartAppArgType: NextTokenResult -> Bool

  sem constructPrefixExpr: all w. (BrkOpExpr LClosed ROpen, Expr) -> ParseResult w Expr
  sem constructPrefixType: all w. (BrkOpType LClosed ROpen, Type) -> ParseResult w Type
  sem constructPrefixPat:  all w. (BrkOpPat  LClosed ROpen, Pat)  -> ParseResult w Pat

  sem constructInfixExpr: all w. (BrkOpExpr LOpen ROpen, Expr, Expr) -> ParseResult w Expr
  sem constructInfixType: all w. (BrkOpType LOpen ROpen, Type, Type) -> ParseResult w Type
  sem constructInfixPat:  all w. (BrkOpPat  LOpen ROpen, Pat,  Pat)  -> ParseResult w Pat

  sem constructPostfixExpr: all w. (BrkOpExpr LOpen RClosed, Expr) -> ParseResult w Expr
  sem constructPostfixType: all w. (BrkOpType LOpen RClosed, Type) -> ParseResult w Type
  sem constructPostfixPat:  all w. (BrkOpPat  LOpen RClosed, Pat)  -> ParseResult w Pat

  sem configExpr: () -> Config BrkOpExpr
  sem configType: () -> Config BrkOpType
  sem configPat:  () -> Config BrkOpPat

  sem topAllowedExpr: TopAllowedFunc BrkOpExpr
  sem topAllowedType: TopAllowedFunc BrkOpType
  sem topAllowedPat:  TopAllowedFunc BrkOpPat

  sem leftAllowedExpr: LeftAllowedFunc BrkOpExpr
  sem leftAllowedType: LeftAllowedFunc BrkOpType
  sem leftAllowedPat:  LeftAllowedFunc BrkOpPat

  sem rightAllowedExpr: RightAllowedFunc BrkOpExpr
  sem rightAllowedType: RightAllowedFunc BrkOpType
  sem rightAllowedPat:  RightAllowedFunc BrkOpPat

  sem parenAllowedExpr: ParenAllowedFunc BrkOpExpr
  sem parenAllowedType: ParenAllowedFunc BrkOpType
  sem parenAllowedPat:  ParenAllowedFunc BrkOpPat

  sem groupingsAllowedExpr: GroupingsAllowedFunc BrkOpExpr
  sem groupingsAllowedType: GroupingsAllowedFunc BrkOpType
  sem groupingsAllowedPat:  GroupingsAllowedFunc BrkOpPat

  sem terminalInfosExpr: all lstyle. all rstyle. BrkOpExpr lstyle rstyle -> [Info]
  sem terminalInfosType: all lstyle. all rstyle. BrkOpType lstyle rstyle -> [Info]
  sem terminalInfosPat:  all lstyle. all rstyle. BrkOpPat  lstyle rstyle -> [Info]

  sem getInfoExpr: all lstyle. all rstyle. BrkOpExpr lstyle rstyle -> Info
  sem getInfoType: all lstyle. all rstyle. BrkOpType lstyle rstyle -> Info
  sem getInfoPat:  all lstyle. all rstyle. BrkOpPat lstyle rstyle -> Info

  -- The main entry point
  sem parseExpr =
  | cur ->
    let state = breakableInitState () in
    parseExprROpen state cur

  sem parseType =
  | cur ->
    let state = breakableInitState () in
    parseTypeROpen state cur

  sem parsePat =
  | cur ->
    let state = breakableInitState () in
    parsePatROpen state cur

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
        let exprRes = breakableConstructSimple {
          constructAtom = lam op. match op with OpExprAtom expr in parseOk expr,
          constructInfix = lam op. lam lhsRes. lam rhsRes.
            result.bind lhsRes (lam lhs.
              result.bind rhsRes (lam rhs.
                constructInfixExpr (op, lhs, rhs)
              )
            ),
          constructPrefix = lam op. lam rhsRes.
            result.bind rhsRes (lam rhs.
              constructPrefixExpr (op, rhs)
            ),
          constructPostfix = lam op. lam lhsRes.
            result.bind lhsRes (lam lhs.
              constructPostfixExpr (op, lhs)
            )
        } sppf in
        result.map (lam expr. (expr, cur)) exprRes
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
        let typRes = breakableConstructSimple {
          constructAtom = lam op. match op with OpTypeAtom typ in parseOk typ,
          constructInfix = lam op. lam lhsRes. lam rhsRes.
            result.bind lhsRes (lam lhs.
              result.bind rhsRes (lam rhs.
                constructInfixType (op, lhs, rhs)
              )
            ),
          constructPrefix = lam op. lam rhsRes.
            result.bind rhsRes (lam rhs.
              constructPrefixType (op, rhs)
            ),
          constructPostfix = lam op. lam lhsRes.
            result.bind lhsRes (lam lhs.
              constructPostfixType (op, lhs)
            )
        } sppf in
        result.map (lam typ. (typ, cur)) typRes
    else
      parseErr (cur.info, "Breakable parse error")

  sem finalizeParsePat state =
  | cur ->
    match breakableFinalizeParse (configPat ()) state with Some sppf then
      let config: BreakableErrorHighlightConfig BrkOpPat = {
        parenAllowed = #frozen"parenAllowedPat",
        topAllowed = #frozen"topAllowedPat",
        terminalInfos = #frozen"terminalInfosPat",
        getInfo = #frozen"getInfoPat",
        lpar = "(",
        rpar = ")"
      } in
      let errSpecs = breakableToErrorHighlightSpec config sppf in
      match errSpecs with [first] ++ _ then
        parseErrs (map breakableHighlightOne errSpecs)
      else
        let patRes = breakableConstructSimple {
          constructAtom = lam op. match op with OpPatAtom pat in parseOk pat,
          constructInfix = lam op. lam lhsRes. lam rhsRes.
            result.bind lhsRes (lam lhs.
              result.bind rhsRes (lam rhs.
                constructInfixPat (op, lhs, rhs)
              )
            ),
          constructPrefix = lam op. lam rhsRes.
            result.bind rhsRes (lam rhs.
              constructPrefixPat (op, rhs)
            ),
          constructPostfix = lam op. lam lhsRes.
            result.bind lhsRes (lam lhs.
              constructPostfixPat (op, lhs)
            )
        } sppf in
        result.map (lam pat. (pat, cur)) patRes
    else
      parseErr (cur.info, "Breakable parse error")

  sem canStartAppArgExpr =
  | _ -> false

  sem canStartAppArgType =
  | _ -> false

  sem constructPrefixExpr =
  | (OpExprDecl decl, inexpr) ->
    let info = infoDecl decl in
    parseOk (TmDecl {
      decl = decl,
      inexpr = inexpr,
      ty = ityunknown_ info,
      info = info
    })

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

  sem configPat =
  | _ ->
    {
      topAllowed = #frozen"topAllowedPat",
      leftAllowed = #frozen"leftAllowedPat",
      rightAllowed = #frozen"rightAllowedPat",
      parenAllowed = #frozen"parenAllowedPat",
      groupingsAllowed = #frozen"groupingsAllowedPat"
    }

  sem topAllowedExpr =
  | _ -> true

  sem topAllowedType =
  | _ -> true

  sem topAllowedPat =
  | _ -> true

  sem leftAllowedExpr =
  | _ -> true

  sem leftAllowedType =
  | _ -> true

  sem leftAllowedPat =
  | _ -> true

  sem rightAllowedExpr =
  | _ -> true

  sem rightAllowedType =
  | _ -> true

  sem rightAllowedPat =
  | _ -> true

  sem parenAllowedExpr =
  | _ -> GEither ()

  sem parenAllowedType =
  | _ -> GEither ()

  sem parenAllowedPat =
  | _ -> GEither ()

  sem groupingsAllowedExpr =
  | _ -> GEither ()

  sem groupingsAllowedType =
  | _ -> GEither ()

  sem groupingsAllowedPat =
  | _ -> GEither ()

  sem terminalInfosExpr =
  | op -> [getInfoExpr op]

  sem terminalInfosType =
  | op -> [getInfoType op]

  sem terminalInfosPat =
  | op -> [getInfoPat op]

  sem getInfoExpr =
  | OpExprAtom expr -> infoTm expr
  | OpExprDecl decl -> infoDecl decl

  sem getInfoType =
  | OpTypeAtom typ -> infoTy typ

  sem getInfoPat =
  | OpPatAtom pat -> infoPat pat
end

lang WithKeyword = Lexer
  sem identIsKeyword =
  | "with" -> true
end

lang LetKeyword = Lexer
  sem identIsKeyword =
  | "let" -> true
end

lang InKeyword = Lexer
  sem identIsKeyword =
  | "in" -> true
end

lang ThenKeyword = Lexer
  sem identIsKeyword =
  | "then" -> true
end

lang ElseKeyword = Lexer
  sem identIsKeyword =
  | "else" -> true
end

lang TrueKeyword = Lexer
  sem identIsKeyword =
  | "true" -> true
end

lang FalseKeyword = Lexer
  sem identIsKeyword =
  | "false" -> true
end

lang RecursiveKeyword = Lexer
  sem identIsKeyword =
  | "recursive" -> true
end

lang LamKeyword = Lexer
  sem identIsKeyword =
  | "lam" -> true
end

lang MatchKeyword = Lexer
  sem identIsKeyword =
  | "match" -> true
end

lang NeverKeyword = Lexer
  sem identIsKeyword =
  | "never" -> true
end

lang IntParser = AstParserBase + IntAst + IntPat
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

  sem parsePatROpen state =
  | { token = IntTok { val = val } } & cur ->
    let pat = PatInt {
      val = val,
      ty = tyint_,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
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

lang NegParser = AstParserBase + IntAst + FloatAst + IntPat
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

  sem parsePatROpen state =
  | { token = OperatorTok { val = "-" } } & tokneg ->
    let cur = nextToken tokneg.stream in

    match cur with { token = IntTok { val = val } } then
      let info = mergeInfo tokneg.info cur.info in
      let pat = PatInt {
        val = negi val,
        ty = tyint_,
        info = info
      } in
      let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
      parsePatRClosed state (nextToken cur.stream)
    else
      parseErr (cur.info, "Expected an integer")
end

lang VarParser = AstParserBase + VarAst + VarTypeAst + NamedPat
  sem canStartAppArgExpr =
  | { token = LIdentTok { } } -> true
  | { token = HashStringTok { hash = "frozen" | "var" } } -> true

  sem canStartAppArgType =
  | { token = LIdentTok { } } -> true
  | { token = HashStringTok { hash = "var" } } -> true

  sem parseExprROpen state =
  | { token = LIdentTok { val = val } | HashStringTok { hash = "var", val = val } } & cur ->
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

  sem parseTypeROpen state =
  | { token = LIdentTok { val = val } | HashStringTok { hash = "var", val = val } } & cur ->
    let typ = TyVar {
      ident = nameNoSym val,
      info = cur.info
    } in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)

  sem parsePatROpen state =
  | { token = LIdentTok { val = "_" } } & cur ->
    let pat = PatNamed {
      ident = PWildcard (),
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)

  | { token = LIdentTok { val = val } | HashStringTok { hash = "var", val = val } } & cur ->
    let pat = PatNamed {
      ident = PName (nameNoSym val),
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
    
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

  sem parsePatRClosed state =
  | cur ->
    -- patterns can not be applied
    finalizeParsePat state cur

  sem constructInfixExpr =
  | (OpExprApp info, lhs, rhs) ->
    let info = mergeInfo (infoTm lhs) (infoTm rhs) in
    parseOk (TmApp {
      lhs = lhs,
      rhs = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem constructInfixType =
  | (OpTypeApp info, lhs, rhs) ->
    let info = mergeInfo (infoTy lhs) (infoTy rhs) in
    parseOk (TyApp {
      lhs = lhs,
      rhs = rhs,
      info = info
    })

  sem groupingsAllowedExpr =
  | (OpExprApp _, OpExprApp _) -> GLeft ()

  sem groupingsAllowedType =
  | (OpTypeApp _, OpTypeApp _)  -> GLeft ()
end

lang DataParser = AstParserBase + DataAst + ConTypeAst + AppTypeAst + DataPat
  syn BrkOpExpr lstyle rstyle =
  | OpExprConApp (Info, Name)

  syn BrkOpType lstyle rstyle =
  | OpTypeConApp (Info, Name)

  syn BrkOpPat lstyle rstyle =
  | OpPatConApp (Info, Name)

  sem getInfoExpr =
  | OpExprConApp (info, _) -> info

  sem getInfoType =
  | OpTypeConApp (info, _) -> info

  sem getInfoPat =
  | OpPatConApp (info, _) -> info

  sem parseExprROpen state =
  | { token = UIdentTok { val = val } | HashStringTok { hash = "con", val = val } } & tokident ->
    let cur = nextToken tokident.stream in
    let ident = nameNoSym val in
    let state = breakableAddPrefix (configExpr ()) (OpExprConApp (tokident.info, ident)) state in
    parseExprROpen state cur

  sem parseTypeROpen state =
  | { token = UIdentTok { val = val } | HashStringTok { hash = "con", val = val } } & tokident ->
    let cur = nextToken tokident.stream in
    let ident = nameNoSym val in
    let state = breakableAddPrefix (configType ()) (OpTypeConApp (tokident.info, ident)) state in
    parseTypeROpen state cur
  
  sem parsePatROpen state =
  | { token = UIdentTok { val = val } | HashStringTok { hash = "con", val = val } } & tokident ->
    let cur = nextToken tokident.stream in
    let ident = nameNoSym val in
    let state = breakableAddPrefix (configPat ()) (OpPatConApp (tokident.info, ident)) state in
    parsePatROpen state cur

  sem constructPrefixExpr =
  | (OpExprConApp (info, ident), rhs) ->
    let info = mergeInfo info (infoTm rhs) in
    parseOk (TmConApp {
      ident = ident,
      body = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem constructPrefixType =
  | (OpTypeConApp (info, ident), rhs) ->
    let lhs = TyCon {
      ident = ident,
      data = ityunknown_ info,
      info = info
    } in
    let info = mergeInfo info (infoTy rhs) in
    parseOk (TyApp {
      lhs = lhs,
      rhs = rhs,
      info = info
    })

  sem constructPrefixPat =
  | (OpPatConApp (info, ident), rhs) ->
    let info = mergeInfo info (infoPat rhs) in
    parseOk (PatCon {
      ident = ident,
      subpat = rhs,
      ty = ityunknown_ info,
      info = info
    })
end

lang ParenParser = AstParserBase
  sem beginParseExprInParen: all w. State BrkOpExpr ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem beginParseTypeInParen: all w. State BrkOpType ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem beginParsePatInParen:  all w. State BrkOpPat  ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Pat,  NextTokenResult)
  sem endParseExprInParen:   all w. State BrkOpExpr ROpen -> NextTokenResult -> Expr -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem endParseTypeInParen:   all w. State BrkOpType ROpen -> NextTokenResult -> Type -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem endParsePatInParen:    all w. State BrkOpPat  ROpen -> NextTokenResult -> Pat  -> NextTokenResult -> ParseResult w (Pat,  NextTokenResult)

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

  sem beginParsePatInParen state open =
  | cur ->
    -- start of new pat in paren
    result.bind (parsePat cur) (lam pat.
      match pat with (pat, cur) in
      endParsePatInParen state open pat cur
    )

  sem endParsePatInParen state open pat =
  | { token = RParenTok {} } & close ->
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken close.stream)

  | cur -> parseErr (cur.info, "Missing closing parenthesis")

  sem parseExprROpen state =
  | { token = LParenTok {} } & open ->
    beginParseExprInParen state open (nextToken open.stream)

  sem parseTypeROpen state =
  | { token = LParenTok {} } & open ->
    beginParseTypeInParen state open (nextToken open.stream)

  sem parsePatROpen state =
  | { token = LParenTok {} } & open ->
    beginParsePatInParen state open (nextToken open.stream)

end

lang UnitParser = ParenParser + RecordAst + RecordTypeAst + RecordPat
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

  sem beginParsePatInParen state open =
  | { token = RParenTok {} } & close ->
    -- this is a unit
    let info = mergeInfo open.info close.info in
    let pat = PatRecord {
      bindings = mapEmpty cmpSID,
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken close.stream)
end

lang TupleParser = ParenParser + RecordAst + RecordTypeAst + RecordPat
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
    let res = match cur with { token = RParenTok {} } then
      parseOk (cur, [expr])
    else
      parseItems [expr] cur
    in

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
    let res = match cur with { token = RParenTok {} } then
      parseOk (cur, [typ])
    else
      parseItems [typ] cur
    in

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

  sem endParsePatInParen state open pat =
  | { token = CommaTok {} } & comma ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parsePat cur) (lam pat.
        match pat with (pat, cur) in
        let acc = snoc acc pat in
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
    let res = match cur with { token = RParenTok {} } then
      parseOk (cur, [pat])
    else
      parseItems [pat] cur
    in

    result.bind res (lam res.
      match res with (close, pats) in
      let info = mergeInfo open.info close.info in
      let pat = PatRecord {
        bindings = foldli (lam acc. lam i. lam pat.
          mapInsert (stringToSid (int2string i)) pat acc
        ) (mapEmpty cmpSID) pats,
        ty = ityunknown_ info,
        info = info
      } in
      let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
      parsePatRClosed state (nextToken close.stream)
    )

end

lang BoolParser = AstParserBase + BoolAst + BoolPat + TrueKeyword + FalseKeyword
  sem canStartAppArgExpr =
  | { token = KeywordTok { val = "true" | "false" } } -> true

  sem canStartAppArgType =
  | { token = UIdentTok { val = "Bool" } } -> true

  sem parseExprROpen state =
  | { token = KeywordTok { val = "true" } } & cur ->
    let expr = TmConst {
      val = CBool { val = true },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
  | { token = KeywordTok { val = "false" } } & cur ->
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

  sem parsePatROpen state =
  | { token = KeywordTok { val = "true" } } & cur ->
    let pat = PatBool {
      val = true,
      ty = tybool_,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
  | { token = KeywordTok { val = "false" } } & cur ->
    let pat = PatBool {
      val = false,
      ty = tybool_,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
end

lang CharParser = AstParserBase + CharAst + CharPat
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

  sem parsePatROpen state =
  | { token = CharTok { val = val } } & cur ->
    let pat = PatChar {
      val = val,
      ty = tychar_,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
end

lang StringParser = AstParserBase + SeqAst + CharAst + SeqTotPat + CharPat
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

  sem parsePatROpen state =
  | { token = StringTok { val = val } } & cur ->
    let pat = PatSeqTot {
      pats = map (lam ch. PatChar {
        val = ch,
        ty = tychar_,
        info = cur.info
      }) val,
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
end

lang SeqParser = AstParserBase + SeqAst + SeqTypeAst + SeqTotPat + SeqEdgePat + NamedPat
  syn BrkOpPat lstyle rstyle =
  | OpPatSeqEdge Info

  sem getInfoPat =
  | OpPatSeqEdge info -> info

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

  sem parsePatROpen state =
  | { token = LBracketTok { } } & toklb ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parsePat cur) (lam pat.
        match pat with (pat, cur) in
        let acc = snoc acc pat in
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
      match res with (tokrb, pats) in
      let info = mergeInfo toklb.info tokrb.info in
      let pat = PatSeqTot {
        pats = pats,
        ty = ityunknown_ info,
        info = info
      } in
      let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
      parsePatRClosed state (nextToken tokrb.stream)
    )

  sem parsePatRClosed state =
  | { token = OperatorTok { val = "++" } } & tokpp ->
    match breakableAddInfix (configPat ()) (OpPatSeqEdge tokpp.info) state with Some(state) then
      let cur = nextToken tokpp.stream in
      parsePatROpen state cur
    else
      parseErr (tokpp.info, "Breakable add infix error")

  sem constructInfixPat =
  | (OpPatSeqEdge info, lhs, rhs) ->
    let info = mergeInfo (infoPat lhs) (infoPat rhs) in

    switch (lhs, rhs)
      -- [1,2,3] ++ rest
      case (PatSeqTot lhs, PatNamed rhs) then
        parseOk (PatSeqEdge {
          prefix = lhs.pats,
          middle = rhs.ident,
          postfix = [],
          ty = ityunknown_ info,
          info = info
        })
      -- rest ++ [7,8,9]
      case (PatNamed lhs, PatSeqTot rhs) then
        parseOk (PatSeqEdge {
          prefix = [],
          middle = lhs.ident,
          postfix = rhs.pats,
          ty = ityunknown_ info,
          info = info
        })
      -- ([1,2,3] ++ rest) ++ [7,8,9]
      case (PatSeqEdge { postfix = [], prefix = prefix, middle = middle } & lhs, PatSeqTot rhs) then
        parseOk (PatSeqEdge {
          prefix = prefix,
          middle = middle,
          postfix = rhs.pats,
          ty = ityunknown_ info,
          info = info
        })
      case _ then
        parseErr (info, "Sequence edge error")
    end
  
  sem groupingsAllowedPat =
  | (OpPatSeqEdge _, OpPatSeqEdge _) -> GLeft ()
end

lang BraceParser = AstParserBase
  sem beginParseExprInBrace: all w. State BrkOpExpr ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem beginParseTypeInBrace: all w. State BrkOpType ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem beginParsePatInBrace:  all w. State BrkOpPat  ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Pat,  NextTokenResult)
  
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

  sem parsePatROpen state =
  | { token = LBraceTok {} } & open ->
    beginParsePatInBrace state open (nextToken open.stream)
end

lang RecordParser = BraceParser + RecordAst + RecordTypeAst + RecordPat + WithKeyword
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
        match cur with { token = KeywordTok { val = "with" } } & tokwith then
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
      match cur with { token = LIdentTok { val = field } | HashStringTok { hash = "label", val = field } } & tokfield then
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

  sem beginParsePatInBrace state open =
  | { token = RBraceTok {} } & close ->
    -- this is a empty record
    let info = mergeInfo open.info close.info in
    let pat = PatRecord {
      bindings = mapEmpty cmpSID,
      ty = ityunknown_ info,
      info = info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken close.stream)
  
  | cur ->
    recursive let parseItems = lam acc. lam cur.
      match cur with { token = LIdentTok { val = field } | HashStringTok { hash = "label", val = field } } & tokfield then
        match nextToken tokfield.stream with { token = OperatorTok { val = "=" } } & tokeq then
          let cur = nextToken tokeq.stream in
          result.bind (parsePat cur) (lam pat.
            match pat with (pat, cur) in
            let acc = mapInsert (stringToSid field) pat acc in
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
          parseErr (cur.info, "Missing pattern assignment")
      else
        parseErr (cur.info, "Unexpected token in record")
    in
    
    let res = parseItems (mapEmpty cmpSID) cur in

    result.bind res (lam res.
      match res with (close, bindings) in
      let info = mergeInfo open.info close.info in
      let typ = PatRecord {
        bindings = bindings,
        ty = ityunknown_ info,
        info = info
      } in
      let state = breakableAddAtom (configPat ()) (OpPatAtom typ) state in
      parsePatRClosed state (nextToken close.stream)
    )
end

lang LetDeclParser = AstParserBase + LetDeclAst + LetKeyword + InKeyword
  sem parseExprROpen state =
  | { token = KeywordTok { val = "let" } } & toklet ->
    result.bind (parseDecl toklet) (lam decl.
      match decl with (decl, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in

      match cur with { token = KeywordTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing in expression")
    )

  sem parseDecl =
  | { token = KeywordTok { val = "let" } } & toklet ->
    let cur = nextToken toklet.stream in

    match cur with { token = LIdentTok { val = ident } | HashStringTok { hash = "var", val = ident } } & tokident then
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

lang RecLetsDeclParser = AstParserBase + RecLetsDeclAst + RecursiveKeyword + LetKeyword + InKeyword
  sem parseExprROpen state =
  | { token = KeywordTok { val = "recursive" } } & rokrec ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parseDecl cur) (lam decl.
        match decl with (DeclLet decl, cur) in
        let acc = snoc acc decl in
        switch cur
          case { token = KeywordTok { val = "in" } } & tokin then
            let cur = nextToken tokin.stream in
            parseOk (tokin, cur, acc)
          case { token = KeywordTok { val = "let" } } then
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

lang LamParser = AstParserBase + LamAst + FunTypeAst + LamKeyword
  syn BrkOpExpr lstyle rstyle =
  | OpExprLam (Info, String, Type, Type)

  syn BrkOpType lstyle rstyle =
  | OpTypeArrow Info

  sem getInfoExpr =
  | OpExprLam (info, _, _, _) -> info

  sem getInfoType =
  | OpTypeArrow info -> info

  sem parseExprROpen state =
  | { token = KeywordTok { val = "lam" } } & toklam ->
    let cur = nextToken toklam.stream in

    match match cur with { token = LIdentTok { val = ident } | HashStringTok { hash = "var", val = ident } } & tokident then
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
    parseOk (TmLam {
      ident = nameNoSym ident,
      tyAnnot = tyAnnot,
      tyParam = tyParam,
      body = body,
      ty = ityunknown_ info,
      info = info
    })

  sem constructInfixType =
  | (OpTypeArrow info, from, to) ->
    let info = mergeInfo (infoTy from) (infoTy to) in
    parseOk (TyArrow {
      from = from,
      to = to,
      info = info
    })

  sem groupingsAllowedType =
  | (OpTypeArrow _, OpTypeArrow _) -> GLeft ()
end

lang MatchParser = AstParserBase + MatchAst + NeverAst + MatchKeyword + WithKeyword + ThenKeyword + ElseKeyword + InKeyword
  syn BrkOpExpr lstyle rstyle =
  | OpExprMatchIn (Info, Expr, Pat)
  | OpExprMatchElse (Info, Expr, Pat, Expr)

  sem parseExprROpen state =
  | { token = KeywordTok { val = "match" } } & tokmatch ->
    let cur = nextToken tokmatch.stream in
    let target = parseExpr cur in
    result.bind target (lam target.
      match target with (target, cur) in
      match cur with { token = KeywordTok { val = "with" } } & tokwith then
        let cur = nextToken tokwith.stream in
        let pat = parsePat cur in
        result.bind pat (lam pat.
          match pat with (pat, cur) in
          switch cur
            -- match .. with .. then .. else ..
            case { token = KeywordTok { val = "then" } } & tokthen then
              let cur = nextToken tokthen.stream in
              let thn = parseExpr cur in
              result.bind thn (lam thn.
                match thn with (thn, cur) in
                match cur with { token = KeywordTok { val = "else" } } & tokelse then
                  let cur = nextToken tokelse.stream in
                  let info = mergeInfo tokmatch.info tokelse.info in
                  let state = breakableAddPrefix (configExpr ()) (OpExprMatchElse (info, target, pat, thn)) state in
                  parseExprROpen state cur
                else
                  parseErr (cur.info, "Expected else keyword")
              )

            -- match .. with .. in ..
            case { token = KeywordTok { val = "in" } } & tokin then
              let cur = nextToken tokin.stream in
              let info = mergeInfo tokmatch.info tokin.info in
              let state = breakableAddPrefix (configExpr ()) (OpExprMatchIn (info, target, pat)) state in
              parseExprROpen state cur

            case _ then
              parseErr (cur.info, "Expected with or in keyword")
          end
        )        
      else
        parseErr (cur.info, "Expected with keyword")
    )
  
  sem constructPrefixExpr =
  | (OpExprMatchIn (info, target, pat), inexpr) ->
    parseOk (TmMatch {
      target = target,
      pat = pat,
      thn = inexpr,
      els = TmNever {
        ty = ityunknown_ info,
        info = info
      },
      ty = ityunknown_ info,
      info = info
    })

  | (OpExprMatchElse (info, target, pat, thn), elsexpr) ->
    parseOk (TmMatch {
      target = target,
      pat = pat,
      thn = thn,
      els = elsexpr,
      ty = ityunknown_ info,
      info = info
    })
end

lang NeverParser = AstParserBase + NeverAst + NeverKeyword
  sem parseExprROpen state =
  | { token = KeywordTok { val = "never" } } & cur ->
    let expr = TmNever {
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

lang AndParser = AstParserBase + AndPat
  syn BrkOpPat lstyle rstyle =
  | OpPatAnd Info

  sem getInfoPat =
  | OpPatAnd info -> info

  sem parsePatRClosed state =
  | { token = OperatorTok { val = "&" } } & tokop ->
    match breakableAddInfix (configPat ()) (OpPatAnd tokop.info) state with Some(state) then
      parsePatROpen state (nextToken tokop.stream)
    else
      parseErr (tokop.info, "Breakable add infix error")

  sem constructInfixPat =
  | (OpPatAnd info, lhs, rhs) ->
    let info = mergeInfo (infoPat lhs) (infoPat rhs) in
    parseOk (PatAnd {
      lpat = lhs,
      rpat = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem groupingsAllowedPat =
  | (OpPatAnd _, OpPatAnd _) -> GLeft ()
end

lang OrParser = AstParserBase + OrPat
  syn BrkOpPat lstyle rstyle =
  | OpPatOr Info

  sem getInfoPat =
  | OpPatOr info -> info

  sem parsePatRClosed state =
  | { token = OperatorTok { val = "|" } } & tokop ->
    match breakableAddInfix (configPat ()) (OpPatOr tokop.info) state with Some(state) then
      parsePatROpen state (nextToken tokop.stream)
    else
      parseErr (tokop.info, "Breakable add infix error")

  sem constructInfixPat =
  | (OpPatOr info, lhs, rhs) ->
    let info = mergeInfo (infoPat lhs) (infoPat rhs) in
    parseOk (PatOr {
      lpat = lhs,
      rpat = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem groupingsAllowedPat =
  | (OpPatOr _, OpPatOr _) -> GLeft ()
end

lang NotParser = AstParserBase + NotPat
  syn BrkOpPat lstyle rstyle =
  | OpPatNot Info

  sem getInfoPat =
  | OpPatNot info -> info

  sem parsePatROpen state =
  | { token = OperatorTok { val = "!" } } & tokop ->
    let state = breakableAddPrefix (configPat ()) (OpPatNot tokop.info) state in
    parsePatROpen state (nextToken tokop.stream)

  sem constructPrefixPat =
  | (OpPatNot info, rhs) ->
    let info = mergeInfo info (infoPat rhs) in
    parseOk (PatNot {
      subpat = rhs,
      ty = ityunknown_ info,
      info = info
    })
  
  sem groupingsAllowedPat =
  | (OpPatNot _, OpPatNot _) -> GLeft ()
end

-- TODO: Better solution
lang PrecedenceParser = AppParser + DataParser + LamParser + LetDeclParser + AndParser + OrParser + NotParser
  sem groupingsAllowedExpr =
  | (OpExprDecl _, OpExprApp _) -> GRight ()
  | (OpExprLam _, OpExprApp _) -> GRight ()
  | (OpExprConApp _, OpExprApp _) -> GLeft ()

  sem groupingsAllowedType =
  | (OpTypeApp _, OpTypeArrow _) -> GLeft ()
  | (OpTypeArrow _, OpTypeApp _) -> GRight ()
  | (OpTypeConApp _, OpTypeApp _) -> GLeft ()

  sem groupingsAllowedPat =
  | (OpPatAnd _, OpPatOr _) -> GLeft ()
  | (OpPatAnd _, OpPatNot _) -> GRight ()
  | (OpPatOr _, OpPatAnd _) -> GRight ()
  | (OpPatOr _, OpPatNot _) -> GRight ()
  | (OpPatNot _, OpPatAnd _) -> GLeft ()
  | (OpPatNot _, OpPatOr _) -> GLeft ()
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

  sem parsePatROpen state =
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
  + DataParser
  + ParenParser
  + UnitParser
  + TupleParser
  + RecordParser
  + LetDeclParser
  + RecLetsDeclParser
  + LamParser
  + MatchParser
  + NeverParser
  + AndParser
  + OrParser
  + NotParser
  + PrecedenceParser
  + UnexpectedTokenParser
end

lang TestParser =
    AstParser
  + MExprPrettyPrint
  + MExprEq
  + MExprToJson
end

type TestResult
con OkSame: () -> TestResult        -- Same result
con OkSameExInfo: () -> TestResult  -- Same result excluding info field
con OkFail: () -> TestResult        -- Both fails
con Fail: () -> TestResult          -- Result is different

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
  switch (result.toOption a, result.toOption b)
    case (Some a, Some b) then
      match eqString (jsonStr a) (jsonStr b) with true then
        OkSame ()
      else match eqExpr a b with true then
        OkSameExInfo ()
      else
        Fail ()
    case (None (), None ()) then
      OkFail ()
    case _ then
      Fail ()
  end in

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

-- let str = "(1,)" in
-- printLn "\nBoot:";
-- printAstBoot str;
-- printLn "Native:";
-- printAst str;

utest compare "0" with OkSame () in
utest compare "1" with OkSame () in
utest compare "-1" with OkSame () in

utest compare "0.0" with OkSame () in
utest compare "1.0" with OkSame () in
utest compare "-1.0" with OkSame () in

utest compare "true" with OkSame () in
utest compare "false" with OkSame () in

utest compare "'a'" with OkSame () in
utest compare "'😊'" with OkSame () in

utest compare "\"test\"" with OkSame () in

utest compare "addi 1 2" with OkSame () in
utest compare "addi 1 2 3" with OkSame () in
utest compare "addi addi 1 2 3" with OkSame () in
utest compare "addi (addi 1 2) 3" with OkSame () in
utest compare "addi 1 (addi 2 3)" with OkSame () in

utest compare "a" with OkSame () in
utest compare "#frozen\"a\"" with OkSame () in
utest compare "#var\"a\"" with OkSame () in

utest compare "()" with OkSameExInfo () in
utest compare "(())" with OkSameExInfo () in
utest compare "addi () ()" with OkSameExInfo () in
utest compare "(addi ()) ()" with OkSameExInfo () in
utest compare "(" with OkFail () in
utest compare ")" with OkFail () in

utest compare "let a = 1 in a" with OkSameExInfo () in
utest compare "let a = 1 in let b = 2 in addi a b" with OkSameExInfo () in
utest compare "let a = 1" with OkFail () in

utest compare "let a: Int = 1 in a" with OkSameExInfo () in
utest compare "let a: Float = 1.0 in a" with OkSameExInfo () in
utest compare "let a: Bool = true in a" with OkSameExInfo () in
utest compare "let a: Char = 'a' in a" with OkSameExInfo () in
utest compare "let a: String = \"test\" in a" with OkSameExInfo () in

utest compare "let a: Int Int = 1 1 in a" with OkSameExInfo () in

utest compare "let a: Int -> Int = addi 1 in a" with OkSameExInfo () in
utest compare "let a: Int Int -> Int = addi in a" with OkSameExInfo () in

utest compare "[]" with OkSame () in
utest compare "[" with OkFail () in
utest compare "]" with OkFail () in
utest compare "[1]" with OkSame () in
utest compare "[1,]" with OkFail () in
utest compare "[,]" with OkFail () in
utest compare "[,1]" with OkFail () in
utest compare "[1, 2]" with OkSame () in
utest compare "[1, [2, 3]]" with OkSame () in
utest compare "[[1, 2], 3]" with OkSame () in
utest compare "cons 0 [1, 2]" with OkSame () in
utest compare "[1 2]" with OkSame () in

utest compare "let a: [Int] = () in a" with OkSameExInfo () in
utest compare "let a: [[Int]] = () in a" with OkSameExInfo () in

utest compare "lam. ()" with OkSameExInfo () in
utest compare "lam a. a" with OkSameExInfo () in
utest compare "lam a: Int. a" with OkSameExInfo () in
utest compare "lam. lam. ()" with OkSameExInfo () in
utest compare "lam a. lam b. addi a b" with OkSameExInfo () in

utest compare "(1, 2)" with OkSame () in
utest compare "(1, (2, 3))" with OkSame () in
utest compare "((1, 2), 3)" with OkSame () in
utest compare "(1,)" with OkSame () in
utest compare "(1,2,)" with OkFail () in
utest compare "(,)" with OkFail () in
utest compare "(,1)" with OkFail () in

utest compare "let a: ((Int, Bool), String) = () in a" with OkSameExInfo () in

utest compare "{a = 1, b = 2}" with OkSame () in
utest compare "{a = 1, bc = { b = 2, c = 3 } }" with OkSame () in
utest compare "{#label\"a\" = 1, b = 2}" with OkSameExInfo () in
utest compare "{" with OkFail () in
utest compare "}" with OkFail () in
utest compare "{a}" with OkFail () in
utest compare "{a = }" with OkFail () in
utest compare "{a = 1, }" with OkFail () in

utest compare "let a: { a: Int, b: Bool } = () in a" with OkSameExInfo () in
utest compare "let a: { a: Int, bc: { b: Bool, c: Char } } = () in a" with OkSameExInfo () in

utest compare "{negi 1 with b = 2}" with OkSameExInfo () in
utest compare "{negi 1 with b = 2, c = 3}" with OkSameExInfo () in
utest compare "{{negi 1 with b = 2} with c = 3}" with OkSameExInfo () in
utest compare "{negi 1 with }" with OkFail () in

utest compare "never" with OkSame () in

utest compare "recursive let a = lam b. 1 in c" with OkSameExInfo () in

utest compare "recursive let a = lam b. 1 let c = lam d. 2 in e" with OkSameExInfo () in

utest compare "Test ()" with OkSameExInfo () in
utest compare "Test (1, 2, 3)" with OkSame () in
utest compare "Test {}" with OkSame () in
utest compare "Test {a = 1, b = 2}" with OkSame () in

utest compare "let o: Option a b c = Option 1 2 3 in ()" with OkSameExInfo () in

utest compare "match a with 1 in b" with OkSameExInfo () in
utest compare "match a with true in b" with OkSameExInfo () in
utest compare "match a with 'a' in b" with OkSameExInfo () in
utest compare "match a with \"test\" in b" with OkSameExInfo () in

utest compare "match a with 1 then b else c" with OkSameExInfo () in

utest compare "match a" with OkFail () in
utest compare "match a with 1" with OkFail () in
utest compare "match a with 1 then" with OkFail () in
utest compare "match a with 1 then b else" with OkFail () in

utest compare "match () with () in x" with OkSameExInfo () in
utest compare "match (a) with (1) in x" with OkSameExInfo () in
utest compare "match (a, b) with (1, 2) in x" with OkSameExInfo () in

utest compare "match a with {} in x" with OkSameExInfo () in
utest compare "match a with { b = 1 } in x" with OkSameExInfo () in
utest compare "match a with { b = 1, cd = { c = 2, d = 3 } } in x" with OkSameExInfo () in

utest compare "match a with [] in x" with OkSameExInfo () in
utest compare "match a with [1] in x" with OkSameExInfo () in
utest compare "match a with [1, 2] in x" with OkSameExInfo () in
utest compare "match a with [1, [3, 4]] in x" with OkSameExInfo () in

utest compare "match a with [1] ++ rest in x" with OkSameExInfo () in
utest compare "match a with rest ++ [1] in x" with OkSameExInfo () in
utest compare "match a with [1] ++ rest ++ [1] in x" with OkSameExInfo () in

utest compare "match a with [1] ++ [1] in x" with OkFail () in
utest compare "match a with rest ++ rest in x" with OkFail () in
utest compare "match a with [1] ++ rest ++ [1] ++ rest in x" with OkFail () in
utest compare "match a with rest ++ [1] ++ rest ++ [1] in x" with OkFail () in

()
