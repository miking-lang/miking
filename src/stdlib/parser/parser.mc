/-

This is the new parser for MCore.

The parser is designed to be as extensible as possible.
It is built on top of the breakable library.

The new parser is simply tested against the ocaml boot parser.
The tests checks that the parsed AST is identical.

`misc/parser-compare.mc` runs more sophisticated tests on full .mc files.
`misc/test` runs parser-compare on most files in the project.

-/

include "basic-types.mc"
include "common.mc"
include "lexer.mc"
include "mexpr/info.mc"
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/json-debug.mc"
include "mexpr/pprint.mc"
include "mlang/ast.mc"
include "mlang/eq.mc"
include "mlang/boot-parser.mc"
include "mlang/pprint.mc"
include "json.mc"
include "fileutils.mc"
include "seq.mc"
include "string.mc"
include "stringid.mc"
include "char.mc"
include "option.mc"
include "map.mc"
include "set.mc"
include "parser/breakable.mc"
include "name.mc"
include "result.mc"

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

  sem startsAtomExpr: NextTokenResult -> Bool
  sem startsAtomType: NextTokenResult -> Bool

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
  sem parseExpr +=
  | cur ->
    let state = breakableInitState () in
    parseExprROpen state cur

  sem parseType +=
  | cur ->
    let state = breakableInitState () in
    parseTypeROpen state cur

  sem parsePat +=
  | cur ->
    let state = breakableInitState () in
    parsePatROpen state cur

  sem finalizeParseExpr state +=
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

  sem finalizeParseType state +=
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

  sem finalizeParsePat state +=
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

  sem startsAtomExpr +=
  | _ -> false

  sem startsAtomType +=
  | _ -> false

  sem constructPrefixExpr +=
  | (OpExprDecl decl, inexpr) ->
    let info = mergeInfo (infoDecl decl) (infoTm inexpr) in
    parseOk (TmDecl {
      decl = decl,
      inexpr = inexpr,
      ty = ityunknown_ info,
      info = info
    })

  sem configExpr +=
  | _ ->
    {
      topAllowed = #frozen"topAllowedExpr",
      leftAllowed = #frozen"leftAllowedExpr",
      rightAllowed = #frozen"rightAllowedExpr",
      parenAllowed = #frozen"parenAllowedExpr",
      groupingsAllowed = #frozen"groupingsAllowedExpr"
    }

  sem configType +=
  | _ ->
    {
      topAllowed = #frozen"topAllowedType",
      leftAllowed = #frozen"leftAllowedType",
      rightAllowed = #frozen"rightAllowedType",
      parenAllowed = #frozen"parenAllowedType",
      groupingsAllowed = #frozen"groupingsAllowedType"
    }

  sem configPat +=
  | _ ->
    {
      topAllowed = #frozen"topAllowedPat",
      leftAllowed = #frozen"leftAllowedPat",
      rightAllowed = #frozen"rightAllowedPat",
      parenAllowed = #frozen"parenAllowedPat",
      groupingsAllowed = #frozen"groupingsAllowedPat"
    }

  sem topAllowedExpr +=
  | _ -> true

  sem topAllowedType +=
  | _ -> true

  sem topAllowedPat +=
  | _ -> true

  sem leftAllowedExpr +=
  | _ -> true

  sem leftAllowedType +=
  | _ -> true

  sem leftAllowedPat +=
  | _ -> true

  sem rightAllowedExpr +=
  | _ -> true

  sem rightAllowedType +=
  | _ -> true

  sem rightAllowedPat +=
  | _ -> true

  sem parenAllowedExpr +=
  | _ -> GEither ()

  sem parenAllowedType +=
  | _ -> GEither ()

  sem parenAllowedPat +=
  | _ -> GEither ()

  sem groupingsAllowedExpr +=
  | _ -> GEither ()

  sem groupingsAllowedType +=
  | _ -> GEither ()

  sem groupingsAllowedPat +=
  | _ -> GEither ()

  sem terminalInfosExpr +=
  | op -> [getInfoExpr op]

  sem terminalInfosType +=
  | op -> [getInfoType op]

  sem terminalInfosPat +=
  | op -> [getInfoPat op]

  sem getInfoExpr +=
  | OpExprAtom expr -> infoTm expr
  | OpExprDecl decl -> infoDecl decl

  sem getInfoType +=
  | OpTypeAtom typ -> infoTy typ

  sem getInfoPat +=
  | OpPatAtom pat -> infoPat pat

  -- Matches a `=` or `+=` assignment operator, whether it is its own
  -- token or the prefix of a merged operator token. Returns whether it
  -- was `+=` and the token stream right after it.
  sem matchAssignOp: NextTokenResult -> Option (Bool, NextTokenResult)
  sem matchAssignOp =
  | cur ->
    match cur.token with OperatorTok { val = v } then
      if eqString v "+=" then Some (true, nextToken cur.stream)
      else if eqString v "=" then Some (false, nextToken cur.stream)
      else if isPrefix eqChar "+=" v then
        optionMap (lam c. (true, c)) (splitOperatorPrefix cur "+=")
      else if isPrefix eqChar "=" v then
        optionMap (lam c. (false, c)) (splitOperatorPrefix cur "=")
      else None ()
    else None ()

end

lang WithKeyword = Lexer
  sem identIsKeyword +=
  | "with" -> true
end

lang LetKeyword = Lexer
  sem identIsKeyword +=
  | "let" -> true
end

lang InKeyword = Lexer
  sem identIsKeyword +=
  | "in" -> true
end

lang ThenKeyword = Lexer
  sem identIsKeyword +=
  | "then" -> true
end

lang ElseKeyword = Lexer
  sem identIsKeyword +=
  | "else" -> true
end

lang TrueKeyword = Lexer
  sem identIsKeyword +=
  | "true" -> true
end

lang FalseKeyword = Lexer
  sem identIsKeyword +=
  | "false" -> true
end

lang RecursiveKeyword = Lexer
  sem identIsKeyword +=
  | "recursive" -> true
end

lang LamKeyword = Lexer
  sem identIsKeyword +=
  | "lam" -> true
end

lang MatchKeyword = Lexer
  sem identIsKeyword +=
  | "match" -> true
end

lang NeverKeyword = Lexer
  sem identIsKeyword +=
  | "never" -> true
end

lang UtestKeyword = Lexer
  sem identIsKeyword +=
  | "utest" -> true
end

lang UsingKeyword = Lexer
  sem identIsKeyword +=
  | "using" -> true
end

lang SwitchKeyword = Lexer
  sem identIsKeyword +=
  | "switch" -> true
end

lang CaseKeyword = Lexer
  sem identIsKeyword +=
  | "case" -> true
end

lang EndKeyword = Lexer
  sem identIsKeyword +=
  | "end" -> true
end

lang TypeKeyword = Lexer
  sem identIsKeyword +=
  | "type" -> true
end

lang ConKeyword = Lexer
  sem identIsKeyword +=
  | "con" -> true
end

lang ExternalKeyword = Lexer
  sem identIsKeyword +=
  | "external" -> true
end

lang UseKeyword = Lexer
  sem identIsKeyword +=
  | "use" -> true
end

lang AllKeyword = Lexer
  sem identIsKeyword +=
  | "all" -> true
end

lang IfKeyword = Lexer
  sem identIsKeyword +=
  | "if" -> true
end

lang LangKeyword = Lexer
  sem identIsKeyword +=
  | "lang" -> true
end

lang SynKeyword = Lexer
  sem identIsKeyword +=
  | "syn" -> true
end

lang SemKeyword = Lexer
  sem identIsKeyword +=
  | "sem" -> true
end

lang IncludeKeyword = Lexer
  sem identIsKeyword +=
  | "include" -> true
end

lang MexprKeyword = Lexer
  sem identIsKeyword +=
  | "mexpr" -> true
end

-- `Unknown` is a reserved type keyword in boot (producing `TyUnknown`
-- directly), not a generic constructor-type reference.
lang UnknownTypeParser = AstParserBase + UnknownTypeAst
  sem startsAtomType +=
  | { token = UIdentTok { val = "Unknown" } } -> true

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "Unknown" } } & cur ->
    let typ = ityunknown_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)
end

lang IntParser = AstParserBase + IntAst + IntPat
  sem startsAtomExpr +=
  | { token = IntTok { } } -> true

  sem startsAtomType +=
  | { token = UIdentTok { val = "Int" } } -> true

  sem parseExprROpen state +=
  | { token = IntTok { val = val } } & cur ->
    let expr = TmConst {
      val = CInt { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "Int" } } & cur ->
    let typ = ityint_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)

  sem parsePatROpen state +=
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
  sem startsAtomExpr +=
  | { token = FloatTok { } } -> true

  sem startsAtomType +=
  | { token = UIdentTok { val = "Float" } } -> true

  sem parseExprROpen state +=
  | { token = FloatTok { val = val } } & cur ->
    let expr = TmConst {
      val = CFloat { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "Float" } } & cur ->
    let typ = ityfloat_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)
end

lang NegParser = AstParserBase + IntAst + FloatAst + IntPat
  sem startsAtomExpr +=
  | { token = OperatorTok { val = "-" } } -> true

  sem parseExprROpen state +=
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

  sem parsePatROpen state +=
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
  sem startsAtomExpr +=
  | { token = LIdentTok { } } -> true
  | { token = HashStringTok { hash = "frozen" | "var" } } -> true

  sem startsAtomType +=
  | { token = LIdentTok { } } -> true
  | { token = HashStringTok { hash = "var" } } -> true

  sem parseExprROpen state +=
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

  sem parseTypeROpen state +=
  | { token = LIdentTok { val = val } | HashStringTok { hash = "var", val = val } } & cur ->
    let typ = TyVar {
      ident = nameNoSym val,
      info = cur.info
    } in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)

  sem parsePatROpen state +=
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
  syn BrkOpExpr lstyle rstyle +=
  | OpExprApp Info

  syn BrkOpType lstyle rstyle +=
  | OpTypeApp Info

  sem getInfoExpr +=
  | OpExprApp info ->
    info

  sem getInfoType +=
  | OpTypeApp info ->
    info

  sem parseExprRClosed state +=
  | cur ->
    -- check if the next token can be part of the current expression.
    match startsAtomExpr cur with true then
      match breakableAddInfix (configExpr ()) (OpExprApp cur.info) state with Some(state) then
        parseExprROpen state cur
      else
        parseErr (cur.info, "Breakable add infix error")
    else
      finalizeParseExpr state cur

  sem parseTypeRClosed state +=
  | cur ->
    -- check if the next token can be part of the current type.
    match startsAtomType cur with true then
      match breakableAddInfix (configType ()) (OpTypeApp cur.info) state with Some(state) then
        parseTypeROpen state cur
      else
        parseErr (cur.info, "Breakable add infix error")
    else
      finalizeParseType state cur

  sem parsePatRClosed state +=
  | cur ->
    -- patterns can not be applied
    finalizeParsePat state cur

  sem constructInfixExpr +=
  | (OpExprApp info, lhs, rhs) ->
    let info = mergeInfo (infoTm lhs) (infoTm rhs) in
    parseOk (TmApp {
      lhs = lhs,
      rhs = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem constructInfixType +=
  | (OpTypeApp info, lhs, rhs) ->
    let info = mergeInfo (infoTy lhs) (infoTy rhs) in
    parseOk (TyApp {
      lhs = lhs,
      rhs = rhs,
      info = info
    })

  sem groupingsAllowedExpr +=
  | (OpExprApp _, OpExprApp _) -> GLeft ()

  sem groupingsAllowedType +=
  | (OpTypeApp _, OpTypeApp _)  -> GLeft ()
end

lang DataParser = AstParserBase + DataAst + ConTypeAst + AppTypeAst + DataPat + DataTypeAst + VarTypeAst
  syn BrkOpExpr lstyle rstyle +=
  | OpExprConApp (Info, Name)

  sem startsAtomType +=
  | { token = UIdentTok { } } -> true
  | { token = HashStringTok { hash = "con" } } -> true

  syn BrkOpPat lstyle rstyle +=
  | OpPatConApp (Info, Name)

  sem getInfoExpr +=
  | OpExprConApp (info, _) -> info

  sem getInfoPat +=
  | OpPatConApp (info, _) -> info

  sem parseExprROpen state +=
  | { token = UIdentTok { val = val } | HashStringTok { hash = "con", val = val } } & tokident ->
    let cur = nextToken tokident.stream in
    let ident = nameNoSym val in
    let state = breakableAddPrefix (configExpr ()) (OpExprConApp (tokident.info, ident)) state in
    parseExprROpen state cur

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = val } | HashStringTok { hash = "con", val = val } } & tokident ->
    let cur = nextToken tokident.stream in
    let ident = nameNoSym val in
    match cur with { token = LBraceTok {} } & tokopen then
      let afterOpen = nextToken tokopen.stream in
      if looksLikeConTypeRestriction afterOpen then
        result.bind (parseConTypeRestrictionBody afterOpen) (lam res.
          match res with (data, closeInfo, cur) in
          let typ = TyCon { ident = ident, data = data, info = mergeInfo tokident.info closeInfo } in
          let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
          parseTypeRClosed state cur
        )
      else
        let typ = TyCon { ident = ident, data = ityunknown_ tokident.info, info = tokident.info } in
        let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
        parseTypeRClosed state cur
    else
      let typ = TyCon { ident = ident, data = ityunknown_ tokident.info, info = tokident.info } in
      let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
      parseTypeRClosed state cur

  sem looksLikeConTypeRestriction: NextTokenResult -> Bool
  sem looksLikeConTypeRestriction =
  | { token = OperatorTok { val = "!" } } -> true
  | { token = UIdentTok {} | LIdentTok {} } & tok -> 
    match nextToken tok.stream with { token = OperatorTok { val = ":" } } then false else true
  | _ -> false

  sem parseConTypeRestrictionBody: all w. NextTokenResult -> ParseResult w (Type, Info, NextTokenResult)
  sem parseConTypeRestrictionBody =
  | { token = OperatorTok { val = "!" } } & toknot ->
    match parseConNameList [] (nextToken toknot.stream) with (names, cur) in
    finishConTypeRestriction
      (TyData { info = NoInfo (), universe = mapEmpty nameCmp, positive = false, cons = setOfSeq nameCmp names })
      cur
  | { token = LIdentTok { val = val } } & tokvar ->
    finishConTypeRestriction
      (TyVar { info = NoInfo (), ident = nameNoSym val })
      (nextToken tokvar.stream)
  | cur ->
    match parseConNameList [] cur with (names, cur) in
    finishConTypeRestriction
      (TyData { info = NoInfo (), universe = mapEmpty nameCmp, positive = true, cons = setOfSeq nameCmp names })
      cur

  sem finishConTypeRestriction: all w. Type -> NextTokenResult -> ParseResult w (Type, Info, NextTokenResult)
  sem finishConTypeRestriction data =
  | { token = RBraceTok {} } & tokclose ->
    parseOk (data, tokclose.info, nextToken tokclose.stream)
  | cur -> parseErr (cur.info, "Missing right brace in constructor type restriction")

  sem parseConNameList: [Name] -> NextTokenResult -> ([Name], NextTokenResult)
  sem parseConNameList acc =
  | { token = UIdentTok { val = val } } & tok -> parseConNameList (snoc acc (nameNoSym val)) (nextToken tok.stream)
  | { token = LIdentTok { val = val } } & tok -> parseConNameList (snoc acc (nameNoSym val)) (nextToken tok.stream)
  | cur -> (acc, cur)

  sem parsePatROpen state +=
  | { token = UIdentTok { val = val } | HashStringTok { hash = "con", val = val } } & tokident ->
    let cur = nextToken tokident.stream in
    let ident = nameNoSym val in
    let state = breakableAddPrefix (configPat ()) (OpPatConApp (tokident.info, ident)) state in
    parsePatROpen state cur

  sem constructPrefixExpr +=
  | (OpExprConApp (info, ident), rhs) ->
    let info = mergeInfo info (infoTm rhs) in
    parseOk (TmConApp {
      ident = ident,
      body = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem constructPrefixPat +=
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

  sem startsAtomExpr +=
  | { token = LParenTok {} } -> true

  sem startsAtomType +=
  | { token = LParenTok {} } -> true

  sem beginParseExprInParen state open +=
  | cur ->
    -- start of new expression in paren
    result.bind (parseExpr cur) (lam expr.
      match expr with (expr, cur) in
      endParseExprInParen state open expr cur
    )

  sem endParseExprInParen state open expr +=
  | { token = RParenTok {} } & close ->
    let expr = withInfo (mergeInfo open.info close.info) expr in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken close.stream)

  | cur -> parseErr (cur.info, "Missing closing parenthesis")

  sem beginParseTypeInParen state open +=
  | cur ->
    -- start of new type in paren
    result.bind (parseType cur) (lam typ.
      match typ with (typ, cur) in
      endParseTypeInParen state open typ cur
    )

  sem endParseTypeInParen state open typ +=
  | { token = RParenTok {} } & close ->
    let typ = tyWithInfo (mergeInfo open.info close.info) typ in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken close.stream)

  | cur -> parseErr (cur.info, "Missing closing parenthesis")

  sem beginParsePatInParen state open +=
  | cur ->
    -- start of new pat in paren
    result.bind (parsePat cur) (lam pat.
      match pat with (pat, cur) in
      endParsePatInParen state open pat cur
    )

  sem endParsePatInParen state open pat +=
  | { token = RParenTok {} } & close ->
    let pat = withInfoPat (mergeInfo open.info close.info) pat in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken close.stream)

  | cur -> parseErr (cur.info, "Missing closing parenthesis")

  sem parseExprROpen state +=
  | { token = LParenTok {} } & open ->
    beginParseExprInParen state open (nextToken open.stream)

  sem parseTypeROpen state +=
  | { token = LParenTok {} } & open ->
    beginParseTypeInParen state open (nextToken open.stream)

  sem parsePatROpen state +=
  | { token = LParenTok {} } & open ->
    beginParsePatInParen state open (nextToken open.stream)

end

lang UnitParser = ParenParser + RecordAst + RecordTypeAst + RecordPat
  sem beginParseExprInParen state open +=
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

  sem beginParseTypeInParen state open +=
  | { token = RParenTok {} } & close ->
    -- this is a unit
    let info = mergeInfo open.info close.info in
    let typ = TyRecord {
      fields = mapEmpty cmpSID,
      info = info
    } in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken close.stream)

  sem beginParsePatInParen state open +=
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
  sem endParseExprInParen state open expr +=
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

  sem endParseTypeInParen state open typ +=
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

  sem endParsePatInParen state open pat +=
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
  sem startsAtomExpr +=
  | { token = KeywordTok { val = "true" | "false" } } -> true

  sem startsAtomType +=
  | { token = UIdentTok { val = "Bool" } } -> true

  sem parseExprROpen state +=
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

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "Bool" } } & cur ->
    let typ = itybool_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)

  sem parsePatROpen state +=
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
  sem startsAtomExpr +=
  | { token = CharTok { } } -> true

  sem startsAtomType +=
  | { token = UIdentTok { val = "Char" } } -> true

  sem parseExprROpen state +=
  | { token = CharTok { val = val } } & cur ->
    let expr = TmConst {
      val = CChar { val = val },
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "Char" } } & cur ->
    let typ = itychar_ cur.info in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)

  sem parsePatROpen state +=
  | { token = CharTok { val = val } } & cur ->
    let pat = PatChar {
      val = val,
      ty = tychar_,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
end

-- `Tensor[T]` is a dedicated, keyword-like type syntax (boot reserves
-- `Tensor` and always requires the bracketed argument), distinct from a
-- generic type application.
lang TensorParser = AstParserBase + TensorTypeAst
  sem startsAtomType +=
  | { token = UIdentTok { val = "Tensor" } } -> true

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "Tensor" } } & toktensor ->
    let cur = nextToken toktensor.stream in
    match cur with { token = LBracketTok {} } & toklb then
      let cur = nextToken toklb.stream in
      result.bind (parseType cur) (lam res.
        match res with (ty, cur) in
        match cur with { token = RBracketTok {} } & tokrb then
          let info = mergeInfo toktensor.info tokrb.info in
          let typ = TyTensor { ty = ty, info = info } in
          let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
          parseTypeRClosed state (nextToken tokrb.stream)
        else
          parseErr (cur.info, "Missing right bracket")
      )
    else
      parseErr (cur.info, "Missing left bracket")
end

lang StringParser = AstParserBase + SeqAst + CharAst + SeqTotPat + CharPat + SeqTypeAst + CharTypeAst
  sem startsAtomExpr +=
  | { token = StringTok { } } -> true

  sem startsAtomType +=
  | { token = UIdentTok { val = "String" } } -> true

  sem parseExprROpen state +=
  | { token = StringTok { val = val } } & cur ->
    let expr = TmSeq {
      tms = map (lam ch. TmConst {
        val = CChar { val = ch },
        ty = tyunknown_,
        info = NoInfo ()
      }) val,
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "String" } } & cur ->
    let typ = TySeq { ty = TyChar { info = NoInfo () }, info = cur.info } in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)

  sem parsePatROpen state +=
  | { token = StringTok { val = val } } & cur ->
    let pat = PatSeqTot {
      pats = map (lam ch. PatChar {
        val = ch,
        ty = tychar_,
        info = NoInfo ()
      }) val,
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configPat ()) (OpPatAtom pat) state in
    parsePatRClosed state (nextToken cur.stream)
end

lang SeqParser = AstParserBase + SeqAst + SeqTypeAst + SeqTotPat + SeqEdgePat + NamedPat
  syn BrkOpPat lstyle rstyle +=
  | OpPatSeqEdge Info

  sem getInfoPat +=
  | OpPatSeqEdge info -> info

  sem startsAtomExpr +=
  | { token = LBracketTok { } } -> true

  sem startsAtomType +=
  | { token = LBracketTok { } } -> true

  sem parseExprROpen state +=
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

  sem parseTypeROpen state +=
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

  sem parsePatROpen state +=
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

  sem parsePatRClosed state +=
  | { token = OperatorTok { val = "++" } } & tokpp ->
    match breakableAddInfix (configPat ()) (OpPatSeqEdge tokpp.info) state with Some(state) then
      let cur = nextToken tokpp.stream in
      parsePatROpen state cur
    else
      parseErr (tokpp.info, "Breakable add infix error")

  sem constructInfixPat +=
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
  
  sem groupingsAllowedPat +=
  | (OpPatSeqEdge _, OpPatSeqEdge _) -> GLeft ()
end

lang BraceParser = AstParserBase
  sem beginParseExprInBrace: all w. State BrkOpExpr ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Expr, NextTokenResult)
  sem beginParseTypeInBrace: all w. State BrkOpType ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Type, NextTokenResult)
  sem beginParsePatInBrace:  all w. State BrkOpPat  ROpen -> NextTokenResult -> NextTokenResult -> ParseResult w (Pat,  NextTokenResult)
  
  sem startsAtomExpr +=
  | { token = LBraceTok {} } -> true

  sem startsAtomType +=
  | { token = LBraceTok {} } -> true

  sem parseExprROpen state +=
  | { token = LBraceTok {} } & open ->
    beginParseExprInBrace state open (nextToken open.stream)

  sem parseTypeROpen state +=
  | { token = LBraceTok {} } & open ->
    beginParseTypeInBrace state open (nextToken open.stream)

  sem parsePatROpen state +=
  | { token = LBraceTok {} } & open ->
    beginParsePatInBrace state open (nextToken open.stream)
end

lang RecordParser = BraceParser + RecordAst + RecordTypeAst + RecordPat + WithKeyword
  sem beginParseExprInBrace state open +=
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
          recursive let parseItems = lam acc. lam cur.
            match cur with { token = LIdentTok { val = field } | HashStringTok { hash = "label", val = field } } & tokfield then
              match nextToken tokfield.stream with { token = OperatorTok { val = "=" } } & tokeq then
                let cur = nextToken tokeq.stream in
                result.bind (parseExpr cur) (lam res.
                  match res with (expr, cur) in
                  let acc = snoc acc (stringToSid field, expr) in
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
              parseErr (cur.info, "Unexpected token in record update")
          in

          let res = parseItems [] cur in

          result.bind res (lam res.
            match res with (close, updates) in
            let info = mergeInfo open.info close.info in
            let expr = foldl
              (lam rec. lam update : (SID, Expr).
                TmRecordUpdate {
                  rec = rec,
                  key = update.0,
                  value = update.1,
                  ty = ityunknown_ info,
                  info = info
                })
              rec updates
            in
            let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
            parseExprRClosed state (nextToken close.stream)
          )
        else
          parseErr (cur.info, "Unexpected token in record")
      )

  sem beginParseTypeInBrace state open +=
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

  sem beginParsePatInBrace state open +=
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
  sem parseExprROpen state +=
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

  sem parseDecl +=
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

lang RecLetsDeclParser = AstParserBase + RecLetsDeclAst + RecursiveKeyword + LetKeyword + InKeyword + EndKeyword
  sem parseExprROpen state +=
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

  -- Top-level form: `recursive let ... let ... end` (terminated by `end`,
  -- unlike the expression form above which is terminated by `in`).
  sem parseDecl +=
  | { token = KeywordTok { val = "recursive" } } & rokrec ->
    recursive let parseItems = lam acc. lam cur.
      result.bind (parseDecl cur) (lam decl.
        match decl with (DeclLet decl, cur) in
        let acc = snoc acc decl in
        switch cur
          case { token = KeywordTok { val = "end" } } & tokend then
            parseOk (tokend, nextToken tokend.stream, acc)
          case { token = KeywordTok { val = "let" } } then
            parseItems acc cur
          case _ then
            parseErr (cur.info, "Unexpected token in recursive declaration")
        end
      )
    in

    let cur = nextToken rokrec.stream in
    result.bind (parseItems [] cur) (lam res.
      match res with (tokend, cur, bindings) in
      let decl = DeclRecLets {
        bindings = bindings,
        info = mergeInfo rokrec.info tokend.info
      } in
      parseOk (decl, cur)
    )
end

lang TypeDeclParser = AstParserBase + TypeDeclAst + VariantTypeAst + TypeKeyword + InKeyword
  sem parseExprROpen state +=
  | { token = KeywordTok { val = "type" } } & toktype ->
    result.bind (parseDecl toktype) (lam decl.
      match decl with (decl, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in

      match cur with { token = KeywordTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing in expression")
    )

  sem parseDecl +=
  | { token = KeywordTok { val = "type" } } & toktype ->

    recursive let parseParams = lam acc. lam lastInfo. lam cur.
      match cur with { token = LIdentTok { val = param } | HashStringTok { hash = "var", val = param } } & tokparam then
        let cur = nextToken tokparam.stream in
        let acc = snoc acc (nameNoSym param) in
        parseParams acc tokparam.info cur
      else
        (acc, lastInfo, cur)
    in

    let cur = nextToken toktype.stream in

    match cur with { token = UIdentTok { val = ident } | HashStringTok { hash = "con", val = ident } } & tokident then
      let cur = nextToken tokident.stream in
      let params = parseParams [] tokident.info cur in
      match params with (params, lastInfo, cur) in

      let tyIdent = match cur with { token = OperatorTok { val = "=" } } & tokeq then
        let cur = nextToken tokeq.stream in
        result.map (lam r. match r with (typ, cur) in (typ, infoTy typ, cur)) (parseType cur)
      else
        let typ = TyVariant {
          info = NoInfo (),
          constrs = mapEmpty nameCmp
        } in
        parseOk (typ, lastInfo, cur)
      in

      result.bind tyIdent (lam tyIdent.
        match tyIdent with (tyIdent, declEndInfo, cur) in
        let decl = DeclType {
          ident = nameNoSym ident,
          params = params,
          tyIdent = tyIdent,
          info = mergeInfo toktype.info declEndInfo
        } in
        parseOk (decl, cur)
      )
    else
      parseErr (cur.info, "Missing identifier")
end


lang LamParser = AstParserBase + LamAst + FunTypeAst + LamKeyword
  syn BrkOpExpr lstyle rstyle +=
  | OpExprLam (Info, String, Type, Type)

  syn BrkOpType lstyle rstyle +=
  | OpTypeArrow Info

  sem getInfoExpr +=
  | OpExprLam (info, _, _, _) -> info

  sem getInfoType +=
  | OpTypeArrow info -> info

  sem parseExprROpen state +=
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

  sem parseTypeRClosed state +=
  | { token = OperatorTok { val = "->" } } & cur ->
    match breakableAddInfix (configType ()) (OpTypeArrow cur.info) state with Some(state) then
      let cur = nextToken cur.stream in
      parseTypeROpen state cur
    else
      parseErr (cur.info, "Breakable add infix error")

  sem constructPrefixExpr +=
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

  sem constructInfixType +=
  | (OpTypeArrow info, from, to) ->
    let info = mergeInfo (infoTy from) (infoTy to) in
    parseOk (TyArrow {
      from = from,
      to = to,
      info = info
    })

  sem groupingsAllowedType +=
  | (OpTypeArrow _, OpTypeArrow _) -> GRight ()
end

lang MatchParser = AstParserBase + MatchAst + NeverAst + MatchKeyword + WithKeyword + ThenKeyword + ElseKeyword + InKeyword
  syn BrkOpExpr lstyle rstyle +=
  | OpExprMatchIn (Info, Expr, Pat)
  | OpExprMatchElse (Info, Expr, Pat, Expr)

  sem getInfoExpr +=
  | OpExprMatchIn (info, _, _) -> info
  | OpExprMatchElse (info, _, _, _) -> info

  sem parseExprROpen state +=
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
  
  sem constructPrefixExpr +=
  | (OpExprMatchIn (info, target, pat), inexpr) ->
    let info = mergeInfo info (infoTm inexpr) in
    parseOk (TmMatch {
      target = target,
      pat = pat,
      thn = inexpr,
      els = TmNever {
        ty = tyunknown_,
        info = NoInfo ()
      },
      ty = ityunknown_ info,
      info = info
    })

  | (OpExprMatchElse (info, target, pat, thn), elsexpr) ->
    let info = mergeInfo info (infoTm elsexpr) in
    parseOk (TmMatch {
      target = target,
      pat = pat,
      thn = thn,
      els = elsexpr,
      ty = ityunknown_ info,
      info = info
    })
end

lang SwitchParser = AstParserBase + MatchAst + LetDeclAst + VarAst + NeverAst + SwitchKeyword + CaseKeyword + EndKeyword
  sem parseExprROpen state +=
  | { token = KeywordTok { val = "switch" } } & tokswitch ->

    recursive let parseItems = lam cur.
      switch cur
        case { token = KeywordTok { val = "case" } } & tokcase then
          let cur = nextToken tokcase.stream in
          let pat = parsePat cur in
          result.bind pat (lam pat.
            match pat with (pat, cur) in
            match cur with { token = KeywordTok { val = "then" } } & tokthen then
              let cur = nextToken tokthen.stream in
              let thn = parseExpr cur in
              result.bind thn (lam thn.
                match thn with (thn, cur) in
                let els = parseItems cur in
                result.bind els (lam els.
                  match els with (els, tokend, cur) in
                  let expr = TmMatch {
                    target = TmVar {
                      ident = nameNoSym "X",
                      ty = tyunknown_,
                      info = NoInfo (),
                      frozen = false
                    },
                    pat = pat,
                    thn = thn,
                    els = els,
                    ty = tyunknown_,
                    info = NoInfo ()
                  } in
                  parseOk (expr, tokend, cur)
                )
              )
            else
              parseErr (cur.info, "Expected then keyword")
          )
        case { token = KeywordTok { val = "end" } } & tokend then
          let cur = nextToken tokend.stream in
          let expr = TmNever {
            ty = tyunknown_,
            info = NoInfo ()
          } in
          parseOk (expr, tokend, cur)
        case _ then
          parseErr (cur.info, "Expected case or end keyword")
      end
    in

    let cur = nextToken tokswitch.stream in
    let body = parseExpr cur in
    result.bind body (lam body.
      match body with (body, cur) in

      let inexpr = parseItems cur in
      result.bind inexpr (lam inexpr.
        match inexpr with (inexpr, tokend, cur) in
        let info = mergeInfo tokswitch.info tokend.info in
        let expr = TmDecl {
          decl = DeclLet {
            ident = nameNoSym "X",
            tyAnnot = ityunknown_ info,
            tyBody = ityunknown_ info,
            body = body,
            info = info
          },
          inexpr = inexpr,
          ty = ityunknown_ info, 
          info = info
        } in

        let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
        parseExprRClosed state cur
      )
    )
end

lang NeverParser = AstParserBase + NeverAst + NeverKeyword
  sem parseExprROpen state +=
  | { token = KeywordTok { val = "never" } } & cur ->
    let expr = TmNever {
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)
end

lang AndParser = AstParserBase + AndPat
  syn BrkOpPat lstyle rstyle +=
  | OpPatAnd Info

  sem getInfoPat +=
  | OpPatAnd info -> info

  sem parsePatRClosed state +=
  | { token = OperatorTok { val = "&" } } & tokop ->
    match breakableAddInfix (configPat ()) (OpPatAnd tokop.info) state with Some(state) then
      parsePatROpen state (nextToken tokop.stream)
    else
      parseErr (tokop.info, "Breakable add infix error")

  sem constructInfixPat +=
  | (OpPatAnd info, lhs, rhs) ->
    let info = mergeInfo (infoPat lhs) (infoPat rhs) in
    parseOk (PatAnd {
      lpat = lhs,
      rpat = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem groupingsAllowedPat +=
  | (OpPatAnd _, OpPatAnd _) -> GRight ()
end

lang OrParser = AstParserBase + OrPat
  syn BrkOpPat lstyle rstyle +=
  | OpPatOr Info

  sem getInfoPat +=
  | OpPatOr info -> info

  sem parsePatRClosed state +=
  | { token = OperatorTok { val = "|" } } & tokop ->
    match breakableAddInfix (configPat ()) (OpPatOr tokop.info) state with Some(state) then
      parsePatROpen state (nextToken tokop.stream)
    else
      parseErr (tokop.info, "Breakable add infix error")

  sem constructInfixPat +=
  | (OpPatOr info, lhs, rhs) ->
    let info = mergeInfo (infoPat lhs) (infoPat rhs) in
    parseOk (PatOr {
      lpat = lhs,
      rpat = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem groupingsAllowedPat +=
  | (OpPatOr _, OpPatOr _) -> GRight ()
end

lang NotParser = AstParserBase + NotPat
  syn BrkOpPat lstyle rstyle +=
  | OpPatNot Info

  sem getInfoPat +=
  | OpPatNot info -> info

  sem parsePatROpen state +=
  | { token = OperatorTok { val = "!" } } & tokop ->
    let state = breakableAddPrefix (configPat ()) (OpPatNot tokop.info) state in
    parsePatROpen state (nextToken tokop.stream)

  sem constructPrefixPat +=
  | (OpPatNot info, rhs) ->
    let info = mergeInfo info (infoPat rhs) in
    parseOk (PatNot {
      subpat = rhs,
      ty = ityunknown_ info,
      info = info
    })
  
  sem groupingsAllowedPat +=
  | (OpPatNot _, OpPatNot _) -> GLeft ()
end

lang UtestParser = AstParserBase + UtestDeclAst + UtestKeyword + WithKeyword + UsingKeyword + ElseKeyword + InKeyword
  sem parseExprROpen state +=
  | { token = KeywordTok { val = "utest" } } & tokutest ->
    result.bind (parseDecl tokutest) (lam decl.
      match decl with (decl, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in

      match cur with { token = KeywordTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing in expression")
    )

  sem parseDecl +=
  | { token = KeywordTok { val = "utest" } } & tokutest ->
    let cur = nextToken tokutest.stream in
    let test = parseExpr cur in
    result.bind test (lam test.
      match test with (test, cur) in
      match cur with { token = KeywordTok { val = "with"} } & tokwith then
        let cur = nextToken tokwith.stream in
        let expected = parseExpr cur in
        result.bind expected (lam expected.
          match expected with (expected, cur) in
          let info = mergeInfo tokutest.info (infoTm expected) in

          let tusing = match cur with { token = KeywordTok { val = "using" } } & tokusing then
            let cur = nextToken tokusing.stream in
            result.map (lam tusing.
              match tusing with (tusing, cur) in
              let info = mergeInfo info (infoTm tusing) in
              (Some tusing, cur, info)
            ) (parseExpr cur)
          else
            parseOk (None (), cur, info)
          in

          result.bind tusing (lam tusing.
            match tusing with (tusing, cur, info) in

            let tonfail = match cur with { token = KeywordTok { val = "else" } } & tokelse then
              let cur = nextToken tokelse.stream in
              result.map (lam tonfail.
                match tonfail with (tonfail, cur) in
                let info = mergeInfo info (infoTm tonfail) in
                (Some tonfail, cur, info)
              ) (parseExpr cur)
            else
              parseOk (None (), cur, info)
            in

            result.bind tonfail (lam tonfail.
              match tonfail with (tonfail, cur, info) in

              let decl = DeclUtest {
                test = test,
                expected = expected,
                tusing = tusing,
                tonfail = tonfail,
                info = info
              } in
              parseOk (decl, cur)
            )
          )
        )
      else
        parseErr (cur.info, "Expected with keyword")
    )
end

lang ConDeclParser = AstParserBase + DataDeclAst + ConKeyword + InKeyword
  sem parseExprROpen state +=
  | { token = KeywordTok { val = "con" } } & tokcon ->
    result.bind (parseDecl tokcon) (lam decl.
      match decl with (decl, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in

      match cur with { token = KeywordTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing in expression")
    )

  sem parseDecl +=
  | { token = KeywordTok { val = "con" } } & tokcon ->
    let cur = nextToken tokcon.stream in

    match cur with { token = UIdentTok { val = ident } | HashStringTok { hash = "con", val = ident } } & tokident then
      let cur = nextToken tokident.stream in

      let tyIdent = match cur with { token = OperatorTok { val = ":" } } & tokcol then
        let cur = nextToken tokcol.stream in
        parseType cur
      else
        parseOk (ityunknown_ (mergeInfo tokcon.info tokident.info), cur)
      in

      result.bind tyIdent (lam tyIdent.
        match tyIdent with (tyIdent, cur) in
        let decl = DeclConDef {
          ident = nameNoSym ident,
          tyIdent = tyIdent,
          info = mergeInfo tokcon.info (infoTy tyIdent)
        } in
        parseOk (decl, cur)
      )
    else
      parseErr (cur.info, "Missing identifier")
end

lang ExtDeclParser = AstParserBase + ExtDeclAst + ExternalKeyword + InKeyword
  sem parseExprROpen state +=
  | { token = KeywordTok { val = "external" } } & tokext ->
    result.bind (parseDecl tokext) (lam decl.
      match decl with (decl, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in

      match cur with { token = KeywordTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing in expression")
    )

  sem parseDecl +=
  | { token = KeywordTok { val = "external" } } & tokext ->
    let cur = nextToken tokext.stream in

    match cur with { token = LIdentTok { val = ident } | HashStringTok { hash = "var", val = ident } } & tokident then
      let cur = nextToken tokident.stream in

      let effectCur = match cur with { token = OperatorTok { val = "!" } } & tokbang then
        (true, nextToken tokbang.stream)
      else
        (false, cur)
      in
      match effectCur with (effect, cur) in

      match cur with { token = OperatorTok { val = ":" } } & tokcol then
        let cur = nextToken tokcol.stream in
        result.bind (parseType cur) (lam res.
          match res with (ty, cur) in
          let decl = DeclExt {
            ident = nameNoSym ident,
            tyIdent = ty,
            effect = effect,
            info = mergeInfo tokext.info (infoTy ty)
          } in
          parseOk (decl, cur)
        )
      else
        parseErr (cur.info, "Missing colon")
    else
      parseErr (cur.info, "Missing identifier")
end

lang UseParser = AstParserBase + UseDeclAst + TyUseAst + UseKeyword + InKeyword
  sem parseExprROpen state +=
  | { token = KeywordTok { val = "use" } } & tokuse ->
    result.bind (parseDecl tokuse) (lam decl.
      match decl with (decl, cur) in

      let state = breakableAddPrefix (configExpr ()) (OpExprDecl decl) state in

      match cur with { token = KeywordTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        parseExprROpen state cur
      else
        parseErr (cur.info, "Missing in expression")
    )

  sem parseDecl +=
  | { token = KeywordTok { val = "use" } } & tokuse ->
    let cur = nextToken tokuse.stream in

    -- A `use`d language name is a generic identifier in boot's grammar
    -- (either case), not specifically a constructor-style UIdent.
    match cur with
      { token = UIdentTok { val = ident } | LIdentTok { val = ident }
              | HashStringTok { hash = "con" | "var", val = ident } } & tokident
    then
      let decl = DeclUse {
        ident = nameNoSym ident,
        info = mergeInfo tokuse.info tokident.info
      } in
      parseOk (decl, nextToken tokident.stream)
    else
      parseErr (cur.info, "Missing identifier")

  sem parseTypeROpen state +=
  | { token = KeywordTok { val = "use" } } & tokuse ->
    let cur = nextToken tokuse.stream in
    match cur with
      { token = UIdentTok { val = ident } | LIdentTok { val = ident }
              | HashStringTok { hash = "con" | "var", val = ident } } & tokident
    then
      let cur = nextToken tokident.stream in
      match cur with { token = KeywordTok { val = "in" } } & tokin then
        let cur = nextToken tokin.stream in
        result.bind (parseType cur) (lam res.
          match res with (inty, cur) in
          let typ = TyUse {
            ident = nameNoSym ident,
            info = mergeInfo tokuse.info (infoTy inty),
            inty = inty
          } in
          let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
          parseTypeRClosed state cur
        )
      else
        parseErr (cur.info, "Missing in")
    else
      parseErr (cur.info, "Missing identifier")
end

lang ProjParser = AstParserBase + MatchAst + NeverAst + RecordPat + NamedPat + VarAst
  syn BrkOpExpr lstyle rstyle +=
  | OpExprProj (Info, String)

  sem getInfoExpr +=
  | OpExprProj (info, _) -> info

  sem parseExprRClosed state +=
  | { token = OperatorTok { val = "." } } & tokdot ->
    let cur = nextToken tokdot.stream in
    switch cur
      case { token = IntTok { val = n } } & toklabel then
        let op = OpExprProj (mergeInfo tokdot.info toklabel.info, int2string n) in
        match breakableAddPostfix (configExpr ()) op state with Some state then
          parseExprRClosed state (nextToken toklabel.stream)
        else
          parseErr (toklabel.info, "Breakable add postfix error")
      case { token = LIdentTok { val = label } | HashStringTok { hash = "label", val = label } } & toklabel then
        let op = OpExprProj (mergeInfo tokdot.info toklabel.info, label) in
        match breakableAddPostfix (configExpr ()) op state with Some state then
          parseExprRClosed state (nextToken toklabel.stream)
        else
          parseErr (toklabel.info, "Breakable add postfix error")
      case _ then
        parseErr (cur.info, "Expected a field label")
    end

  sem constructPostfixExpr +=
  | (OpExprProj (info, label), target) ->
    let fullInfo = mergeInfo (infoTm target) info in
    let tmpIdent = nameNoSym "t" in
    parseOk (TmMatch {
      target = target,
      pat = PatRecord {
        bindings = mapInsert (stringToSid label)
          (PatNamed { ident = PName tmpIdent, ty = tyunknown_, info = NoInfo () })
          (mapEmpty cmpSID),
        ty = tyunknown_,
        info = NoInfo ()
      },
      thn = TmVar { ident = tmpIdent, ty = tyunknown_, info = NoInfo (), frozen = false },
      els = TmNever { ty = tyunknown_, info = NoInfo () },
      ty = ityunknown_ fullInfo,
      info = fullInfo
    })
end

lang IfParser = AstParserBase + MatchAst + BoolPat + IfKeyword + ThenKeyword + ElseKeyword
  syn BrkOpExpr lstyle rstyle +=
  | OpExprIf (Info, Expr, Expr)

  sem getInfoExpr +=
  | OpExprIf (info, _, _) -> info

  sem parseExprROpen state +=
  | { token = KeywordTok { val = "if" } } & tokif ->
    let cur = nextToken tokif.stream in
    let cond = parseExpr cur in
    result.bind cond (lam cond.
      match cond with (cond, cur) in
      match cur with { token = KeywordTok { val = "then" } } & tokthen then
        let cur = nextToken tokthen.stream in
        let thn = parseExpr cur in
        result.bind thn (lam thn.
          match thn with (thn, cur) in
          match cur with { token = KeywordTok { val = "else" } } & tokelse then
            let cur = nextToken tokelse.stream in
            let info = mergeInfo tokif.info tokelse.info in
            let state = breakableAddPrefix (configExpr ()) (OpExprIf (info, cond, thn)) state in
            parseExprROpen state cur
          else
            parseErr (cur.info, "Expected else keyword")
        )
      else
        parseErr (cur.info, "Expected then keyword")
    )

  sem constructPrefixExpr +=
  | (OpExprIf (info, cond, thn), els) ->
    let info = mergeInfo info (infoTm els) in
    parseOk (TmMatch {
      target = cond,
      pat = PatBool { val = true, ty = tybool_, info = NoInfo () },
      thn = thn,
      els = els,
      ty = ityunknown_ info,
      info = info
    })
end

lang SemicolonParser = AstParserBase + LetDeclAst
  syn BrkOpExpr lstyle rstyle +=
  | OpExprSemi Info

  sem getInfoExpr +=
  | OpExprSemi info -> info

  sem parseExprRClosed state +=
  | { token = SemiTok {} } & toksemi ->
    match breakableAddInfix (configExpr ()) (OpExprSemi toksemi.info) state with Some state then
      parseExprROpen state (nextToken toksemi.stream)
    else
      parseErr (toksemi.info, "Breakable add infix error")

  sem constructInfixExpr +=
  | (OpExprSemi info, lhs, rhs) ->
    let info = mergeInfo (infoTm lhs) (infoTm rhs) in
    parseOk (TmDecl {
      decl = DeclLet {
        ident = nameNoSym "",
        tyAnnot = ityunknown_ info,
        tyBody = ityunknown_ info,
        body = lhs,
        info = info
      },
      inexpr = rhs,
      ty = ityunknown_ info,
      info = info
    })

  sem groupingsAllowedExpr +=
  | (OpExprSemi _, OpExprSemi _) -> GRight ()
end

lang KindParser = AstParserBase + DataKindAst
  sem parseKind +=
  | { token = LBraceTok {} } & tokopen ->
    parseKindBody (mapEmpty nameCmp) (nextToken tokopen.stream)

  sem parseKindBody: all w. Map Name {lower : Set Name, upper : Option (Set Name)} -> NextTokenResult -> ParseResult w (Kind, NextTokenResult)
  sem parseKindBody entries =
  | { token = RBraceTok {} } & tokclose ->
    parseOk (Data { types = entries }, nextToken tokclose.stream)
  | cur ->
    result.bind (parseKindEntry cur) (lam res.
      match res with (name, entry, cur) in
      let entries = mapInsert name entry entries in
      match cur with { token = CommaTok {} } & tokcomma then
        parseKindBody entries (nextToken tokcomma.stream)
      else match cur with { token = RBraceTok {} } & tokclose then
        parseOk (Data { types = entries }, nextToken tokclose.stream)
      else
        parseErr (cur.info, "Missing comma or right brace in kind")
    )

  sem parseKindEntry: all w. NextTokenResult -> ParseResult w (Name, {lower : Set Name, upper : Option (Set Name)}, NextTokenResult)
  sem parseKindEntry =
  | { token = UIdentTok { val = val } } & tokident ->
    let name = nameNoSym val in
    let cur = nextToken tokident.stream in
    match cur with { token = LBracketTok {} } & tokopen then
      let cur = nextToken tokopen.stream in
      switch cur
      case { token = OperatorTok { val = ">" } } & tokop then
        match parseKindConList [] (nextToken tokop.stream) with (lower, cur) in
        finishKindEntry name {lower = setOfSeq nameCmp lower, upper = None ()} cur
      case { token = OperatorTok { val = "|" } } & tokop then
        match parseKindConList [] (nextToken tokop.stream) with (lower, cur) in
        finishKindEntry name {lower = setOfSeq nameCmp lower, upper = Some (setEmpty nameCmp)} cur
      case { token = OperatorTok { val = "<" } } & tokop then
        match parseKindConList [] (nextToken tokop.stream) with (upper, cur) in
        switch cur
        case { token = OperatorTok { val = "|" } } & tokbar then
          match parseKindConList [] (nextToken tokbar.stream) with (lower, cur) in
          finishKindEntry name {lower = setOfSeq nameCmp lower, upper = Some (setOfSeq nameCmp upper)} cur
        case cur then
          finishKindEntry name {lower = setEmpty nameCmp, upper = Some (setOfSeq nameCmp upper)} cur
        end
      case cur then
        parseErr (cur.info, "Expected >, <, or | in kind entry")
      end
    else parseErr (cur.info, "Missing left bracket in kind entry")
  | cur -> parseErr (cur.info, "Missing type identifier in kind entry")

  sem finishKindEntry: all w. Name -> {lower : Set Name, upper : Option (Set Name)} -> NextTokenResult -> ParseResult w (Name, {lower : Set Name, upper : Option (Set Name)}, NextTokenResult)
  sem finishKindEntry name entry =
  | { token = RBracketTok {} } & tokclose -> parseOk (name, entry, nextToken tokclose.stream)
  | cur -> parseErr (cur.info, "Missing right bracket in kind entry")

  sem parseKindConList: [Name] -> NextTokenResult -> ([Name], NextTokenResult)
  sem parseKindConList acc =
  | { token = UIdentTok { val = val } } & tok -> parseKindConList (snoc acc (nameNoSym val)) (nextToken tok.stream)
  | { token = LIdentTok { val = val } } & tok -> parseKindConList (snoc acc (nameNoSym val)) (nextToken tok.stream)
  | cur -> (acc, cur)
end

lang AllParser = AstParserBase + AllTypeAst + PolyKindAst + AllKeyword + KindParser
  sem parseTypeROpen state +=
  | { token = KeywordTok { val = "all" } } & tokall ->
    let cur = nextToken tokall.stream in

    match cur with { token = LIdentTok { val = ident } | HashStringTok { hash = "var", val = ident } } & tokident then
      let cur = nextToken tokident.stream in
      let ident = nameNoSym ident in

      match cur with { token = OperatorTok { val = "::" } } & tokdcolon then
        let cur = nextToken tokdcolon.stream in
        result.bind (parseKind cur) (lam res.
          match res with (kind, cur) in
          match cur with { token = OperatorTok { val = "." } } & tokdot then
            let cur = nextToken tokdot.stream in
            result.bind (parseType cur) (lam res.
              match res with (ty, cur) in
              let typ = TyAll {
                info = mergeInfo tokall.info (infoTy ty),
                ident = ident,
                kind = kind,
                ty = ty
              } in
              let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
              parseTypeRClosed state cur
            )
          else
            parseErr (cur.info, "Missing period")
        )
      else match cur with { token = OperatorTok { val = "." } } & tokdot then
        let cur = nextToken tokdot.stream in
        result.bind (parseType cur) (lam res.
          match res with (ty, cur) in
          let typ = TyAll {
            info = mergeInfo tokall.info (infoTy ty),
            ident = ident,
            kind = Poly (),
            ty = ty
          } in
          let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
          parseTypeRClosed state cur
        )
      else
        parseErr (cur.info, "Missing period")
    else
      parseErr (cur.info, "Missing identifier")
end

lang SynDeclParser = AstParserBase + SynDeclAst + SynKeyword + RecordTypeAst
  sem parseDecl +=
  | { token = KeywordTok { val = "syn" } } & toksyn ->
    let cur = nextToken toksyn.stream in

    match cur with { token = UIdentTok { val = ident } | HashStringTok { hash = "con", val = ident } } & tokident then
      let cur = nextToken tokident.stream in

      recursive let parseParams = lam acc. lam cur.
        match cur with { token = LIdentTok { val = param } | HashStringTok { hash = "var", val = param } } & tokparam then
          parseParams (snoc acc (nameNoSym param)) (nextToken tokparam.stream)
        else
          (acc, cur)
      in
      match parseParams [] cur with (params, cur) in

      let opInfoFallback = cur.info in
      match matchAssignOp cur with Some (isSum, cur) then
        recursive let parseConstrs = lam acc. lam cur.
          match cur with { token = OperatorTok { val = "|" } } & tokbar then
            let cur = nextToken tokbar.stream in
            match cur with { token = UIdentTok { val = conIdent } | HashStringTok { hash = "con", val = conIdent } } & tokcon then
              let cur = nextToken tokcon.stream in
              let tyRes =
                if startsAtomType cur then
                  result.map (lam r. match r with (ty, cur) in (ty, infoTy ty, cur)) (parseType cur)
                else
                  parseOk (TyRecord { fields = mapEmpty cmpSID, info = NoInfo () }, tokcon.info, cur)
              in
              result.bind tyRes (lam res.
                match res with (ty, tyEndInfo, cur) in
                let constr = {ident = nameNoSym conIdent, tyIdent = ty, info = mergeInfo tokbar.info tyEndInfo} in
                parseConstrs (snoc acc constr) cur
              )
            else
              parseErr (cur.info, "Missing constructor identifier")
          else
            parseOk (acc, cur)
        in

        result.bind (parseConstrs [] cur) (lam res.
          match res with (constrs, cur) in
          let kind = if isSum then SynSum { base = nameNoSym ident } else SynBase () in
          let endInfo = match constrs with _ ++ [lastConstr] then lastConstr.info else opInfoFallback in
          let decl = DeclSyn {
            ident = nameNoSym ident,
            params = params,
            defs = constrs,
            info = mergeInfo toksyn.info endInfo,
            kind = kind
          } in
          parseOk (decl, cur)
        )
      else
        parseErr (cur.info, "Expected = or +=")
    else
      parseErr (cur.info, "Missing identifier")
end

lang SemDeclParser = AstParserBase + SemDeclAst + SemKeyword
  sem parseDecl +=
  | { token = KeywordTok { val = "sem" } } & toksem ->
    let cur = nextToken toksem.stream in

    match cur with { token = LIdentTok { val = ident } | HashStringTok { hash = "var", val = ident } } & tokident then
      let cur = nextToken tokident.stream in

      match cur with { token = OperatorTok { val = ":" } } & tokcol then
        let cur = nextToken tokcol.stream in
        result.bind (parseType cur) (lam res.
          match res with (ty, cur) in
          let decl = DeclSem {
            ident = nameNoSym ident,
            tyAnnot = ty,
            tyBody = ityunknown_ (infoTy ty),
            impl = None (),
            info = mergeInfo toksem.info (infoTy ty),
            kind = SemBase ()
          } in
          parseOk (decl, cur)
        )
      else
        recursive let parseParams = lam acc. lam cur.
          switch cur
            case { token = LParenTok {} } & toklp then
              let cur = nextToken toklp.stream in
              match cur with { token = LIdentTok { val = pident } | HashStringTok { hash = "var", val = pident } } & tokpident then
                let cur = nextToken tokpident.stream in
                match cur with { token = OperatorTok { val = ":" } } & tokpcol then
                  let cur = nextToken tokpcol.stream in
                  result.bind (parseType cur) (lam res.
                    match res with (ty, cur) in
                    match cur with { token = RParenTok {} } & tokrp then
                      let param =
                        { ident = nameNoSym pident
                        , tyAnnot = ty
                        , tyParam = ityunknown_ (infoTy ty)
                        , info = mergeInfo toklp.info tokrp.info
                        } in
                      parseParams (snoc acc param) (nextToken tokrp.stream)
                    else
                      parseErr (cur.info, "Missing closing parenthesis")
                  )
                else
                  parseErr (cur.info, "Missing colon")
              else
                parseErr (cur.info, "Missing identifier")
            case { token = LIdentTok { val = pident } | HashStringTok { hash = "var", val = pident } } & tokpident then
              let info = tokpident.info in
              let param = {ident = nameNoSym pident, tyAnnot = ityunknown_ info, tyParam = ityunknown_ info, info = info} in
              parseParams (snoc acc param) (nextToken tokpident.stream)
            case _ then
              parseOk (acc, cur)
          end
        in

        result.bind (parseParams [] cur) (lam res.
          match res with (params, cur) in
          let opInfoFallback = cur.info in
          match matchAssignOp cur with Some (isSum, cur) then
            recursive let parseCases = lam acc. lam cur.
              match cur with { token = OperatorTok { val = "|" } } & tokbar then
                let cur = nextToken tokbar.stream in
                result.bind (parsePat cur) (lam pres.
                  match pres with (pat, cur) in
                  match cur with { token = OperatorTok { val = "->" } } & tokarrow then
                    let cur = nextToken tokarrow.stream in
                    result.bind (parseExpr cur) (lam eres.
                      match eres with (body, cur) in
                      let c = {pat = pat, body = body, info = mergeInfo tokbar.info (infoTm body)} in
                      parseCases (snoc acc c) cur
                    )
                  else
                    parseErr (cur.info, "Expected ->")
                )
              else
                parseOk (acc, cur)
            in

            result.bind (parseCases [] cur) (lam res.
              match res with (cases, cur) in
              let kind = if isSum then SemSum { base = nameNoSym ident } else SemBase () in
              let endInfo = match cases with _ ++ [lastCase] then lastCase.info else opInfoFallback in
              let info = mergeInfo toksem.info endInfo in
              let decl = DeclSem {
                ident = nameNoSym ident,
                tyAnnot = ityunknown_ info,
                tyBody = ityunknown_ info,
                impl = Some { params = params, cases = cases },
                info = info,
                kind = kind
              } in
              parseOk (decl, cur)
            )
          else
            parseErr (cur.info, "Expected = or +=")
        )
    else
      parseErr (cur.info, "Missing identifier")
end

lang LangDeclParser = AstParserBase + LangDeclAst + LangKeyword + EndKeyword + SynDeclParser + SemDeclParser + TypeDeclParser
  sem parseDecl +=
  | { token = KeywordTok { val = "lang" } } & toklang ->
    let cur = nextToken toklang.stream in

    -- A `lang` name is a generic identifier in boot's grammar (either
    -- case), not specifically a constructor-style UIdent.
    match cur with
      { token = UIdentTok { val = ident } | LIdentTok { val = ident }
              | HashStringTok { hash = "con" | "var", val = ident } } & tokident
    then
      let cur = nextToken tokident.stream in

      recursive let parseIncludes = lam acc. lam cur.
        match cur with
          { token = UIdentTok { val = incIdent } | LIdentTok { val = incIdent }
                  | HashStringTok { hash = "con" | "var", val = incIdent } } & tokinc
        then
          let acc = snoc acc (nameNoSym incIdent, tokinc.info) in
          let cur = nextToken tokinc.stream in
          match cur with { token = OperatorTok { val = "+" } } & tokplus then
            parseIncludes acc (nextToken tokplus.stream)
          else
            parseOk (acc, cur)
        else
          parseErr (cur.info, "Missing language identifier")
      in

      let includesRes = match cur with { token = OperatorTok { val = "=" } } & tokeq then
        parseIncludes [] (nextToken tokeq.stream)
      else
        parseOk ([], cur)
      in

      result.bind includesRes (lam res.
        match res with (includes, cur) in

        recursive let parseBodyDecls = lam acc. lam cur.
          match cur with { token = KeywordTok { val = "end" } } & tokend then
            parseOk (acc, tokend, nextToken tokend.stream)
          else
            result.bind (parseDecl cur) (lam res.
              match res with (decl, cur) in
              parseBodyDecls (snoc acc decl) cur
            )
        in

        result.bind (parseBodyDecls [] cur) (lam res.
          match res with (decls, tokend, cur) in
          let decl = DeclLang {
            ident = nameNoSym ident,
            includes = includes,
            decls = decls,
            info = mergeInfo toklang.info tokend.info
          } in
          parseOk (decl, cur)
        )
      )
    else
      parseErr (cur.info, "Missing identifier")
end

lang IncludeDeclParser = AstParserBase + IncludeDeclAst + IncludeKeyword
  sem parseDecl +=
  | { token = KeywordTok { val = "include" } } & tokinc ->
    let cur = nextToken tokinc.stream in
    match cur with { token = StringTok { val = path } } & tokpath then
      let decl = DeclInclude {
        path = path,
        info = mergeInfo tokinc.info tokpath.info
      } in
      parseOk (decl, nextToken tokpath.stream)
    else
      parseErr (cur.info, "Missing include path")
end

-- The entry point for parsing an entire mcore file: zero or more
-- `include` statements, zero or more top-level declarations, and an
-- optional `mexpr <expr>` section.
lang ProgramParser = AstParserBase + MLangTopLevel + RecordAst + IncludeDeclParser + MexprKeyword
  sem parseProgram: all w. NextTokenResult -> ParseResult w (MLangProgram, NextTokenResult)

  sem parseProgram =
  | cur ->
    recursive let parseIncludes = lam acc. lam cur.
      match cur with { token = KeywordTok { val = "include" } } then
        result.bind (parseDecl cur) (lam res.
          match res with (decl, cur) in
          parseIncludes (snoc acc decl) cur
        )
      else
        parseOk (acc, cur)
    in

    result.bind (parseIncludes [] cur) (lam res.
      match res with (includes, cur) in

      recursive let parseTops = lam acc. lam cur.
        switch cur
          case { token = KeywordTok { val = "mexpr" } } then parseOk (acc, cur)
          case { token = EOFTok {} } then parseOk (acc, cur)
          case _ then
            result.bind (parseDecl cur) (lam res.
              match res with (decl, cur) in
              parseTops (snoc acc decl) cur
            )
        end
      in

      result.bind (parseTops [] cur) (lam res.
        match res with (tops, cur) in

        let exprRes = match cur with { token = KeywordTok { val = "mexpr" } } & tokmexpr then
          parseExpr (nextToken tokmexpr.stream)
        else
          parseOk (TmRecord { bindings = mapEmpty cmpSID, ty = ityunknown_ cur.info, info = cur.info }, cur)
        in

        result.bind exprRes (lam res.
          match res with (expr, cur) in
          match cur with { token = EOFTok {} } then
            parseOk ({decls = concat includes tops, expr = expr}, cur)
          else
            parseErr (cur.info, "Unexpected token, expected end of file")
        )
      )
    )
end

-- TODO: Better solution
lang PrecedenceParser = AppParser + DataParser + LamParser + LetDeclParser + AndParser + OrParser + NotParser + IfParser + SemicolonParser + MatchParser + ProjParser + SeqParser
  sem groupingsAllowedExpr +=
  | (OpExprDecl _, OpExprApp _) -> GRight ()
  | (OpExprLam _, OpExprApp _) -> GRight ()
  | (OpExprConApp _, OpExprApp _) -> GLeft ()
  | (OpExprDecl _, OpExprSemi _) -> GRight ()
  | (OpExprLam _, OpExprSemi _) -> GRight ()
  | (OpExprIf _, OpExprSemi _) -> GRight ()
  | (OpExprApp _, OpExprSemi _) -> GLeft ()
  | (OpExprConApp _, OpExprSemi _) -> GLeft ()
  | (OpExprSemi _, OpExprApp _) -> GRight ()
  | (OpExprSemi _, OpExprConApp _) -> GRight ()
  | (OpExprIf _, OpExprApp _) -> GRight ()
  | (OpExprMatchIn _, OpExprApp _) -> GRight ()
  | (OpExprMatchElse _, OpExprApp _) -> GRight ()
  | (OpExprMatchIn _, OpExprSemi _) -> GRight ()
  | (OpExprMatchElse _, OpExprSemi _) -> GRight ()
  | (OpExprApp _, OpExprProj _) -> GRight ()
  | (OpExprProj _, OpExprApp _) -> GLeft ()
  | (OpExprLam _, OpExprProj _) -> GRight ()
  | (OpExprDecl _, OpExprProj _) -> GRight ()
  | (OpExprIf _, OpExprProj _) -> GRight ()
  | (OpExprMatchIn _, OpExprProj _) -> GRight ()
  | (OpExprMatchElse _, OpExprProj _) -> GRight ()
  | (OpExprSemi _, OpExprProj _) -> GRight ()
  | (OpExprProj _, OpExprSemi _) -> GLeft ()
  | (OpExprConApp _, OpExprProj _) -> GRight ()
  | (OpExprProj _, OpExprConApp _) -> GLeft ()

  sem groupingsAllowedType +=
  | (OpTypeApp _, OpTypeArrow _) -> GLeft ()
  | (OpTypeArrow _, OpTypeApp _) -> GRight ()

  sem groupingsAllowedPat +=
  | (OpPatAnd _, OpPatOr _) -> GLeft ()
  | (OpPatAnd _, OpPatNot _) -> GRight ()
  | (OpPatOr _, OpPatAnd _) -> GRight ()
  | (OpPatOr _, OpPatNot _) -> GRight ()
  | (OpPatNot _, OpPatAnd _) -> GLeft ()
  | (OpPatNot _, OpPatOr _) -> GLeft ()
  | (OpPatSeqEdge _, OpPatOr _) -> GLeft ()
  | (OpPatOr _, OpPatSeqEdge _) -> GRight ()
  | (OpPatAnd _, OpPatSeqEdge _) -> GRight ()
  | (OpPatSeqEdge _, OpPatAnd _) -> GLeft ()
  | (OpPatConApp _, OpPatAnd _) -> GLeft ()
  | (OpPatConApp _, OpPatOr _) -> GLeft ()
end

lang UnexpectedTokenParser = AstParserBase
  sem parseExprROpen state +=
  | cur ->
    let str = concat "Unexpexted token while parsing expr: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parseDecl +=
  | cur ->
    let str = concat "Unexpexted token while parsing decl: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parseTypeROpen state +=
  | cur ->
    let str = concat "Unexpexted token while parsing type: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parseKind +=
  | cur ->
    let str = concat "Unexpexted token while parsing kind: " (tokToStr cur.token) in
    parseErr (cur.info, str)

  sem parsePatROpen state +=
  | cur ->
    let str = concat "Unexpexted token while parsing pat: " (tokToStr cur.token) in
    parseErr (cur.info, str)
end

lang MExprParser =
    IntParser
  + FloatParser
  + BoolParser
  + CharParser
  + StringParser
  + TensorParser
  + UnknownTypeParser
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
  + TypeDeclParser
  + ConDeclParser
  + ExtDeclParser
  + LamParser
  + MatchParser
  + SwitchParser
  + IfParser
  + SemicolonParser
  + NeverParser
  + AndParser
  + OrParser
  + NotParser
  + UtestParser
  + AllParser
  + ProjParser
  + PrecedenceParser
  + UnexpectedTokenParser
end

lang MLangParser =
    MExprParser
  + UseParser
  + SynDeclParser
  + SemDeclParser
  + LangDeclParser
  + IncludeDeclParser
  + ProgramParser
end

lang TestParser =
    MLangParser
  + MExprPrettyPrint
  + MLangPrettyPrint
  + MLangEq
  + MExprToJson
end

type TestResult
con OkSame: () -> TestResult        -- Same result
con OkSameExInfo: () -> TestResult  -- Same result excluding info field
con OkFail: () -> TestResult        -- Both fails
con Fail: () -> TestResult          -- Result is different

mexpr

use TestParser in
use BootParserMLang in

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

let parseProg = lam str. result.map (lam a. a.0) (parseProgram (lex str)) in
let parseBootProg = lam str. parseMLangString str in


let compareProg = lam str.
  let a = parseProg str in
  let b = parseBootProg str in
  switch (result.toOption a, result.toOption b)
    case (Some a, Some b) then
      if eqProgram a b then OkSameExInfo () else Fail ()
    case (None (), None ()) then
      OkFail ()
    case _ then
      Fail ()
  end in

let printProgBoot = lam str.
  switch result.consume (parseBootProg str)
  case (w, Left e) then
    printLn "Parse error:";
    iter (lam e. match e with (info, msg) in printLn (infoErrorString info msg)) e
  case (w, Right prog) then
    printLn (mlang2str prog)
  end
in

let printProg = lam str.
  switch result.consume (parseProg str)
  case (w, Left e) then
    printLn "Parse error:";
    iter (lam e. match e str with (info, msg) in printLn (infoErrorString info msg)) e
  case (w, Right prog) then
    printLn (mlang2str prog)
  end
in



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

utest compare "\"test\"" with OkSameExInfo () in

utest compare "addi 1 2" with OkSame () in
utest compare "addi 1 2 3" with OkSame () in
utest compare "addi addi 1 2 3" with OkSame () in
utest compare "addi (addi 1 2) 3" with OkSameExInfo () in
utest compare "addi 1 (addi 2 3)" with OkSameExInfo () in

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

utest compare "let a: Tensor[Int] = x in a" with OkSameExInfo () in
utest compare "let a: Tensor [Int] = x in a" with OkSameExInfo () in
utest compare "let a: Tensor[Tensor[Int]] = x in a" with OkSameExInfo () in

utest compare "f {a with x = 1}" with OkSame () in
utest compare "f {a with x = 1, y = 2}" with OkSame () in
utest compare "f {{a with x = 1} with y = 2}" with OkSame () in
utest compare "f (a.x)" with OkSameExInfo () in
utest compare "f (a.0)" with OkSameExInfo () in

utest compare "type T a b in x" with OkSameExInfo () in

utest compare "let a: Unknown = x in a" with OkSameExInfo () in
utest compare "let a: Unknown -> Int = x in a" with OkSameExInfo () in

utest compare "let a: Int Int = 1 1 in a" with OkSameExInfo () in

utest compare "let a: Int -> Int = addi 1 in a" with OkSameExInfo () in
utest compare "let a: Int Int -> Int = addi in a" with OkSameExInfo () in
utest compare "let a: Int -> Int -> Int = f in a" with OkSameExInfo () in

utest compare "let a: Foo = x in a" with OkSameExInfo () in
utest compare "let a: Foo -> Int = x in a" with OkSameExInfo () in
utest compare "let a: Map SID Expr = x in a" with OkSameExInfo () in

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

utest compare "{negi 1 with b = 2}" with OkSame () in
utest compare "{negi 1 with b = 2, c = 3}" with OkSame () in
utest compare "{{negi 1 with b = 2} with c = 3}" with OkSame () in
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

utest compare "match a with 1 then b else c" with OkSame () in

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

utest compare "x.0" with OkSameExInfo () in
utest compare "x.field" with OkSameExInfo () in
utest compare "(x.0).1" with OkSameExInfo () in
utest compare "snoc acc.0 content" with OkSameExInfo () in
utest compare "f (g a).0 b" with OkSameExInfo () in
utest compare "lam x. x.0" with OkSameExInfo () in

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

utest compare "match a with 1 & 2 & 3 in b" with OkSameExInfo () in
utest compare "match a with 1 | 2 | 3 in b" with OkSameExInfo () in
utest compare "match a with \"/\" ++ _ | \"./\" ++ _ | \"../\" ++ _ in b" with OkSameExInfo () in
utest compare "match a with c & ([1] ++ rest) in b" with OkSameExInfo () in

utest compare "utest a with 1 in x" with OkSameExInfo () in
utest compare "utest a with 1" with OkFail () in
utest compare "utest a with" with OkFail () in
utest compare "utest a " with OkFail () in
utest compare "utest" with OkFail () in
utest compare "utest with" with OkFail () in
utest compare "utest a with 1 using b in x" with OkSameExInfo () in
utest compare "utest a with 1 using in x" with OkFail () in
utest compare "utest a with 1 using eq else b in x" with OkSameExInfo () in
utest compare "utest a with 1 else" with OkFail () in

utest compare "switch a end" with OkSameExInfo () in
utest compare "switch a case 1 then b case 2 then c end" with OkSameExInfo () in
utest compare "switch a case 1 then switch b case 2 then x end end" with OkSameExInfo () in
utest compare "switch" with OkFail () in
utest compare "switch a" with OkFail () in
utest compare "switch end" with OkFail () in
utest compare "switch a case" with OkFail () in
utest compare "switch a case 1" with OkFail () in
utest compare "switch a case end" with OkFail () in
utest compare "switch a case 1 end" with OkFail () in
utest compare "switch a case 1 then" with OkFail () in
utest compare "switch a case 1 then end" with OkFail () in

utest compare "f (if true then 1 else 2) 3" with OkSameExInfo () in
utest compare "(match a with 1 then b else c) d" with OkSameExInfo () in

utest compare "type T in x" with OkSameExInfo () in
utest compare "type T a in x" with OkSameExInfo () in
utest compare "type T a b in x" with OkSameExInfo () in
utest compare "type T = Int in x" with OkSameExInfo () in
utest compare "type T = Int Int in x" with OkSameExInfo () in
utest compare "type T a b = Int Int in x" with OkSameExInfo () in
utest compare "type in x" with OkFail () in
utest compare "type T = in x" with OkFail () in

utest compare "con Foo: Int in x" with OkSameExInfo () in
utest compare "con Foo: Int -> Int in x" with OkSameExInfo () in
utest compare "con Foo: Int in Foo 1" with OkSameExInfo () in
utest compare "con Foo in x" with OkSameExInfo () in
utest compare "con in x" with OkFail () in
utest compare "con Foo: in x" with OkFail () in
utest compare "con Foo: Int" with OkFail () in

utest compare "external foo: Int in foo" with OkSameExInfo () in
utest compare "external foo ! : Int in foo" with OkSameExInfo () in
utest compare "external foo: Int -> Int in foo 1" with OkSameExInfo () in
utest compare "external in x" with OkFail () in
utest compare "external foo in x" with OkFail () in
utest compare "external foo: in x" with OkFail () in
utest compare "external foo: Int" with OkFail () in

utest compare "use Foo in x" with OkSameExInfo () in
utest compare "use foo in x" with OkSameExInfo () in
utest compare "use in x" with OkFail () in
utest compare "use Foo" with OkFail () in

utest compare "if true then 1 else 2" with OkSameExInfo () in
utest compare "if true then 1 else if false then 2 else 3" with OkSameExInfo () in
utest compare "if true then addi 1 2 else 3" with OkSameExInfo () in
utest compare "if" with OkFail () in
utest compare "if true" with OkFail () in
utest compare "if true then 1" with OkFail () in
utest compare "if true then 1 else" with OkFail () in

utest compare "1; 2" with OkSameExInfo () in
utest compare "1; 2; 3" with OkSameExInfo () in
utest compare "let a = 1 in a; 2" with OkSameExInfo () in

utest compare "let a: all x. x -> x = lam y. y in a" with OkSameExInfo () in
utest compare "let a: all x. Int = 1 in a" with OkSameExInfo () in
utest compare "let a: all x. all y. x -> y -> x = lam a. lam b. a in a" with OkSameExInfo () in

utest compare "f a; g b; c" with OkSameExInfo () in
utest compare "(f a; g b); c" with OkSameExInfo () in
utest compare "if true then 1 else a; 2" with OkSameExInfo () in
utest compare "match a with 1 in b; 2" with OkSameExInfo () in



utest compareProg "lang Foo\n  syn Expr =\n  | CInt Int\n  sem eval =\n  | CInt n -> n\nend\nmexpr\n1" with OkSameExInfo () in

utest compareProg "lang Foo = Bar + Baz\nend\nmexpr\n1" with OkSameExInfo () in

utest compareProg (strJoin "\n" [
  "lang Bar",
  "  syn Expr =",
  "  | CInt Int",
  "end",
  "lang Baz",
  "  syn Expr =",
  "  | CBool Bool",
  "end",
  "lang Foo = Bar + Baz",
  "  syn Expr +=",
  "  | CUnit ()",
  "  sem eval: Expr -> Int",
  "end",
  "mexpr",
  "1"
]) with OkSameExInfo () in

utest compareProg (strJoin "\n" [
  "lang Foo",
  "  sem f (x: Int) (y: Int) =",
  "  | 1 -> addi x y",
  "  | n -> n",
  "end",
  "mexpr",
  "1"
]) with OkSameExInfo () in

utest compareProg (strJoin "\n" [
  "include \"foo.mc\"",
  "include \"bar.mc\"",
  "let x = 1",
  "type T = Int",
  "con C: Int",
  "external ext: Int",
  "recursive",
  "  let f = lam x. x",
  "  let g = lam x. x",
  "end",
  "utest 1 with 1",
  "mexpr",
  "x"
]) with OkSameExInfo () in

utest compareProg "mexpr\n1" with OkSameExInfo () in
utest compareProg "1" with OkFail () in
utest compareProg "let x = 1\nmexpr\nx" with OkSameExInfo () in
utest compareProg "lang" with OkFail () in
utest compareProg "lang Foo" with OkFail () in
utest compareProg "lang Foo =\nend\nmexpr\n1" with OkFail () in
utest compareProg "lang Foo\n  syn Expr\nend\nmexpr\n1" with OkFail () in

utest compareProg "lang Foo\nend\nlet a: use Foo in Int = 1\nmexpr\na" with OkSameExInfo () in

utest compareProg (strJoin "\n" [
  "lang Foo",
  "  sem f =| 1 -> 2",
  "  sem g x =| 1 -> x",
  "end",
  "mexpr",
  "1"
]) with OkSameExInfo () in

utest compareProg (strJoin "\n" [
  "lang Bar",
  "  syn X =",
  "  | C1 Int",
  "end",
  "lang Foo = Bar",
  "  syn X +=| C2 Int",
  "end",
  "mexpr",
  "1"
]) with OkSameExInfo () in

utest compareProg "lang _foo\nend\nmexpr\n1" with OkSameExInfo () in
utest compareProg "lang _foo\nend\nlang _bar = _foo\nend\nmexpr\n1" with OkSameExInfo () in

()
