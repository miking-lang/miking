/-

This is the new parser for MCore.

The parser is designed to be as extensible as possible.
It is built on top of the breakable library.

-/

include "basic-types.mc"
include "bool.mc"
include "common.mc"
include "lexer.mc"
include "mexpr/info.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "mexpr/ast-builder.mc"
include "mexpr/json-debug.mc"
include "mexpr/pprint.mc"
include "mlang/ast.mc"
include "mlang/cmp.mc"
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

type ParseRes w a = Result w (String -> (Info, String)) a

let parseOk:  all w. all a. a              -> ParseRes w a = lam a. result.ok a
let parseErr: all w. all a. (Info, String) -> ParseRes w a = lam e. result.err (lam src. e)
let parseErrs: all w. all a. [String -> (Info, String)] -> ParseRes w a = lam errs.
  foldl1 result.withAnnotations (map result.err errs)

lang AstParserBase = Lexer + Ast + DeclAst
  syn BrkOpExpr lstyle rstyle =
  | OpExprAtom Expr
  | OpExprDecl Decl

  syn BrkOpType lstyle rstyle =
  | OpTypeAtom Type

  syn BrkOpPat lstyle rstyle =
  | OpPatAtom Pat

  syn BrkCatExpr =
  | CatExprPostfix     ()
  | CatExprApplication ()
  | CatExprSequencing  ()
  | CatExprBinder      ()

  syn BrkCatType =
  | CatTypeApplication ()
  | CatTypeArrow       ()

  syn BrkCatPat =
  | CatPatApplication ()
  | CatPatPrefix      ()
  | CatPatLogic       ()

  sem parseExpr: all w. NextTokenResult -> ParseRes w (Expr, NextTokenResult)
  sem parseDecl: all w. NextTokenResult -> ParseRes w (Decl, NextTokenResult)
  sem parseType: all w. NextTokenResult -> ParseRes w (Type, NextTokenResult)
  sem parseKind: all w. NextTokenResult -> ParseRes w (Kind, NextTokenResult)
  sem parsePat:  all w. NextTokenResult -> ParseRes w (Pat,  NextTokenResult)

  sem parseExprRClosed:  all w. State BrkOpExpr RClosed -> NextTokenResult -> ParseRes w (Expr, NextTokenResult)
  sem parseTypeRClosed:  all w. State BrkOpType RClosed -> NextTokenResult -> ParseRes w (Type, NextTokenResult)
  sem parsePatRClosed:   all w. State BrkOpPat  RClosed -> NextTokenResult -> ParseRes w (Pat,  NextTokenResult)

  sem parseExprROpen:    all w. State BrkOpExpr ROpen   -> NextTokenResult -> ParseRes w (Expr, NextTokenResult)
  sem parseTypeROpen:    all w. State BrkOpType ROpen   -> NextTokenResult -> ParseRes w (Type, NextTokenResult)
  sem parsePatROpen:     all w. State BrkOpPat  ROpen   -> NextTokenResult -> ParseRes w (Pat,  NextTokenResult)

  sem finalizeParseExpr: all w. State BrkOpExpr RClosed -> NextTokenResult -> ParseRes w (Expr, NextTokenResult)
  sem finalizeParseType: all w. State BrkOpType RClosed -> NextTokenResult -> ParseRes w (Type, NextTokenResult)
  sem finalizeParsePat:  all w. State BrkOpPat  RClosed -> NextTokenResult -> ParseRes w (Pat,  NextTokenResult)

  sem startsAtomExpr: NextTokenResult -> Bool
  sem startsAtomType: NextTokenResult -> Bool

  sem constructPrefixExpr: all w. (BrkOpExpr LClosed ROpen, Expr) -> ParseRes w Expr
  sem constructPrefixType: all w. (BrkOpType LClosed ROpen, Type) -> ParseRes w Type
  sem constructPrefixPat:  all w. (BrkOpPat  LClosed ROpen, Pat)  -> ParseRes w Pat

  sem constructInfixExpr: all w. (BrkOpExpr LOpen ROpen, Expr, Expr) -> ParseRes w Expr
  sem constructInfixType: all w. (BrkOpType LOpen ROpen, Type, Type) -> ParseRes w Type
  sem constructInfixPat:  all w. (BrkOpPat  LOpen ROpen, Pat,  Pat)  -> ParseRes w Pat

  sem constructPostfixExpr: all w. (BrkOpExpr LOpen RClosed, Expr) -> ParseRes w Expr
  sem constructPostfixType: all w. (BrkOpType LOpen RClosed, Type) -> ParseRes w Type
  sem constructPostfixPat:  all w. (BrkOpPat  LOpen RClosed, Pat)  -> ParseRes w Pat

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

  sem opCatExpr: all lstyle. all rstyle. BrkOpExpr lstyle rstyle -> BrkCatExpr
  sem opCatType: all lstyle. all rstyle. BrkOpType lstyle rstyle -> BrkCatType
  sem opCatPat:  all lstyle. all rstyle. BrkOpPat  lstyle rstyle -> BrkCatPat

  sem categoryGroupingExpr: (BrkCatExpr, BrkCatExpr) -> AllowedDirection
  sem categoryGroupingType: (BrkCatType, BrkCatType) -> AllowedDirection
  sem categoryGroupingPat:  (BrkCatPat,  BrkCatPat)  -> AllowedDirection

  sem categoryGroupingExpr +=
  | (CatExprPostfix _, _) -> GLeft ()
  | (CatExprApplication _, CatExprPostfix _) -> GRight ()
  | (CatExprApplication _, _) -> GLeft ()
  | (CatExprSequencing _, CatExprPostfix _) -> GRight ()
  | (CatExprSequencing _, CatExprApplication _) -> GRight ()
  | (CatExprSequencing _, _) -> GLeft ()
  | (CatExprBinder _, CatExprPostfix _) -> GRight ()
  | (CatExprBinder _, CatExprApplication _) -> GRight ()
  | (CatExprBinder _, CatExprSequencing _) -> GRight ()
  | (CatExprBinder _, _) -> GLeft ()
  | _ -> GEither ()

  sem categoryGroupingType +=
  | (CatTypeApplication _, _) -> GLeft ()
  | (CatTypeArrow _, CatTypeApplication _) -> GRight ()
  | (CatTypeArrow _, _) -> GLeft ()
  | _ -> GEither ()

  sem categoryGroupingPat +=
  | (CatPatApplication _, _) -> GLeft ()
  | (CatPatPrefix _, CatPatApplication _) -> GRight ()
  | (CatPatPrefix _, _) -> GLeft ()
  | (CatPatLogic _, CatPatApplication _) -> GRight ()
  | (CatPatLogic _, CatPatPrefix _) -> GRight ()
  | (CatPatLogic _, _) -> GLeft ()
  | _ -> GEither ()

  sem groupingsAllowedExpr +=
  | (p, c) -> categoryGroupingExpr (opCatExpr p, opCatExpr c)

  sem groupingsAllowedType +=
  | (p, c) -> categoryGroupingType (opCatType p, opCatType c)

  sem groupingsAllowedPat +=
  | (p, c) -> categoryGroupingPat (opCatPat p, opCatPat c)

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
      parseErr (cur.info, "Expected an expression")

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
      parseErr (cur.info, "Expected a type")

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
      parseErr (cur.info, "Expected a pattern")

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

  sem terminalInfosExpr +=
  | op -> [getInfoExpr op]

  sem terminalInfosType +=
  | op -> [getInfoType op]

  sem terminalInfosPat +=
  | op -> [getInfoPat op]

  sem opCatExpr +=
  | OpExprDecl _ -> CatExprBinder ()

  sem getInfoExpr +=
  | OpExprAtom expr -> infoTm expr
  | OpExprDecl decl -> infoDecl decl

  sem getInfoType +=
  | OpTypeAtom typ -> infoTy typ

  sem getInfoPat +=
  | OpPatAtom pat -> infoPat pat
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
        parseErr (cur.info, "Expected an integer or float literal after unary '-'")
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
      parseErr (cur.info, "Expected an integer literal after unary '-' in a pattern")
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

  sem opCatExpr +=
  | OpExprApp _ -> CatExprApplication ()

  sem opCatType +=
  | OpTypeApp _ -> CatTypeApplication ()

  sem parseExprRClosed state +=
  | cur ->
    -- check if the next token can be part of the current expression.
    match startsAtomExpr cur with true then
      match breakableAddInfix (configExpr ()) (OpExprApp cur.info) state with Some(state) then
        parseExprROpen state cur
      else
        parseErr (cur.info, "Function application is not allowed here")
    else
      finalizeParseExpr state cur

  sem parseTypeRClosed state +=
  | cur ->
    -- check if the next token can be part of the current type.
    match startsAtomType cur with true then
      match breakableAddInfix (configType ()) (OpTypeApp cur.info) state with Some(state) then
        parseTypeROpen state cur
      else
        parseErr (cur.info, "Type application is not allowed here")
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

  sem opCatExpr +=
  | OpExprConApp _ -> CatExprApplication ()

  sem opCatPat +=
  | OpPatConApp _ -> CatPatApplication ()

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

  sem parseConTypeRestrictionBody: all w. NextTokenResult -> ParseRes w (Type, Info, NextTokenResult)
  sem parseConTypeRestrictionBody =
  | { token = OperatorTok { val = "!" } } & toknot ->
    match parseConNameList ([], NoInfo ()) (nextToken toknot.stream)
    with ((names, namesInfo), cur) in
    finishConTypeRestriction
      (TyData {
        info = mergeInfo toknot.info namesInfo,
        universe = mapEmpty nameCmp, positive = false,
        cons = setOfSeq nameCmp names
      })
      cur
  | { token = LIdentTok { val = val } } & tokvar ->
    finishConTypeRestriction
      (TyVar { info = tokvar.info, ident = nameNoSym val })
      (nextToken tokvar.stream)
  | start ->
    match parseConNameList ([], NoInfo ()) start with ((names, namesInfo), cur) in
    finishConTypeRestriction
      (TyData {
        info = mergeInfo start.info namesInfo,
        universe = mapEmpty nameCmp, positive = true,
        cons = setOfSeq nameCmp names
      })
      cur

  sem finishConTypeRestriction: all w. Type -> NextTokenResult -> ParseRes w (Type, Info, NextTokenResult)
  sem finishConTypeRestriction data =
  | { token = RBraceTok {} } & tokclose ->
    parseOk (data, tokclose.info, nextToken tokclose.stream)
  | cur -> parseErr (cur.info, "Expected '}' to close the constructor type restriction")

  sem parseConNameList: ([Name], Info) -> NextTokenResult -> (([Name], Info), NextTokenResult)
  sem parseConNameList acc =
  | { token = UIdentTok { val = val } } & tok ->
    parseConNameList (snoc acc.0 (nameNoSym val), mergeInfo acc.1 tok.info) (nextToken tok.stream)
  | { token = LIdentTok { val = val } } & tok ->
    parseConNameList (snoc acc.0 (nameNoSym val), mergeInfo acc.1 tok.info) (nextToken tok.stream)
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
  sem beginParseExprInParen: all w. State BrkOpExpr ROpen -> NextTokenResult -> NextTokenResult -> ParseRes w (Expr, NextTokenResult)
  sem beginParseTypeInParen: all w. State BrkOpType ROpen -> NextTokenResult -> NextTokenResult -> ParseRes w (Type, NextTokenResult)
  sem beginParsePatInParen:  all w. State BrkOpPat  ROpen -> NextTokenResult -> NextTokenResult -> ParseRes w (Pat,  NextTokenResult)
  sem endParseExprInParen:   all w. State BrkOpExpr ROpen -> NextTokenResult -> Expr -> NextTokenResult -> ParseRes w (Expr, NextTokenResult)
  sem endParseTypeInParen:   all w. State BrkOpType ROpen -> NextTokenResult -> Type -> NextTokenResult -> ParseRes w (Type, NextTokenResult)
  sem endParsePatInParen:    all w. State BrkOpPat  ROpen -> NextTokenResult -> Pat  -> NextTokenResult -> ParseRes w (Pat,  NextTokenResult)

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

  | cur -> parseErr (cur.info, "Expected ')' to close the parenthesized expression")

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

  | cur -> parseErr (cur.info, "Expected ')' to close the parenthesized type")

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

  | cur -> parseErr (cur.info, "Expected ')' to close the parenthesized pattern")

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
            parseErr (cur.info, "Expected ',' or ')' in tuple expression")
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
            parseErr (cur.info, "Expected ',' or ')' in tuple type")
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
            parseErr (cur.info, "Expected ',' or ')' in tuple pattern")
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
          parseErr (cur.info, "Expected ']' to close 'Tensor[...]'")
      )
    else
      parseErr (cur.info, "Expected '[' after 'Tensor'")
end

lang StringParser = AstParserBase + SeqAst + CharAst + SeqTotPat + CharPat + SeqTypeAst + CharTypeAst
  sem startsAtomExpr +=
  | { token = StringTok { } } -> true

  sem startsAtomType +=
  | { token = UIdentTok { val = "String" } } -> true

  sem parseExprROpen state +=
  | { token = StringTok { val = val } } & cur ->
    let charInfo = cur.info in
    let expr = TmSeq {
      tms = map (lam ch. TmConst {
        val = CChar { val = ch },
        ty = tyunknown_,
        info = charInfo
      }) val,
      ty = ityunknown_ cur.info,
      info = cur.info
    } in
    let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
    parseExprRClosed state (nextToken cur.stream)

  sem parseTypeROpen state +=
  | { token = UIdentTok { val = "String" } } & cur ->
    let typ = TySeq { ty = tychar_, info = cur.info } in
    let state = breakableAddAtom (configType ()) (OpTypeAtom typ) state in
    parseTypeRClosed state (nextToken cur.stream)

  sem parsePatROpen state +=
  | { token = StringTok { val = val } } & cur ->
    let charInfo = cur.info in
    let pat = PatSeqTot {
      pats = map (lam ch. PatChar {
        val = ch,
        ty = tychar_,
        info = charInfo
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

  sem opCatPat +=
  | OpPatSeqEdge _ -> CatPatApplication ()

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
            parseErr (cur.info, "Expected ',' or ']' in sequence expression")
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
        parseErr (cur.info, "Expected ']' to close the sequence type")
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
            parseErr (cur.info, "Expected ',' or ']' in sequence pattern")
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
      parseErr (tokpp.info, "'++' is not allowed here")

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
        parseErr (info, "Expected a literal sequence on at least one side of '++'")
    end
  
  sem groupingsAllowedPat +=
  | (OpPatSeqEdge _, OpPatSeqEdge _) -> GLeft ()
end

lang BraceParser = AstParserBase
  sem beginParseExprInBrace: all w. State BrkOpExpr ROpen -> NextTokenResult -> NextTokenResult -> ParseRes w (Expr, NextTokenResult)
  sem beginParseTypeInBrace: all w. State BrkOpType ROpen -> NextTokenResult -> NextTokenResult -> ParseRes w (Type, NextTokenResult)
  sem beginParsePatInBrace:  all w. State BrkOpPat  ROpen -> NextTokenResult -> NextTokenResult -> ParseRes w (Pat,  NextTokenResult)
  
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
                  parseErr (cur.info, "Expected ',' or '}' in record expression")
              end
            )
          else
            parseErr (cur.info, "Expected '=' after record field name")
        else
          parseErr (cur.info, "Expected a field name or '}' in record expression")
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
                      parseErr (cur.info, "Expected ',' or '}' in record update")
                  end
                )
              else
                parseErr (cur.info, "Expected '=' after record update field name")
            else
              parseErr (cur.info, "Expected a field name or '}' in record update")
          in

          let res = parseItems [] cur in

          result.bind res (lam res.
            match res with (close, updates) in
            let info = mergeInfo open.info close.info in
            let typ = ityunknown_ info in
            let expr = foldl
              (lam rec. lam update : (SID, Expr).
                TmRecordUpdate {
                  rec = rec,
                  key = update.0,
                  value = update.1,
                  ty = typ,
                  info = info
                })
              rec updates
            in
            let state = breakableAddAtom (configExpr ()) (OpExprAtom expr) state in
            parseExprRClosed state (nextToken close.stream)
          )
        else
          parseErr (cur.info, "Expected 'with' after the record expression to update")
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
                parseErr (cur.info, "Expected ',' or '}' in record type")
            end
          )
        else
          parseErr (cur.info, "Expected ':' after record type field name")
      else
        parseErr (cur.info, "Expected a field name or '}' in record type")
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
                parseErr (cur.info, "Expected ',' or '}' in record pattern")
            end
          )
        else
          parseErr (cur.info, "Expected '=' after record pattern field name")
      else
        parseErr (cur.info, "Expected a field name or '}' in record pattern")
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
        parseErr (cur.info, "Expected 'in' after the 'let' declaration")
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
          parseErr (cur.info, "Expected '=' after the 'let' binding's identifier (and optional type annotation)")
      )
    else
      parseErr (cur.info, "Expected an identifier after 'let'")
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
            parseErr (cur.info, "Expected 'let' or 'in' in a 'recursive let' chain")
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
            parseErr (cur.info, "Expected 'let' or 'end' in a 'recursive let' chain")
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
        parseErr (cur.info, "Expected 'in' after the 'type' declaration")
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
          info = lastInfo,
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
      parseErr (cur.info, "Expected a type identifier after 'type'")
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

  sem opCatExpr +=
  | OpExprLam _ -> CatExprBinder ()

  sem opCatType +=
  | OpTypeArrow _ -> CatTypeArrow ()

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
        parseErr (cur.info, "Expected '.' after the 'lam' parameter")
    )

  sem parseTypeRClosed state +=
  | { token = OperatorTok { val = "->" } } & cur ->
    match breakableAddInfix (configType ()) (OpTypeArrow cur.info) state with Some(state) then
      let cur = nextToken cur.stream in
      parseTypeROpen state cur
    else
      parseErr (cur.info, "'->' is not allowed here")

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

  sem opCatExpr +=
  | OpExprMatchIn _ -> CatExprBinder ()
  | OpExprMatchElse _ -> CatExprBinder ()

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
                  parseErr (cur.info, "Expected 'else' after the 'match ... then' branch")
              )

            -- match .. with .. in ..
            case { token = KeywordTok { val = "in" } } & tokin then
              let cur = nextToken tokin.stream in
              let info = mergeInfo tokmatch.info tokin.info in
              let state = breakableAddPrefix (configExpr ()) (OpExprMatchIn (info, target, pat)) state in
              parseExprROpen state cur

            case _ then
              parseErr (cur.info, "Expected 'then' or 'in' after the 'match ... with <pattern>'")
          end
        )        
      else
        parseErr (cur.info, "Expected 'with' after the 'match' target expression")
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
        info = info
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
                  -- The match reaches to the end of the branch it falls
                  -- through to, so that each link of the chain contains the
                  -- next one rather than sitting beside it.
                  let caseInfo = mergeInfo tokcase.info (infoTm els) in
                  let expr = TmMatch {
                    target = TmVar {
                      ident = nameNoSym "X",
                      ty = tyunknown_,
                      info = caseInfo,
                      frozen = false
                    },
                    pat = pat,
                    thn = thn,
                    els = els,
                    ty = tyunknown_,
                    info = caseInfo
                  } in
                  parseOk (expr, tokend, cur)
                )
              )
            else
              parseErr (cur.info, "Expected 'then' after the 'case' pattern")
          )
        case { token = KeywordTok { val = "end" } } & tokend then
          let cur = nextToken tokend.stream in
          let expr = TmNever {
            ty = tyunknown_,
            info = tokend.info
          } in
          parseOk (expr, tokend, cur)
        case _ then
          parseErr (cur.info, "Expected 'case' or 'end' in a 'switch' expression")
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
        let typ = ityunknown_ info in
        let expr = TmDecl {
          decl = DeclLet {
            ident = nameNoSym "X",
            tyAnnot = typ,
            tyBody = typ,
            body = body,
            info = info
          },
          inexpr = inexpr,
          ty = typ,
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

  sem opCatPat +=
  | OpPatAnd _ -> CatPatLogic ()

  sem parsePatRClosed state +=
  | { token = OperatorTok { val = "&" } } & tokop ->
    match breakableAddInfix (configPat ()) (OpPatAnd tokop.info) state with Some(state) then
      parsePatROpen state (nextToken tokop.stream)
    else
      parseErr (tokop.info, "'&' is not allowed here")

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

  sem opCatPat +=
  | OpPatOr _ -> CatPatLogic ()

  sem parsePatRClosed state +=
  | { token = OperatorTok { val = "|" } } & tokop ->
    match breakableAddInfix (configPat ()) (OpPatOr tokop.info) state with Some(state) then
      parsePatROpen state (nextToken tokop.stream)
    else
      parseErr (tokop.info, "'|' is not allowed here")

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

  sem opCatPat +=
  | OpPatNot _ -> CatPatPrefix ()

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
        parseErr (cur.info, "Expected 'in' after the 'utest' declaration")
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
        parseErr (cur.info, "Expected 'with' after the 'utest' expression")
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
        parseErr (cur.info, "Expected 'in' after the 'con' declaration")
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
      parseErr (cur.info, "Expected a constructor identifier after 'con'")
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
        parseErr (cur.info, "Expected 'in' after the 'external' declaration")
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
        parseErr (cur.info, "Expected ':' after the 'external' identifier (and optional '!')")
    else
      parseErr (cur.info, "Expected an identifier after 'external'")
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
        parseErr (cur.info, "Expected 'in' after the 'use' declaration")
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
      parseErr (cur.info, "Expected a language identifier after 'use'")

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
        parseErr (cur.info, "Expected 'in' after 'use <lang>' in a type")
    else
      parseErr (cur.info, "Expected a language identifier after 'use'")
end

lang ProjParser = AstParserBase + MatchAst + NeverAst + RecordPat + NamedPat + VarAst
  syn BrkOpExpr lstyle rstyle +=
  | OpExprProj (Info, String)

  sem getInfoExpr +=
  | OpExprProj (info, _) -> info

  sem opCatExpr +=
  | OpExprProj _ -> CatExprPostfix ()

  sem parseExprRClosed state +=
  | { token = OperatorTok { val = "." } } & tokdot ->
    let cur = nextToken tokdot.stream in
    switch cur
      case { token = IntTok { val = n } } & toklabel then
        let op = OpExprProj (mergeInfo tokdot.info toklabel.info, int2string n) in
        match breakableAddPostfix (configExpr ()) op state with Some state then
          parseExprRClosed state (nextToken toklabel.stream)
        else
          parseErr (toklabel.info, "'.' projection is not allowed here")
      case { token = LIdentTok { val = label } | HashStringTok { hash = "label", val = label } } & toklabel then
        let op = OpExprProj (mergeInfo tokdot.info toklabel.info, label) in
        match breakableAddPostfix (configExpr ()) op state with Some state then
          parseExprRClosed state (nextToken toklabel.stream)
        else
          parseErr (toklabel.info, "'.' projection is not allowed here")
      case _ then
        parseErr (cur.info, "Expected a field label (an identifier or integer) after '.'")
    end

  sem constructPostfixExpr +=
  | (OpExprProj (info, label), target) ->
    let fullInfo = mergeInfo (infoTm target) info in
    let tmpIdent = nameNoSym "X" in
    parseOk (TmMatch {
      target = target,
      pat = PatRecord {
        bindings = mapInsert (stringToSid label)
          (PatNamed { ident = PName tmpIdent, ty = tyunknown_, info = fullInfo })
          (mapEmpty cmpSID),
        ty = tyunknown_,
        info = fullInfo
      },
      thn = TmVar { ident = tmpIdent, ty = tyunknown_, info = fullInfo, frozen = false },
      els = TmNever { ty = tyunknown_, info = fullInfo },
      ty = ityunknown_ fullInfo,
      info = fullInfo
    })
end

lang IfParser = AstParserBase + MatchAst + BoolPat + IfKeyword + ThenKeyword + ElseKeyword
  syn BrkOpExpr lstyle rstyle +=
  | OpExprIf (Info, Expr, Expr)

  sem getInfoExpr +=
  | OpExprIf (info, _, _) -> info

  sem opCatExpr +=
  | OpExprIf _ -> CatExprBinder ()

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
            parseErr (cur.info, "Expected 'else' after the 'if ... then' branch")
        )
      else
        parseErr (cur.info, "Expected 'then' after the 'if' condition")
    )

  sem constructPrefixExpr +=
  | (OpExprIf (info, cond, thn), els) ->
    let info = mergeInfo info (infoTm els) in
    parseOk (TmMatch {
      target = cond,
      pat = PatBool { val = true, ty = tybool_, info = infoTm cond },
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

  sem opCatExpr +=
  | OpExprSemi _ -> CatExprSequencing ()

  sem parseExprRClosed state +=
  | { token = SemiTok {} } & toksemi ->
    match breakableAddInfix (configExpr ()) (OpExprSemi toksemi.info) state with Some state then
      parseExprROpen state (nextToken toksemi.stream)
    else
      parseErr (toksemi.info, "';' is not allowed here")

  sem constructInfixExpr +=
  | (OpExprSemi info, lhs, rhs) ->
    let info = mergeInfo (infoTm lhs) (infoTm rhs) in
    let typ = ityunknown_ info in
    parseOk (TmDecl {
      decl = DeclLet {
        ident = nameNoSym "",
        tyAnnot = typ,
        tyBody = typ,
        body = lhs,
        info = info
      },
      inexpr = rhs,
      ty = typ,
      info = info
    })

  sem groupingsAllowedExpr +=
  | (OpExprSemi _, OpExprSemi _) -> GRight ()
end

lang KindParser = AstParserBase + DataKindAst
  sem parseKind +=
  | { token = LBraceTok {} } & tokopen ->
    parseKindBody (mapEmpty nameCmp) (nextToken tokopen.stream)

  sem parseKindBody: all w. Map Name {lower : Set Name, upper : Option (Set Name)} -> NextTokenResult -> ParseRes w (Kind, NextTokenResult)
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
        parseErr (cur.info, "Expected ',' or '}' in kind")
    )

  sem parseKindEntry: all w. NextTokenResult -> ParseRes w (Name, {lower : Set Name, upper : Option (Set Name)}, NextTokenResult)
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
        parseErr (cur.info, "Expected '>', '<', or '|' after '[' in a kind entry")
      end
    else parseErr (cur.info, "Expected '[' after the type name in a kind entry")
  | cur -> parseErr (cur.info, "Expected a type identifier in a kind entry")

  sem finishKindEntry: all w. Name -> {lower : Set Name, upper : Option (Set Name)} -> NextTokenResult -> ParseRes w (Name, {lower : Set Name, upper : Option (Set Name)}, NextTokenResult)
  sem finishKindEntry name entry =
  | { token = RBracketTok {} } & tokclose -> parseOk (name, entry, nextToken tokclose.stream)
  | cur -> parseErr (cur.info, "Expected ']' to close the kind entry")

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
            parseErr (cur.info, "Expected '.' after the kind constraint in 'all'")
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
        parseErr (cur.info, "Expected '.' after the type variable in 'all'")
    else
      parseErr (cur.info, "Expected a type variable identifier after 'all'")
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

      match cur with { token = OperatorTok { val = ("=" | "+=") & op } } & tokop then
        let isSum = eqString op "+=" in
        let cur = nextToken tokop.stream in
        recursive let parseConstrs = lam acc. lam cur.
          match cur with { token = OperatorTok { val = "|" } } & tokbar then
            let cur = nextToken tokbar.stream in
            match cur with { token = UIdentTok { val = conIdent } | HashStringTok { hash = "con", val = conIdent } } & tokcon then
              let cur = nextToken tokcon.stream in
              let tyRes =
                if startsAtomType cur then
                  result.map (lam r. match r with (ty, cur) in (ty, infoTy ty, cur)) (parseType cur)
                else
                  parseOk (TyRecord { fields = mapEmpty cmpSID, info = tokcon.info }, tokcon.info, cur)
              in
              result.bind tyRes (lam res.
                match res with (ty, tyEndInfo, cur) in
                let constr = {ident = nameNoSym conIdent, tyIdent = ty, info = mergeInfo tokbar.info tyEndInfo} in
                parseConstrs (snoc acc constr) cur
              )
            else
              parseErr (cur.info, "Expected a constructor identifier after '|' in a 'syn' declaration")
          else
            parseOk (acc, cur)
        in

        result.bind (parseConstrs [] cur) (lam res.
          match res with (constrs, cur) in
          let kind = if isSum then SynSum { base = nameNoSym ident } else SynBase () in
          let endInfo = match constrs with _ ++ [lastConstr] then lastConstr.info else tokop.info in
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
        parseErr (cur.info, "Expected '=' or '+=' after the 'syn' name and parameters")
    else
      parseErr (cur.info, "Expected a type identifier after 'syn'")
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
                      parseErr (cur.info, "Expected ')' to close the 'sem' parameter")
                  )
                else
                  parseErr (cur.info, "Expected ':' after the 'sem' parameter name")
              else
                parseErr (cur.info, "Expected an identifier after '(' in a 'sem' parameter")
            case { token = LIdentTok { val = pident } | HashStringTok { hash = "var", val = pident } } & tokpident then
              let info = tokpident.info in
              let typ = ityunknown_ info in
              let param = {ident = nameNoSym pident, tyAnnot = typ, tyParam = typ, info = info} in
              parseParams (snoc acc param) (nextToken tokpident.stream)
            case _ then
              parseOk (acc, cur)
          end
        in

        result.bind (parseParams [] cur) (lam res.
          match res with (params, cur) in
          match cur with { token = OperatorTok { val = ("=" | "+=") & op } } & tokop then
            let isSum = eqString op "+=" in
            let cur = nextToken tokop.stream in
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
                    parseErr (cur.info, "Expected '->' after the 'sem' case pattern")
                )
              else
                parseOk (acc, cur)
            in

            result.bind (parseCases [] cur) (lam res.
              match res with (cases, cur) in
              let kind = if isSum then SemSum { base = nameNoSym ident } else SemBase () in
              let endInfo = match cases with _ ++ [lastCase] then lastCase.info else tokop.info in
              let info = mergeInfo toksem.info endInfo in
              let typ = ityunknown_ info in
              let decl = DeclSem {
                ident = nameNoSym ident,
                tyAnnot = typ,
                tyBody = typ,
                impl = Some { params = params, cases = cases },
                info = info,
                kind = kind
              } in
              parseOk (decl, cur)
            )
          else
            parseErr (cur.info, "Expected '=' or '+=' after the 'sem' name and parameters")
        )
    else
      parseErr (cur.info, "Expected an identifier after 'sem'")
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
          parseErr (cur.info, "Expected an included language identifier after '+'")
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
      parseErr (cur.info, "Expected an identifier after 'lang'")
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
      parseErr (cur.info, "Expected a string literal path after 'include'")
end

-- The entry point for parsing an entire mcore file: zero or more
-- `include` statements, zero or more top-level declarations, and an
-- optional `mexpr <expr>` section.
lang ProgramParser = AstParserBase + MLangTopLevel + RecordAst + IncludeDeclParser + MexprKeyword
  sem parseProgram: all w. NextTokenResult -> ParseRes w (MLangProgram, NextTokenResult)

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
            parseErr (cur.info, "Expected end of file")
        )
      )
    )
end

lang UnexpectedTokenParser = AstParserBase
  sem parseExprROpen state +=
  | cur -> parseErr (cur.info, "Expected the start of an expression")

  sem parseDecl +=
  | cur -> parseErr (cur.info, "Expected the start of a declaration")

  sem parseTypeROpen state +=
  | cur -> parseErr (cur.info, "Expected the start of a type")

  sem parseKind +=
  | cur -> parseErr (cur.info, "Expected a kind constraint")

  sem parsePatROpen state +=
  | cur -> parseErr (cur.info, "Expected the start of a pattern")
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
  + UnexpectedTokenParser
  
  -- Can we remove this?
  sem groupingsAllowedPat +=
  | (OpPatAnd _, OpPatOr _) -> GLeft ()
  | (OpPatOr _, OpPatAnd _) -> GRight ()
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
  + MLangCmp
  + MExprToJson
end

mexpr

use TestParser in

let lex = lam str. nextToken {pos = initPos "t", str = str} in

let compactSpan = lam s.
  match s with "<" ++ rest then
    match index (eqChar ' ') rest with Some i then
      subsequence rest (addi i 1) (subi (subi (length rest) i) 2)
    else s
  else s in

let scalarStr = lam v.
  switch v
  case JsonString s then Some s
  case JsonBool b then Some (if b then "true" else "false")
  case JsonInt i then Some (int2string i)
  case JsonFloat f then Some (float2string f)
  case JsonNull _ then Some "null"
  case JsonArray xs then match xs with [JsonString s] ++ _ then Some s else None ()
  case _ then None ()
  end in

recursive
  let dumpNode = lam ind. lam label. lam fields.
    let conName = match mapLookup "con" fields with Some (JsonString c) then c else "?" in
    let span = match mapLookup "info" fields with Some (JsonString i)
      then concat " " (compactSpan i) else "" in
    let isInferredSlot = lam k.
      and (eqString k "ty")
          (or (isPrefix eqChar "Tm" conName) (isPrefix eqChar "Pat" conName)) in
    let rest = filter
      (lam kv. not (or (isInferredSlot kv.0)
                       (or (eqString kv.0 "con") (eqString kv.0 "info"))))
      (mapBindings fields) in
    let scalars = foldl (lam acc. lam kv.
        match scalarStr kv.1 with Some v then
          if and (eqString kv.0 "frozen") (eqString v "false") then acc
          else snoc acc (join [" ", kv.0, "=", v])
        else acc) [] rest in
    let kids = foldl (lam acc. lam kv. concat acc (emit (addi ind 2) kv.0 kv.1)) [] rest in
    cons (join [make ind ' ', label, conName, span, join scalars]) kids
  let emit = lam ind. lam label. lam v.
    switch v
    case JsonObject f then
      if mapMem "con" f then dumpNode ind (concat label ": ") f
      else join (map (lam kv. emit ind (join [label, ".", kv.0]) kv.1) (mapBindings f))
    case JsonArray xs then join (map (emit ind label) xs)
    case _ then []
    end
in

-- One line per node: its constructor, where it sits, and its scalar fields.
let dumpOf = lam s.
  switch result.consume (result.map (lam a. a.0) (parseExpr (lex s)))
  case (_, Right e) then dumpNode 0 "" (match exprToJson e with JsonObject f in f)
  case (_, Left _) then ["PARSE FAILED"]
  end in

-- `declToJson` has no cases for the MLang declarations, so a program is
-- pinned by its printed form and by a walk of every span it contains.
let progStrOf = lam s.
  switch result.consume (result.map (lam a. a.0) (parseProgram (lex s)))
  case (_, Right p) then strSplit "\n" (mlang2str p)
  case (_, Left _) then ["PARSE FAILED"]
  end in
recursive
  let sE = lam acc. lam e.
    let acc = snoc acc (join ["expr ", compactSpan (info2str (infoTm e))]) in
    let acc = sfold_Expr_Pat sP acc e in
    sfold_Expr_Expr sE acc e
  let sP = lam acc. lam q.
    let acc = snoc acc (join ["pat ", compactSpan (info2str (infoPat q))]) in
    let acc = sfold_Pat_Expr sE acc q in
    sfold_Pat_Pat sP acc q
  let sD = lam acc. lam d.
    let acc = snoc acc (join ["decl ", compactSpan (info2str (infoDecl d))]) in
    let acc = sfold_Decl_Decl sD acc d in
    let acc = sfold_Decl_Pat sP acc d in
    sfold_Decl_Expr sE acc d
in

let progSpansOf = lam s.
  switch result.consume (result.map (lam a. a.0) (parseProgram (lex s)))
  case (_, Right p) then sE (foldl sD [] p.decls) p.expr
  case (_, Left _) then ["PARSE FAILED"]
  end in

let errOf = lam s.
  switch result.consume (result.map (lam a. a.0) (parseExpr (lex s)))
  case (_, Left errs) then
    match head errs s with (i, msg) in join [compactSpan (info2str i), ": ", msg]
  case (_, Right _) then "PARSED" end in

let progErrOf = lam s.
  switch result.consume (result.map (lam a. a.0) (parseProgram (lex s)))
  case (_, Left errs) then
    match head errs s with (i, msg) in join [compactSpan (info2str i), ": ", msg]
  case (_, Right _) then "PARSED" end in

-------------------------------------------------------------------------
-- Expressions
-------------------------------------------------------------------------

utest dumpOf "1" with
[ "TmConst 1:0-1:1 const=1" ] in

utest dumpOf "-1" with
[ "TmConst 1:0-1:2 const=(negi 1)" ] in

utest dumpOf "1.0" with
[ "TmConst 1:0-1:3 const=1." ] in

utest dumpOf "true" with
[ "TmConst 1:0-1:4 const=true" ] in

utest dumpOf "\'a\'" with
[ "TmConst 1:0-1:3 const=\'a\'" ] in

utest dumpOf "\'😊\'" with
[ "TmConst 1:0-1:3 const=\'😊\'" ] in

utest dumpOf "\"ab\"" with
[ "TmSeq 1:0-1:4"
, "  tms: TmConst 1:0-1:4 const=\'a\'"
, "  tms: TmConst 1:0-1:4 const=\'b\'" ] in

utest dumpOf "()" with
[ "TmRecord 1:0-1:2" ] in

utest dumpOf "a" with
[ "TmVar 1:0-1:1 ident=a" ] in

utest dumpOf "#var\"a\"" with
[ "TmVar 1:0-1:7 ident=a" ] in

utest dumpOf "#frozen\"a\"" with
[ "TmVar 1:0-1:10 ident=a frozen=true" ] in

utest dumpOf "addi 1 2" with
[ "TmApp 1:0-1:8"
, "  lhs: TmApp 1:0-1:6"
, "    lhs: TmVar 1:0-1:4 ident=addi"
, "    rhs: TmConst 1:5-1:6 const=1"
, "  rhs: TmConst 1:7-1:8 const=2" ] in

utest dumpOf "addi (addi 1 2) 3" with
[ "TmApp 1:0-1:17"
, "  lhs: TmApp 1:0-1:15"
, "    lhs: TmVar 1:0-1:4 ident=addi"
, "    rhs: TmApp 1:5-1:15"
, "      lhs: TmApp 1:6-1:12"
, "        lhs: TmVar 1:6-1:10 ident=addi"
, "        rhs: TmConst 1:11-1:12 const=1"
, "      rhs: TmConst 1:13-1:14 const=2"
, "  rhs: TmConst 1:16-1:17 const=3" ] in

utest dumpOf "let a = 1 in a" with
[ "TmDecl (merged) 1:0-1:14"
, "  decls: DeclLet 1:0-1:9 ident=a"
, "    body: TmConst 1:8-1:9 const=1"
, "    tyBody: TyUnknown 1:0-1:9"
, "    tyAnnot: TyUnknown 1:4-1:5"
, "  inexpr: TmVar 1:13-1:14 ident=a" ] in

utest dumpOf "let a: Int -> Int = f in a" with
[ "TmDecl (merged) 1:0-1:26"
, "  decls: DeclLet 1:0-1:21 ident=a"
, "    body: TmVar 1:20-1:21 ident=f"
, "    tyBody: TyUnknown 1:0-1:21"
, "    tyAnnot: TyArrow 1:7-1:17"
, "      to: TyInt 1:14-1:17"
, "      from: TyInt 1:7-1:10"
, "  inexpr: TmVar 1:25-1:26 ident=a" ] in

utest dumpOf "let a: [Int] = x in a" with
[ "TmDecl (merged) 1:0-1:21"
, "  decls: DeclLet 1:0-1:16 ident=a"
, "    body: TmVar 1:15-1:16 ident=x"
, "    tyBody: TyUnknown 1:0-1:16"
, "    tyAnnot: TySeq 1:7-1:12"
, "      ty: TyInt 1:8-1:11"
, "  inexpr: TmVar 1:20-1:21 ident=a" ] in

utest dumpOf "let a: {x: Int} = y in a" with
[ "TmDecl (merged) 1:0-1:24"
, "  decls: DeclLet 1:0-1:19 ident=a"
, "    body: TmVar 1:18-1:19 ident=y"
, "    tyBody: TyUnknown 1:0-1:19"
, "    tyAnnot: TyRecord 1:7-1:15"
, "      fields.x: TyInt 1:11-1:14"
, "  inexpr: TmVar 1:23-1:24 ident=a" ] in

utest dumpOf "let a: all x. x -> x = f in a" with
[ "TmDecl (merged) 1:0-1:29"
, "  decls: DeclLet 1:0-1:24 ident=a"
, "    body: TmVar 1:23-1:24 ident=f"
, "    tyBody: TyUnknown 1:0-1:24"
, "    tyAnnot: TyAll 1:7-1:20 kind=Poly ident=x"
, "      ty: TyArrow 1:14-1:20"
, "        to: TyVar 1:19-1:20 ident=x"
, "        from: TyVar 1:14-1:15 ident=x"
, "  inexpr: TmVar 1:28-1:29 ident=a" ] in

utest dumpOf "let a: Tensor[Int] = x in a" with
[ "TmDecl (merged) 1:0-1:27"
, "  decls: DeclLet 1:0-1:22 ident=a"
, "    body: TmVar 1:21-1:22 ident=x"
, "    tyBody: TyUnknown 1:0-1:22"
, "    tyAnnot: TyTensor 1:7-1:18"
, "      ty: TyInt 1:14-1:17"
, "  inexpr: TmVar 1:26-1:27 ident=a" ] in

utest dumpOf "let a: Map SID Expr = x in a" with
[ "TmDecl (merged) 1:0-1:28"
, "  decls: DeclLet 1:0-1:23 ident=a"
, "    body: TmVar 1:22-1:23 ident=x"
, "    tyBody: TyUnknown 1:0-1:23"
, "    tyAnnot: TyApp 1:7-1:19"
, "      lhs: TyApp 1:7-1:14"
, "        lhs: TyCon 1:7-1:10 ident=Map"
, "          data: TyUnknown 1:7-1:10"
, "        rhs: TyCon 1:11-1:14 ident=SID"
, "          data: TyUnknown 1:11-1:14"
, "      rhs: TyCon 1:15-1:19 ident=Expr"
, "        data: TyUnknown 1:15-1:19"
, "  inexpr: TmVar 1:27-1:28 ident=a" ] in

utest dumpOf "lam a. a" with
[ "TmLam 1:0-1:8 ident=a"
, "  body: TmVar 1:7-1:8 ident=a"
, "  tyAnnot: TyUnknown file info"
, "  tyParam: TyUnknown 1:4-1:5" ] in

utest dumpOf "lam a: Int. a" with
[ "TmLam 1:0-1:13 ident=a"
, "  body: TmVar 1:12-1:13 ident=a"
, "  tyAnnot: TyInt 1:7-1:10"
, "  tyParam: TyUnknown 1:4-1:5" ] in

utest dumpOf "lam. ()" with
[ "TmLam 1:0-1:7 ident="
, "  body: TmRecord 1:5-1:7"
, "  tyAnnot: TyUnknown file info"
, "  tyParam: TyUnknown file info" ] in

utest dumpOf "[1, 2]" with
[ "TmSeq 1:0-1:6"
, "  tms: TmConst 1:1-1:2 const=1"
, "  tms: TmConst 1:4-1:5 const=2" ] in

utest dumpOf "(1, 2)" with
[ "TmRecord 1:0-1:6"
, "  bindings.0: TmConst 1:1-1:2 const=1"
, "  bindings.1: TmConst 1:4-1:5 const=2" ] in

utest dumpOf "{a = 1, b = 2}" with
[ "TmRecord 1:0-1:14"
, "  bindings.a: TmConst 1:5-1:6 const=1"
, "  bindings.b: TmConst 1:12-1:13 const=2" ] in

utest dumpOf "{a with x = 1, y = 2}" with
[ "TmRecordUpdate 1:0-1:21 key=y"
, "  rec: TmRecordUpdate 1:0-1:21 key=x"
, "    rec: TmVar 1:1-1:2 ident=a"
, "    value: TmConst 1:12-1:13 const=1"
, "  value: TmConst 1:19-1:20 const=2" ] in

utest dumpOf "x.0" with
[ "TmMatch 1:0-1:3"
, "  els: TmNever 1:0-1:3"
, "  pat: PatRecord 1:0-1:3"
, "    bindings.0: PatNamed 1:0-1:3 ident=X"
, "  thn: TmVar 1:0-1:3 ident=X"
, "  target: TmVar 1:0-1:1 ident=x" ] in

utest dumpOf "x.field" with
[ "TmMatch 1:0-1:7"
, "  els: TmNever 1:0-1:7"
, "  pat: PatRecord 1:0-1:7"
, "    bindings.field: PatNamed 1:0-1:7 ident=X"
, "  thn: TmVar 1:0-1:7 ident=X"
, "  target: TmVar 1:0-1:1 ident=x" ] in

utest dumpOf "(x.0).1" with
[ "TmMatch 1:0-1:7"
, "  els: TmNever 1:0-1:7"
, "  pat: PatRecord 1:0-1:7"
, "    bindings.1: PatNamed 1:0-1:7 ident=X"
, "  thn: TmVar 1:0-1:7 ident=X"
, "  target: TmMatch 1:0-1:5"
, "    els: TmNever 1:1-1:4"
, "    pat: PatRecord 1:1-1:4"
, "      bindings.0: PatNamed 1:1-1:4 ident=X"
, "    thn: TmVar 1:1-1:4 ident=X"
, "    target: TmVar 1:1-1:2 ident=x" ] in

utest dumpOf "never" with
[ "TmNever 1:0-1:5" ] in

utest dumpOf "recursive let a = lam b. 1 in c" with
[ "TmDecl (merged) 1:0-1:31"
, "  decls: DeclRecLets 1:0-1:29"
, "    bindings.body: TmLam 1:18-1:26 ident=b"
, "      body: TmConst 1:25-1:26 const=1"
, "      tyAnnot: TyUnknown file info"
, "      tyParam: TyUnknown 1:22-1:23"
, "    bindings.tyBody: TyUnknown 1:10-1:26"
, "    bindings.tyAnnot: TyUnknown 1:14-1:15"
, "  inexpr: TmVar 1:30-1:31 ident=c" ] in

utest dumpOf "Test (1, 2)" with
[ "TmConApp 1:0-1:11 ident=Test"
, "  body: TmRecord 1:5-1:11"
, "    bindings.0: TmConst 1:6-1:7 const=1"
, "    bindings.1: TmConst 1:9-1:10 const=2" ] in

utest dumpOf "match a with 1 then b else c" with
[ "TmMatch 1:0-1:28"
, "  els: TmVar 1:27-1:28 ident=c"
, "  pat: PatInt 1:13-1:14 val=1"
, "  thn: TmVar 1:20-1:21 ident=b"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "match a with 1 in b" with
[ "TmMatch 1:0-1:19"
, "  els: TmNever 1:0-1:19"
, "  pat: PatInt 1:13-1:14 val=1"
, "  thn: TmVar 1:18-1:19 ident=b"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "match a with (1, 2) in x" with
[ "TmMatch 1:0-1:24"
, "  els: TmNever 1:0-1:24"
, "  pat: PatRecord 1:13-1:19"
, "    bindings.0: PatInt 1:14-1:15 val=1"
, "    bindings.1: PatInt 1:17-1:18 val=2"
, "  thn: TmVar 1:23-1:24 ident=x"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "match a with {b = 1} in x" with
[ "TmMatch 1:0-1:25"
, "  els: TmNever 1:0-1:25"
, "  pat: PatRecord 1:13-1:20"
, "    bindings.b: PatInt 1:18-1:19 val=1"
, "  thn: TmVar 1:24-1:25 ident=x"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "match a with [1] ++ rest in x" with
[ "TmMatch 1:0-1:29"
, "  els: TmNever 1:0-1:29"
, "  pat: PatSeqEdge 1:13-1:24 middle=rest"
, "    prefix: PatInt 1:14-1:15 val=1"
, "  thn: TmVar 1:28-1:29 ident=x"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "match a with 1 & 2 in b" with
[ "TmMatch 1:0-1:23"
, "  els: TmNever 1:0-1:23"
, "  pat: PatAnd 1:13-1:18"
, "    lpat: PatInt 1:13-1:14 val=1"
, "    rpat: PatInt 1:17-1:18 val=2"
, "  thn: TmVar 1:22-1:23 ident=b"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "match a with 1 | 2 in b" with
[ "TmMatch 1:0-1:23"
, "  els: TmNever 1:0-1:23"
, "  pat: PatOr 1:13-1:18"
, "    lpat: PatInt 1:13-1:14 val=1"
, "    rpat: PatInt 1:17-1:18 val=2"
, "  thn: TmVar 1:22-1:23 ident=b"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "match a with C x in b" with
[ "TmMatch 1:0-1:21"
, "  els: TmNever 1:0-1:21"
, "  pat: PatCon 1:13-1:16 ident=C"
, "    subpat: PatNamed 1:15-1:16 ident=x"
, "  thn: TmVar 1:20-1:21 ident=b"
, "  target: TmVar 1:6-1:7 ident=a" ] in

utest dumpOf "utest a with 1 in x" with
[ "TmDecl (merged) 1:0-1:19"
, "  decls: DeclUtest 1:0-1:14 tusing=null"
, "    test: TmVar 1:6-1:7 ident=a"
, "    expected: TmConst 1:13-1:14 const=1"
, "  inexpr: TmVar 1:18-1:19 ident=x" ] in

utest dumpOf "utest a with 1 using eq else b in x" with
[ "TmDecl (merged) 1:0-1:35"
, "  decls: DeclUtest 1:0-1:30"
, "    test: TmVar 1:6-1:7 ident=a"
, "    tusing: TmVar 1:21-1:23 ident=eq"
, "    expected: TmConst 1:13-1:14 const=1"
, "  inexpr: TmVar 1:34-1:35 ident=x" ] in

utest dumpOf "switch a end" with
[ "TmDecl (merged) 1:0-1:12"
, "  decls: DeclLet 1:0-1:12 ident=X"
, "    body: TmVar 1:7-1:8 ident=a"
, "    tyBody: TyUnknown 1:0-1:12"
, "    tyAnnot: TyUnknown 1:0-1:12"
, "  inexpr: TmNever 1:9-1:12" ] in

utest dumpOf "switch a case 1 then b case 2 then c end" with
[ "TmDecl (merged) 1:0-1:40"
, "  decls: DeclLet 1:0-1:40 ident=X"
, "    body: TmVar 1:7-1:8 ident=a"
, "    tyBody: TyUnknown 1:0-1:40"
, "    tyAnnot: TyUnknown 1:0-1:40"
, "  inexpr: TmMatch 1:9-1:40"
, "    els: TmMatch 1:23-1:40"
, "      els: TmNever 1:37-1:40"
, "      pat: PatInt 1:28-1:29 val=2"
, "      thn: TmVar 1:35-1:36 ident=c"
, "      target: TmVar 1:23-1:40 ident=X"
, "    pat: PatInt 1:14-1:15 val=1"
, "    thn: TmVar 1:21-1:22 ident=b"
, "    target: TmVar 1:9-1:40 ident=X" ] in

utest dumpOf "if true then 1 else 2" with
[ "TmMatch 1:0-1:21"
, "  els: TmConst 1:20-1:21 const=2"
, "  pat: PatBool 1:3-1:7 val=true"
, "  thn: TmConst 1:13-1:14 const=1"
, "  target: TmConst 1:3-1:7 const=true" ] in

utest dumpOf "1; 2" with
[ "TmDecl (merged) 1:0-1:4"
, "  decls: DeclLet 1:0-1:4 ident="
, "    body: TmConst 1:0-1:1 const=1"
, "    tyBody: TyUnknown 1:0-1:4"
, "    tyAnnot: TyUnknown 1:0-1:4"
, "  inexpr: TmConst 1:3-1:4 const=2" ] in

utest dumpOf "type T a = Int in x" with
[ "TmDecl (merged) 1:0-1:19"
, "  decls: DeclType 1:0-1:14 ident=T"
, "    tyIdent: TyInt 1:11-1:14"
, "  inexpr: TmVar 1:18-1:19 ident=x" ] in

utest dumpOf "con Foo: Int in x" with
[ "TmDecl (merged) 1:0-1:17"
, "  decls: DeclConDef 1:0-1:12 ident=Foo"
, "    tyIdent: TyInt 1:9-1:12"
, "  inexpr: TmVar 1:16-1:17 ident=x" ] in

utest dumpOf "external foo: Int in foo" with
[ "TmDecl (merged) 1:0-1:24"
, "  decls: DeclExt 1:0-1:17 ident=foo effect=false"
, "    tyIdent: TyInt 1:14-1:17"
, "  inexpr: TmVar 1:21-1:24 ident=foo" ] in

utest dumpOf "use Foo in x" with
[ "TmDecl (merged) 1:0-1:12"
, "  decls: DeclUse 1:0-1:7 ident=Foo"
, "  inexpr: TmVar 1:11-1:12 ident=x" ] in

-------------------------------------------------------------------------
-- What a malformed expression reports, and where
-------------------------------------------------------------------------

utest errOf "(" with "1:1-1:1: Expected the start of an expression" in
utest errOf ")" with "1:0-1:1: Expected the start of an expression" in
utest errOf "[1,]" with "1:3-1:4: Expected the start of an expression" in
utest errOf "{a = }" with "1:5-1:6: Expected the start of an expression" in
utest errOf "let a = 1" with "1:9-1:9: Expected \'in\' after the \'let\' declaration" in
utest errOf "lam" with "1:3-1:3: Expected \'.\' after the \'lam\' parameter" in
utest errOf "match a" with "1:7-1:7: Expected \'with\' after the \'match\' target expression" in
utest errOf "match a with 1" with "1:14-1:14: Expected \'then\' or \'in\' after the \'match ... with <pattern>\'" in
utest errOf "match a with 1 then b else" with "1:26-1:26: Expected the start of an expression" in
utest errOf "utest" with "1:5-1:5: Expected the start of an expression" in
utest errOf "utest a with" with "1:12-1:12: Expected the start of an expression" in
utest errOf "switch" with "1:6-1:6: Expected the start of an expression" in
utest errOf "switch a" with "1:8-1:8: Expected \'case\' or \'end\' in a \'switch\' expression" in
utest errOf "switch a case 1" with "1:15-1:15: Expected \'then\' after the \'case\' pattern" in
utest errOf "if" with "1:2-1:2: Expected the start of an expression" in
utest errOf "if true then 1" with "1:14-1:14: Expected \'else\' after the \'if ... then\' branch" in
utest errOf "type in x" with "1:5-1:7: Expected a type identifier after \'type\'" in
utest errOf "con in x" with "1:4-1:6: Expected a constructor identifier after \'con\'" in
utest errOf "external in x" with "1:9-1:11: Expected an identifier after \'external\'" in
utest errOf "use in x" with "1:4-1:6: Expected a language identifier after \'use\'" in
utest errOf "x." with "1:2-1:2: Expected a field label (an identifier or integer) after \'.\'" in

-------------------------------------------------------------------------
-- Programs
-------------------------------------------------------------------------

utest progStrOf "mexpr\n1" with
[ "mexpr"
, "1" ] in

utest progSpansOf "mexpr\n1" with
[ "expr 2:0-2:1" ] in

utest progStrOf "let x = 1\nmexpr\nx" with
[ "let x = 1"
, "mexpr"
, "x" ] in

utest progSpansOf "let x = 1\nmexpr\nx" with
[ "decl 1:0-1:9"
, "expr 1:8-1:9"
, "expr 3:0-3:1" ] in

utest progStrOf "lang Foo\n  syn Expr =\n  | CInt Int\n  sem eval =\n  | CInt n -> n\nend\nmexpr\n1" with
[ "lang Foo"
, "  syn Expr ="
, "  | CInt Int"
, "  sem eval ="
, "  | CInt n ->"
, "    n"
, "end"
, "mexpr"
, "1" ] in

utest progSpansOf "lang Foo\n  syn Expr =\n  | CInt Int\n  sem eval =\n  | CInt n -> n\nend\nmexpr\n1" with
[ "decl 1:0-6:3"
, "decl 2:2-3:12"
, "decl 4:2-5:15"
, "pat 5:4-5:10"
, "pat 5:9-5:10"
, "expr 5:14-5:15"
, "expr 8:0-8:1" ] in

utest progStrOf "lang Foo = Bar + Baz\nend\nmexpr\n1" with
[ "lang Foo ="
, "  Bar"
, "  + Baz"
, "end"
, "mexpr"
, "1" ] in

utest progSpansOf "lang Foo = Bar + Baz\nend\nmexpr\n1" with
[ "decl 1:0-2:3"
, "expr 4:0-4:1" ] in

utest progStrOf "lang Foo\n  sem f (x: Int) =\n  | 1 -> x\nend\nmexpr\n1" with
[ "lang Foo"
, "  sem f (x : Int) ="
, "  | 1 ->"
, "    x"
, "end"
, "mexpr"
, "1" ] in

utest progSpansOf "lang Foo\n  sem f (x: Int) =\n  | 1 -> x\nend\nmexpr\n1" with
[ "decl 1:0-4:3"
, "decl 2:2-3:10"
, "pat 3:4-3:5"
, "expr 3:9-3:10"
, "expr 6:0-6:1" ] in

utest progStrOf "include \"foo.mc\"\ntype T = Int\ncon C: Int\nexternal ext: Int\nutest 1 with 1\nmexpr\nx" with
[ "include \"foo.mc\""
, "type T ="
, "  Int"
, "con C: Int"
, "external ext : Int"
, "utest 1"
, "with 1"
, "mexpr"
, "x" ] in

utest progSpansOf "include \"foo.mc\"\ntype T = Int\ncon C: Int\nexternal ext: Int\nutest 1 with 1\nmexpr\nx" with
[ "decl 1:0-1:16"
, "decl 2:0-2:12"
, "decl 3:0-3:10"
, "decl 4:0-4:17"
, "decl 5:0-5:14"
, "expr 5:6-5:7"
, "expr 5:13-5:14"
, "expr 7:0-7:1" ] in

utest progStrOf "recursive\n  let f = lam x. x\nend\nmexpr\nf" with
[ "recursive"
, "  let f = lam x."
, "      x"
, "mexpr"
, "f" ] in

utest progSpansOf "recursive\n  let f = lam x. x\nend\nmexpr\nf" with
[ "decl 1:0-3:3"
, "expr 2:10-2:18"
, "expr 2:17-2:18"
, "expr 5:0-5:1" ] in

-------------------------------------------------------------------------
-- What a malformed program reports, and where
-------------------------------------------------------------------------

utest progErrOf "1" with "1:0-1:1: Expected the start of a declaration" in
utest progErrOf "lang" with "1:4-1:4: Expected an identifier after \'lang\'" in
utest progErrOf "lang Foo" with "1:8-1:8: Expected the start of a declaration" in
utest progErrOf "lang Foo =\nend\nmexpr\n1" with "2:0-2:3: Expected an included language identifier after \'+\'" in
utest progErrOf "lang Foo\n  syn Expr\nend\nmexpr\n1" with "3:0-3:3: Expected \'=\' or \'+=\' after the \'syn\' name and parameters" in

()
