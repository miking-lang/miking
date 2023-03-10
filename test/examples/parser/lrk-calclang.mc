include "common.mc"
include "ext/file-ext.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "parser/lrk.mc"


lang LRParser_CalcLang = LRParser
                       + BracketTokenParser
                       + UIntTokenParser
                       + MExprPrettyPrint
  syn Token =
  | PlusTok {info : Info}
  | TimesTok {info : Info}
  syn TokenRepr =
  | PlusRepr ()
  | TimesRepr ()

  sem parseToken (pos : Pos) =
  | "+" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = PlusTok {info = info}, lit = "+", info = info, stream = {pos = pos2, str = str}}
  | "*" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = TimesTok {info = info}, lit = "+", info = info, stream = {pos = pos2, str = str}}

  sem tokKindEq (tokRepr : TokenRepr) =
  | PlusTok _ -> match tokRepr with PlusRepr _ then true else false
  | TimesTok _ -> match tokRepr with TimesRepr _ then true else false

  sem tokInfo =
  | PlusTok {info = info} -> info
  | TimesTok {info = info} -> info

  sem tokToStr =
  | PlusTok _ -> "<Plus>"
  | TimesTok _ -> "<Times>"

  sem tokReprToStr =
  | PlusRepr _ -> "<Plus>"
  | TimesRepr _ -> "<Times>"

  sem tokToRepr =
  | PlusTok _ -> PlusRepr ()
  | TimesTok _ -> TimesRepr ()
end

mexpr

use LRParser_CalcLang in

let _Expr = nameSym "Expr" in
let _Term = nameSym "Term" in
let _Factor = nameSym "Factor" in

let tokTy = tyrecord_ [("info", tycon_ "Info")] in
let tokUIntTy = tyrecord_ [("info", tycon_ "Info"), ("val", tyint_)] in

let tokenConTypes = mapFromSeq tokReprCompare [
  (EOFRepr {}, {conIdent = nameNoSym "EOFTok", conArg = tokTy}),
  (LParenRepr {}, {conIdent = nameNoSym "LParenTok", conArg = tokTy}),
  (RParenRepr {}, {conIdent = nameNoSym "RParenTok", conArg = tokTy}),
  (PlusRepr {}, {conIdent = nameNoSym "PlusTok", conArg = tokTy}),
  (TimesRepr {}, {conIdent = nameNoSym "TimesTok", conArg = tokTy}),
  (IntRepr {}, {conIdent = nameNoSym "IntTok", conArg = tokUIntTy})
] in

let syntaxdef: LRSyntaxDef = {
  entrypoint = _Expr,
  rules = [
    {name = _Expr, terms = [LRNonTerminal _Expr, LRTerminal (PlusRepr {}), LRNonTerminal _Term],
     action = withType (tyarrows_ [tyunit_, tystr_, tokTy, tystr_, tystr_])
                       (ulams_ ["actionState", "lexpr", "plusTok", "rterm"]
                               (appf1_ (var_ "join") (seq_ [
                                  str_ "PLUS(", var_ "lexpr", str_ ", ", var_ "rterm", str_ ")"
                                ])))},
    {name = _Expr, terms = [LRNonTerminal _Term],
     action = withType (tyarrows_ [tyunit_, tystr_, tystr_])
                       (ulams_ ["actionState", "term"] (var_ "term"))},
    {name = _Term, terms = [LRNonTerminal _Term, LRTerminal (TimesRepr {}), LRNonTerminal _Factor],
     action = withType (tyarrows_ [tyunit_, tystr_, tokTy, tystr_, tystr_])
                       (ulams_ ["actionState", "lterm", "plusTok", "rfactor"]
                               (appf1_ (var_ "join") (seq_ [
                                  str_ "TIMES(", var_ "lterm", str_ ", ", var_ "rfactor", str_ ")"
                                ])))},
    {name = _Term, terms = [LRNonTerminal _Factor],
     action = withType (tyarrows_ [tyunit_, tystr_, tystr_])
                       (ulams_ ["actionState", "factor"] (var_ "factor"))},
    {name = _Factor, terms = [LRTerminal (LParenRepr {}), LRNonTerminal _Expr, LRTerminal (RParenRepr {})],
     action = withType (tyarrows_ [tyunit_, tokTy, tystr_, tokTy, tystr_])
                       (ulams_ ["actionState", "lparen", "midexpr", "rparen"] (var_ "midexpr"))},
    {name = _Factor, terms = [LRTerminal (IntRepr {})],
     action = withType (tyarrows_ [tyunit_, tokUIntTy, tystr_])
                       (ulams_ ["actionState", "uint"]
                               (appf1_ (var_ "join") (seq_ [
                                  str_ "INT(", appf1_ (var_ "int2string") (recordproj_ "val" (var_ "uint")), str_ ")"
                                ])))}
  ],
  initActionState = unit_
} in

switch lrCreateParseTable 1 tokenConTypes syntaxdef
case ResultErr {errors = errors} then
  errorSingle [] (join (mapValues errors))
case ResultOk {value = lrtable} then
  printLn (lrtable2string 2 lrtable);
  printLn "";
  let parser = lrGenerateParser lrtable in
  let program: String = strJoin "\n" [
    "include \"map.mc\"",
    "include \"result.mc\"",
    "include \"seq.mc\"",
    "include \"string.mc\"",
    "include \"mexpr/info.mc\"",
    "include \"parser/lexer.mc\"",
"
lang PMLexer = Lexer
  syn Token =
  | PlusTok {info : Info}
  | TimesTok {info : Info}
  syn TokenRepr =
  | PlusRepr ()
  | TimesRepr ()

  sem parseToken (pos : Pos) =
  | \"+\" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = PlusTok {info = info}, lit = \"+\", info = info, stream = {pos = pos2, str = str}}
  | \"*\" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = TimesTok {info = info}, lit = \"+\", info = info, stream = {pos = pos2, str = str}}

  sem tokKindEq (tokRepr : TokenRepr) =
  | PlusTok _ -> match tokRepr with PlusRepr _ then true else false
  | TimesTok _ -> match tokRepr with TimesRepr _ then true else false

  sem tokInfo =
  | PlusTok {info = info} -> info
  | TimesTok {info = info} -> info

  sem tokToStr =
  | PlusTok _ -> \"<Plus>\"
  | TimesTok _ -> \"<Times>\"

  sem tokReprToStr =
  | PlusRepr _ -> \"<Plus>\"
  | TimesRepr _ -> \"<Times>\"

  sem tokToRepr =
  | PlusTok _ -> PlusRepr ()
  | TimesTok _ -> TimesRepr ()
end
",
    "mexpr",
    "use PMLexer in",
    "let wrappedNextToken = lam s. result.ok (nextToken s) in",
    expr2str (bindall_ [
      let_ "parse" (tyTm parser) parser,
      let_ "lexerState" (tycon_ "Stream")
                        (urecord_ [("pos", appf1_ (var_ "initPos") (str_ "file")),
                                   ("str", get_ (var_ "argv") (int_ 1))]),
      ulet_ "parse_result" (appf2_ (var_ "parse")
                                   (var_ "lexerState")
                                   (var_ "wrappedNextToken")),
      matchall_ [
        matchex_ (var_ "parse_result") (pcon_ "ResultOk" (prec_ [("value", (pvar_ "result"))])) (
          appf1_ (var_ "printLn") (appf1_ (var_ "join") (seq_ [
            str_ "success: \"", var_ "result", str_ "\""
          ]))
        ),
        matchex_ (var_ "parse_result") (pcon_ "ResultErr" (prec_ [("errors", (pvar_ "errors"))])) (
          appf1_ (var_ "printLn") (appf2_ (var_ "strJoin") (str_ "\n")
                                          (map_ (ulam_ "v" (
                                                  appf1_ (var_ "join") (seq_ [
                                                    str_ "Parse error at ",
                                                    appf1_ (var_ "info2str") (tupleproj_ 0 (var_ "v")),
                                                    str_ ": ",
                                                    tupleproj_ 1 (var_ "v")
                                                  ])
                                                ))
                                                (appf1_ (var_ "mapValues") (var_ "errors"))))
        )
      ]
    ]),
    ""
  ] in
  let fname = "lrk-calclang-gen.mc" in
  match writeOpen fname with Some wc then
    writeString wc program;
    printLn (join ["Generated parser as \"", fname, "\""])
  else
    printLn (join ["Could not open the file \"", fname, "\""])
end
