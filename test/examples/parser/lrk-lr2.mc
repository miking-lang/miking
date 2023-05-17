-- A grammar that is not LR(1)
--   S -> R S | R
--   R -> , <name> T
--   T -> , | <uint> |

include "common.mc"
include "ext/file-ext.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "parser/lrk.mc"

lang LRParser_NonLL = LRParser
                    + LIdentTokenParser
                    + UIntTokenParser
                    + CommaTokenParser
                    + MExprPrettyPrint
end

mexpr

use LRParser_NonLL in

let _S = nameSym "S" in
let _R = nameSym "R" in
let _T = nameSym "T" in

let tokTy = tyrecord_ [("info", tycon_ "Info")] in
let inttokTy = tyrecord_ [("info", tycon_ "Info"), ("val", tycon_ "Int")] in
let identtokTy = tyrecord_ [("info", tycon_ "Info"), ("val", tycon_ "String")] in

let tokenConTypes = mapFromSeq tokReprCmp [
  (EOFRepr {}, {conIdent = nameNoSym "EOFTok", conArg = tokTy}),
  (CommaRepr {}, {conIdent = nameNoSym "CommaTok", conArg = tokTy}),
  (IntRepr {}, {conIdent = nameNoSym "IntTok", conArg = inttokTy}),
  (LIdentRepr {}, {conIdent = nameNoSym "LIdentTok", conArg = identtokTy})
] in

let syntaxdef: SyntaxDef = {
  entrypoint = _S,
  productions = [
    {nt = _S, terms = [NonTerminal _R, NonTerminal _S],
     action = withType (tyarrows_ [tyunit_, tystr_, tyseq_ tystr_, tyseq_ tystr_])
                       (ulams_ ["actionState", "a1_R", "a2_S"]
                               (cons_ (var_ "a1_R") (var_ "a2_S")))},
    {nt = _S, terms = [NonTerminal _R],
     action = withType (tyarrows_ [tyunit_, tystr_, tyseq_ tystr_])
                       (ulams_ ["actionState", "a1_R"]
                               (seq_ [var_ "a1_R"]))},
    {nt = _R, terms = [Terminal (CommaRepr {}), Terminal (LIdentRepr {}), NonTerminal _T],
     action = withType (tyarrows_ [tyunit_, tokTy, identtokTy, tyint_, tystr_])
                       (ulams_ ["actionState", "a1_Comma", "a2_Ident", "a3_T"]
                               (appf1_ (var_ "join") (seq_ [
                                  recordproj_ "val" (var_ "a2_Ident"),
                                  str_ ": ",
                                  appf1_ (var_ "int2string") (var_ "a3_T")
                                ])))},
    {nt = _T, terms = [Terminal (CommaRepr {})],
     action = withType (tyarrows_ [tyunit_, tokTy, tyint_])
                       (ulams_ ["actionState", "a1_Comma"]
                               (negi_ (int_ 2)))},
    {nt = _T, terms = [Terminal (IntRepr {})],
     action = withType (tyarrows_ [tyunit_, inttokTy, tyint_])
                       (ulams_ ["actionState", "a1_Int"]
                               (recordproj_ "val" (var_ "a1_Int")))},
    {nt = _T, terms = [],
     action = withType (tyarrows_ [tyunit_, tyint_])
                       (ulams_ ["actionState"]
                               (negi_ (int_ 1)))}
  ],
  initActionState = unit_
} in

switch lrCreateParseTable 2 tokenConTypes syntaxdef
case ResultErr {errors = errors} then
  errorSingle [] (join (mapValues errors))
case ResultOk {value = lrtable} then
  printLn (lrtable2string 2 lrtable);
  printLn "";
  let bindings = {lrDefaultGeneratorBindings () with
    v_stream = var_ "initLexerState",
    v_nextToken = var_ "wrappedNextToken"
  } in
  let parser = lrGenerateParser bindings lrtable in
  let program: String = strJoin "\n" [
    "include \"map.mc\"",
    "include \"result.mc\"",
    "include \"seq.mc\"",
    "include \"string.mc\"",
    "include \"mexpr/info.mc\"",
    "include \"parser/lexer.mc\"",
    "let seq2string = lam s: [String]. snoc (cons '[' (strJoin \", \" s)) ']'",
    "mexpr",
    "use Lexer in",
    "let wrappedNextToken = lam s. result.ok (nextToken s) in",
    expr2str (bindall_ [
      let_ "initLexerState" (tycon_ "Stream")
                        (urecord_ [("pos", appf1_ (var_ "initPos") (str_ "file")),
                                   ("str", get_ (var_ "argv") (int_ 1))]),
      let_ "parse_result" (tyTm parser) parser,
      matchall_ [
        matchex_ (var_ "parse_result") (pcon_ "ResultOk" (prec_ [("value", (pvar_ "result"))])) (
          appf1_ (var_ "printLn") (appf1_ (var_ "join") (seq_ [
            str_ "success: ", appf1_ (var_ "seq2string") (var_ "result")
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
  let fname = "lrk-lr2-gen.mc" in
  match writeOpen fname with Some wc then
    writeString wc program;
    printLn (join ["Generated parser as \"", fname, "\""])
  else
    printLn (join ["Could not open the file \"", fname, "\""])
end



