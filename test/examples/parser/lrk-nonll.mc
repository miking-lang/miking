-- example of something that is not LL-parsable
-- L = { (^m )^n | forall n >= 0, forall m >= n}

include "common.mc"
include "ext/file-ext.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "parser/lrk.mc"

lang LRParser_NonLL = LRParser
                    + BracketTokenParser
                    + MExprPrettyPrint
end

mexpr

use LRParser_NonLL in

let _LeftRight = nameSym "LeftRight" in
let _LeftOnly = nameSym "LeftOnly" in

let tokTy = tyrecord_ [("info", tycon_ "Info")] in

let tokenConTypes = mapFromSeq tokReprCompare [
  (EOFRepr {}, {conIdent = nameNoSym "EOFTok", conArg = tokTy}),
  (LParenRepr {}, {conIdent = nameNoSym "LParenTok", conArg = tokTy}),
  (RParenRepr {}, {conIdent = nameNoSym "RParenTok", conArg = tokTy})
] in

let syntaxdef: LRSyntaxDef = {
  entrypoint = _LeftOnly,
  rules = [
    {name = _LeftOnly, terms = [LRTerminal (LParenRepr {}), LRNonTerminal _LeftOnly],
     action = withType (tyarrows_ [tyunit_, tokTy, tystr_, tystr_])
                       (ulams_ ["actionState", "lparen", "lprod"]
                               (cons_ (char_ '(') (var_ "lprod")))},
    {name = _LeftOnly, terms = [LRNonTerminal _LeftRight],
     action = withType (tyarrows_ [tyunit_, tystr_, tystr_])
                       (ulams_ ["actionState", "lrprod"]
                               (cons_ (char_ '|') (var_ "lrprod")))},
    {name = _LeftRight, terms = [LRTerminal (LParenRepr {}), LRNonTerminal _LeftRight, LRTerminal (RParenRepr {})],
     action = withType (tyarrows_ [tyunit_, tokTy, tystr_, tokTy, tystr_])
                       (ulams_ ["actionState", "lparen", "middle", "rparen"]
                               (cons_ (char_ '(') (snoc_ (var_ "middle") (char_ ')'))))},
    {name = _LeftRight, terms = [],
     action = withType (tyarrows_ [tyunit_, tystr_])
                       (ulams_ ["actionState"]
                               (str_ "e"))}
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
    "mexpr",
    "use Lexer in",
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
  let fname = "lrk-nonll-gen.mc" in
  match writeOpen fname with Some wc then
    writeString wc program;
    printLn (join ["Generated parser as \"", fname, "\""])
  else
    printLn (join ["Could not open the file \"", fname, "\""])
end



