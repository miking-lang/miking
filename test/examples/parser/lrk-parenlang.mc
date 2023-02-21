include "common.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "parser/lrk.mc"


lang LRParser_ParenLang = LRParser
                        + BracketTokenParser
                        + MExprPrettyPrint
end

mexpr

use LRParser_ParenLang in

let _Parens = nameSym "Parens" in

let tokenConTypes = mapFromSeq tokReprCompare [
  (EOFRepr {}, {conIdent = nameNoSym "EOFTok", conArg = tyunit_}),
  (LParenRepr {}, {conIdent = nameNoSym "LParenTok", conArg = tyunit_}),
  (RParenRepr {}, {conIdent = nameNoSym "RParenTok", conArg = tyunit_})
] in

let syntaxdef: LRSyntaxDef = {
  entrypoint = _Parens,
  rules = [
    {name = _Parens, terms = [LRTerminal (LParenRepr {}), LRNonTerminal _Parens, LRTerminal (RParenRepr {})],
     action = withType (tyarrows_ [tyunknown_, tyunit_, tystr_, tyunit_, tystr_])
                       (ulams_ ["actionState", "lparen", "middle", "rparen"]
                               (cons_ (char_ '(') (snoc_ (var_ "middle") (char_ ')'))))},
    {name = _Parens, terms = [],
     action = withType (tyarrows_ [tyunknown_, tystr_])
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
  printLn "\n\n";
  let parser = lrGenerateParser lrtable in
  printLn (expr2str parser);
  printLn "\n\n"
end
