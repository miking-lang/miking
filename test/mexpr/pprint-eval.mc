-- Tests the pretty-printer by printing an AST, parsing it, evaluating it, and
-- making sure that the results match.

include "result.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/eval.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"

lang PPrintEvalTestLang = MExprAst
                        + MExprPrettyPrint
                        + MExprEval
                        + MExprTypeCheck
                        + MExprSym
                        + BootParser
                        + MExprEq
end

mexpr

use PPrintEvalTestLang in

let testAsts: [Expr] = [
  bindall_ [
    ulet_ "a" (int_ 5),
    ulet_ "b" (int_ 3),
    addi_ (var_ "a") (var_ "b")
  ],
  bindall_ [
    ulet_ "f" (ulam_ "x" (bindall_ [
      if_ (gti_ (var_ "x") (int_ 10)) ( --if
        subi_ (var_ "x") (int_ 10)
      ) (if_ (lti_ (var_ "x") (int_ 3)) ( -- else if
        addi_ (int_ 1000) (var_ "x")
      ) ( -- else
        muli_ (var_ "x") (var_ "x")
      ))
    ])),
    ulet_ "a" (appf1_ (var_ "f") (int_ 5)),
    ulet_ "b" (appf1_ (var_ "f") (int_ 1)),
    addi_ (var_ "a") (var_ "b")
  ]
] in

let symeval: Expr -> Expr = lam e: Expr.
  let e = symbolize e in
  let e = typeCheck e in
  eval (evalCtxEmpty ()) e
in

foldl (lam. lam sourceAst: Expr.
  let parseResult = parseMExprString defaultBootParserParseMExprStringArg
                                     (expr2str sourceAst)
  in (
    match parseResult with ResultOk {value = parsedAst} then
      let vRef    = symeval sourceAst in
      let vParsed = symeval parsedAst in
      utest vRef with vParsed using eqExpr in ()
    else
      utest "unexpected failure" with "" in ()
  )
) () testAsts

