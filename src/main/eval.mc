
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "options.mc"
include "parse.mc"
include "seq.mc"
include "name.mc"

include "mexpr/boot-parser.mc"
include "mexpr/ast-builder.mc"
include "mexpr/profiling.mc"
include "mexpr/symbolize.mc"
include "mexpr/mexpr.mc"
include "mexpr/builtin.mc"
include "mexpr/eval.mc"
include "mexpr/type-check.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/type-lift.mc"
include "mexpr/utest-generate.mc"
include "peval/ast.mc"


lang ExtMCore =
  BootParser + MExpr + MExprTypeCheck + MExprRemoveTypeAscription +
  MExprTypeCheck + MExprTypeLift + MExprUtestGenerate +
  MExprProfileInstrument + MExprEval + SpecializeAst

  sem updateArgv : [String] -> Expr -> Expr
  sem updateArgv args =
  | TmConst {val = CArgv ()} -> seq_ (map str_ args)
  | t -> smap_Expr_Expr (updateArgv args) t

end

lang TyAnnotFull = MExprPrettyPrint + TyAnnot + HtmlAnnotator
end

-- Main function for evaluating a program using the interpreter
-- files: a list of files
-- options: the options structure to the main program
-- args: the program arguments to the executed program, if any
let eval = lam files. lam options : Options. lam args.
  use ExtMCore in
  let evalFile = lam file.
    let ast = parseParseMCoreFile {
      keepUtests = options.runTests,
      keywords = specializeKeywords,
      pruneExternalUtests = not options.disablePruneExternalUtests,
      pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
      findExternalsExclude = false, -- the interpreter does not support externals
      eliminateDeadCode = not options.keepDeadCode
    } file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (mexprToString ast) else ());

    let ast = makeKeywords ast in

    let ast = symbolize ast in

    let ast =
      if options.debugProfile then
        instrumentProfiling ast
      else ast
    in

    let ast =
      removeMetaVarExpr
        (typeCheckExpr
           {typcheckEnvDefault with
            disableConstructorTypes = not options.enableConstructorTypes}
           ast)
    in
    (if options.debugTypeCheck then
       printLn (use TyAnnotFull in annotateMExpr ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    let ast = generateUtest options.runTests options.runSpecificTest ast in
    if options.exitBefore then exit 0
    else
      eval (evalCtxEmpty ()) (updateArgv args ast); ()
  in
  iter evalFile files
