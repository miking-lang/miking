-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "accelerate.mc"
include "mi-lite.mc"
include "options.mc"
include "parse.mc"
include "mexpr/profiling.mc"
include "mexpr/runtime-check.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/utesttrans.mc"
include "mexpr/shallow-patterns.mc"
include "tuning/context-expansion.mc"
include "tuning/tune-file.mc"
include "ocaml/ast.mc"
include "ocaml/mcore.mc"
include "ocaml/external-includes.mc"
include "ocaml/wrap-in-try-with.mc"
include "javascript/compile.mc"
include "javascript/mcore.mc"
include "pmexpr/demote.mc"

lang MCoreCompile =
  BootParser +
  PMExprDemote +
  MExprHoles +
  MExprSym + MExprRemoveTypeAscription + MExprTypeCheck +
  MExprUtestTrans + MExprRuntimeCheck + MExprProfileInstrument +
  MExprPrettyPrint +
  MExprLowerNestedPatterns +
  OCamlTryWithWrap
end

let generateTests = lam ast. lam testsEnabled.
  use MCoreCompile in
  if testsEnabled then
    let ast = removeTypeAscription ast in
    utestGen ast
  else
    let symEnv = symEnvEmpty in
    (symEnv, utestStrip ast)

let insertTunedOrDefaults = lam options : Options. lam ast. lam file.
  use MCoreCompile in
  let ast = stripTuneAnnotations ast in
  if options.useTuned then
    let tuneFile = tuneFileName file in
    if fileExists tuneFile then
      let table = tuneFileReadTable tuneFile in
      let ast = symbolize ast in
      let ast = normalizeTerm ast in
      match colorCallGraph [] ast with (env, ast) in
      insert env table ast
    else error (join ["Tune file ", tuneFile, " does not exist"])
  else default ast

let compileWithUtests = lam options : Options. lam sourcePath. lam ast.
  use MCoreCompile in
    let ast = symbolize ast in

    -- If option --debug-profile, insert instrumented profiling expressions
    -- in AST
    let ast =
      if options.debugProfile then instrumentProfiling ast
      else ast
    in

    let ast = typeCheck ast in
    (if options.debugTypeCheck then
       printLn (join [expr2str ast, "\n : ", type2str (tyTm ast)]) else ());

    -- If --runtime-checks is set, runtime safety checks are instrumented in
    -- the AST. This includes for example bounds checking on sequence
    -- operations.
    let ast = if options.runtimeChecks then injectRuntimeChecks ast else ast in

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (symEnv, ast) in

    -- Re-symbolize the MExpr AST and re-annotate it with types
    let ast = symbolizeExpr symEnv ast in

    let ast = lowerAll ast in
    (if options.debugShallow then
      printLn (expr2str ast) else ());

    if options.toJavaScript then compileMCoreToJS {
        compileJSOptionsEmpty with
        targetPlatform = parseJSTarget options.jsTarget,
        generalOptimizations = not options.disableJsGeneralOptimizations,
        tailCallOptimizations = not options.disableJsTCO
      } ast sourcePath
    else compileMCore ast
      { debugTypeAnnot = lam ast. if options.debugTypeAnnot then printLn (expr2str ast) else ()
      , debugGenerate = lam ocamlProg. if options.debugGenerate then printLn ocamlProg else ()
      , exitBefore = lam. if options.exitBefore then exit 0 else ()
      , postprocessOcamlTops = lam tops. if options.runtimeChecks then wrapInTryWith tops else tops
      , compileOcaml = ocamlCompile options sourcePath
      }

-- Main function for compiling a program
-- files: a list of files
-- options: the options structure to the main program
-- args: the program arguments to the executed program, if any
let compile = lam files. lam options : Options. lam args.
  use MCoreCompile in
  let compileFile = lam file.
    let ast = parseParseMCoreFile {
      keepUtests = options.runTests,
      pruneExternalUtests = not options.disablePruneExternalUtests,
      pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
      findExternalsExclude = true,
      eliminateDeadCode = not options.keepDeadCode,
      keywords = concat holeKeywords parallelKeywords
    } file in
    let ast = makeKeywords [] ast in

    -- Applies static and dynamic checks on the accelerated expressions, to
    -- verify that the code within them are supported by the accelerate
    -- backends.
    -- TODO(larshum, 2022-06-29): Rewrite compilation so that we don't
    -- duplicate symbolization and type-checking when compiling in debug mode.
    let ast =
      if options.debugAccelerate then
        let ast = symbolizeExpr keywordsSymEnv ast in
        let ast = typeCheck ast in
        let ast = removeTypeAscription ast in
        match checkWellFormedness options ast with (ast, _, _) in
        demoteParallel ast
      else demoteParallel ast in

    -- Insert tuned values, or use default values if no .tune file present
    let ast = insertTunedOrDefaults options ast file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    compileWithUtests options file ast; ()
  in
  if options.accelerate then compileAccelerate files options args
  else iter compileFile files
