-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "accelerate.mc"
include "mi-lite.mc"
include "options.mc"
include "parse.mc"
include "mexpr/profiling.mc"
include "mexpr/runtime-check.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-check.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/utesttrans.mc"
include "tuning/context-expansion.mc"
include "tuning/tune-file.mc"
include "ocaml/ast.mc"
include "ocaml/mcore.mc"
include "ocaml/external-includes.mc"
include "ocaml/wrap-in-try-with.mc"
include "javascript/compile.mc"
include "pmexpr/demote.mc"

lang MCoreCompile =
  BootParser +
  PMExprDemote +
  MExprHoles +
  MExprSym + MExprTypeAnnot + MExprTypeCheck + MExprUtestTrans +
  MExprRuntimeCheck + MExprProfileInstrument +
  OCamlTryWithWrap
end

let pprintMcore = lam ast.
  use MExprPrettyPrint in
  expr2str ast

let generateTests = lam ast. lam testsEnabled. lam typeChecked.
  use MCoreCompile in
  if testsEnabled then
    let ast =
      if not typeChecked then typeAnnot (symbolize ast)
      else ast
    in
    let ast = removeTypeAscription ast in
    utestGen ast
  else
    let symEnv = symEnvEmpty in
    (symEnv, utestStrip ast)

let insertTunedOrDefaults = lam options : Options. lam ast. lam file.
  use MCoreCompile in
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
    -- If option --debug-profile, insert instrumented profiling expressions
    -- in AST
    let ast =
      if options.debugProfile then instrumentProfiling (symbolize ast)
      else ast
    in

    -- If option --typecheck, type check the AST
    let ast =
      if options.typeCheck then
        typeCheck (symbolizeExpr {symEnvEmpty with strictTypeVars = true} ast)
      else ast
    in

    -- If --runtime-checks is set, runtime safety checks are instrumented in
    -- the AST. This includes for example bounds checking on sequence
    -- operations.
    let ast = if options.runtimeChecks then injectRuntimeChecks ast else ast in

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests options.typeCheck with (symEnv, ast) in

    -- Re-symbolize the MExpr AST and re-annotate it with types
    let ast = symbolizeExpr symEnv ast in

    if options.toJavaScript then
      javascriptCompileFile ast sourcePath
    else compileMCore ast
      { debugTypeAnnot = lam ast. if options.debugTypeAnnot then printLn (pprintMcore ast) else ()
      , debugGenerate = lam ocamlProg. if options.debugGenerate then printLn ocamlProg else ()
      , exitBefore = lam. if options.exitBefore then exit 0 else ()
      , postprocessOcamlTops = lam tops. if options.runtimeChecks then wrapInTryWith tops else tops
      , compileOcaml = ocamlCompile sourcePath
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
      keywords = concat holeKeywords parallelKeywords
    } file in
    let ast = makeKeywords [] ast in

    -- Demote parallel constructs to sequential equivalents and remove
    -- accelerate terms
    let ast = demoteParallel ast in

    -- Insert tuned values, or use default values if no .tune file present
    let ast = insertTunedOrDefaults options ast file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (pprintMcore ast) else ());

    compileWithUtests options file ast; ()
  in
  if options.accelerate then compileAccelerate files options args
  else iter compileFile files
