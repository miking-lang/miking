-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "mi-lite.mc"
include "options.mc"
include "parse.mc"
include "mexpr/profiling.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-check.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/utesttrans.mc"
include "tuning/decision-points.mc"
include "tuning/tune-file.mc"
include "ocaml/ast.mc"
include "ocaml/mcore.mc"
include "ocaml/external-includes.mc"

lang MCoreCompile =
  BootParser +
  MExprHoles +
  MExprSym + MExprTypeAnnot + MExprTypeCheck + MExprUtestTrans +
  MExprProfileInstrument
end

let pprintMcore = lam ast.
  use MExprPrettyPrint in
  expr2str ast

let generateTests = lam ast. lam testsEnabled.
  use MCoreCompile in
  if testsEnabled then
    let ast = symbolize ast in
    let ast = typeAnnot ast in
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
      insert [] table ast
    else error (join ["Tune file ", tuneFile, " does not exist"])
  else default ast

let ocamlCompileAstWithUtests = lam options : Options. lam sourcePath. lam ast.
  use MCoreCompile in
    -- If option --debug-profile, insert instrumented profiling expressions
    -- in AST
    let ast =
      if options.debugProfile then instrumentProfiling (symbolize ast)
      else ast
    in

    -- If option --typecheck, type check the AST
    let ast = if options.typeCheck then typeCheck (symbolize ast) else ast in

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (symEnv, ast) then

      -- Re-symbolize the MExpr AST and re-annotate it with types
      let ast = symbolizeExpr symEnv ast in

      compileMCore ast
        { debugTypeAnnot = lam ast. if options.debugTypeAnnot then printLn (pprintMcore ast) else ()
        , debugGenerate = lam ocamlProg. if options.debugGenerate then printLn ocamlProg else ()
        , exitBefore = lam. if options.exitBefore then exit 0 else ()
        , compileOcaml = ocamlCompile options sourcePath
        }
    else never

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
      keywords = decisionPointsKeywords
    } file in
    let ast = makeKeywords [] ast in

    -- Insert tuned values, or use default values if no .tune file present
    let ast = insertTunedOrDefaults options ast file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (pprintMcore ast) else ());

    ocamlCompileAstWithUtests options file ast; ()
  in
  iter compileFile files
