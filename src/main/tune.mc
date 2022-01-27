
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "compile.mc"
include "options.mc"
include "sys.mc"
include "parse.mc"
include "tuning/context-expansion.mc"
include "tuning/hole-cfa.mc"
include "tuning/dependency-analysis.mc"
include "tuning/instrumentation.mc"
include "tuning/tune.mc"

lang MCoreTune =
  BootParser +
  MExprHoles + MExprHoleCFA + DependencyAnalysis + Instrumentation + MExprTune
end

let tableFromFile = lam file.
  if fileExists file then tuneFileReadTable file
  else error (join ["Tune file ", file, " does not exist"])

let dumpTable = lam file. lam env. lam table.
  let destination = tuneFileName file in
  tuneFileDumpTable destination env table

let dependencyAnalysis
  : TuneOptions -> CallCtxEnv -> Expr -> (DependencyGraph, Expr) =
  lam options : TuneOptions. lam env : CallCtxEnv. lam ast.
    use MCoreTune in
    if options.dependencyAnalysis then
      let ast = use HoleANFAll in normalizeTerm ast in
      let cfaRes = cfaData (graphDataFromEnv env) ast in
      let dep = analyzeDependency env cfaRes ast in
      (dep, ast)
    else assumeFullDependency env ast

let tune = lam files. lam options : Options. lam args.

  let tuneOptions : TuneOptions = options.tuneOptions in

  let tuneFile = lam file.
    use MCoreTune in
    let ast = parseParseMCoreFile {
      keepUtests = options.runTests,
      pruneExternalUtests = not options.disablePruneExternalUtests,
      pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
      findExternalsExclude = true,
      keywords = holeKeywords
    } file in
    let ast = makeKeywords [] ast in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = use HoleANF in normalizeTerm ast in

    -- Do coloring of call graph for maintaining call context
    match colorCallGraph [] ast with (env, ast) in

    -- Perform dependency analysis
    match dependencyAnalysis tuneOptions env ast with (dep, ast) in

    -- Instrument the program
    match instrument env dep ast with (instRes, ast) in

    -- Context expand the holes
    match contextExpand env ast with (r, ast) in

    -- If option --tuned is given, then use tune file as defaults
    let table =
      if options.useTuned then tableFromFile (tuneFileName file) else r.table in

    -- Compile the program and write to temporary directory
    let binary = ocamlCompileAstWithUtests
      {options with output = Some (sysJoinPath r.tempDir "tune")} file ast in

    -- Do the tuning
    let result = tuneEntry binary tuneOptions env dep instRes r in

    -- Write the best found values to filename.tune
    tuneFileDumpTable (tuneFileName file) (Some env) result;

    -- If option --compile is given, then compile the program using the
    -- tuned values
    (if options.compileAfterTune then
      compile [file] {options with useTuned = true} args
     else ());

    -- If option --enable-cleanup is given, then remove the tune file
    (if tuneOptions.cleanup then sysDeleteFile (tuneFileName file) else ());

    -- Clean up temporary files used during tuning
    r.cleanup ();
    instRes.cleanup ()
  in
  iter tuneFile files
