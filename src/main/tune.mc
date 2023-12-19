
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
  BootParser + MExprTypeCheck +
  MExprHoles + MExprHoleCFA + NestedMeasuringPoints + DependencyAnalysis +
  Instrumentation + MExprTune
end

let tableFromFile = lam file.
  if fileExists file then tuneFileReadTable file
  else error (join ["Tune file ", file, " does not exist"])

let dependencyAnalysis
  : use MCoreTune in Options -> CallCtxEnv -> Expr -> (DependencyGraph, Expr) =
  lam options : Options. lam env : CallCtxEnv. lam ast.
    use MCoreTune in
    if options.tuneOptions.dependencyAnalysis then
      let ast = typeCheck ast in
      let ast = use HoleANFAll in normalizeTerm ast in
      let cfaRes = holeCfa (graphDataInit env) ast in
      let cfaRes = analyzeNested env cfaRes ast in
      let dep = analyzeDependency env cfaRes ast in
      (if options.tuneOptions.debugDependencyAnalysis then
         match pprintCode 0 pprintEnvEmpty ast with (pprintEnv, astStr) in
         printLn astStr;
         match cfaGraphToString pprintEnv cfaRes with (pprintEnv, resStr) in
         printLn resStr
       else ());
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
      eliminateDeadCode = not options.keepDeadCode,
      keywords = holeKeywords
    } file in
    let ast = makeKeywords ast in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (mexprToString ast) else ());

    let ast = symbolize ast in
    let ast = use HoleANF in normalizeTerm ast in

    -- Do coloring of call graph for maintaining call context
    match colorCallGraph [] ast with (env, ast) in

    -- Perform dependency analysis
    match dependencyAnalysis options env ast with (dep, ast) in

    -- Instrument the program
    match instrument env dep ast with (instRes, ast) in

    -- If option --debug-instrumentation, then pretty print the instrumented AST
    (if tuneOptions.debugInstrumentation then printLn (mexprToString ast) else ());

    -- Context expand the holes
    match contextExpand env ast with (r, ast) in

    -- If option --debug-expansion, then pretty print the expanded AST
    (if tuneOptions.debugExpansion then printLn (mexprToString ast) else ());

    -- If option --tuned is given, then use tune file as defaults
    let table =
      if options.useTuned then tableFromFile (tuneFileName file) else r.table in

    -- Strip annotations before compiling
    let ast = stripTuneAnnotations ast in

    -- Compile the program and write to temporary directory
    let binary = compileWithUtests
      {options with output = Some (sysJoinPath r.tempDir "tune")} file ast in

    -- Do the tuning
    let result = tune binary tuneOptions env dep instRes r ast in

    -- Write the best found values to filename.tune
    tuneFileDumpTable (tuneFileName file) env result true;

    -- If option --compile is given, then compile the program using the
    -- tuned values
    (if options.compileAfterTune then
      compile [file] {options with useTuned = true} args
     else ());

    -- If option --enable-cleanup is given, then remove the tune file
    (if tuneOptions.cleanup then sysDeleteFile (tuneFileName file); () else ());

    -- Clean up temporary files used during tuning
    r.cleanup ();
    instRes.cleanup ()
  in
  iter tuneFile files
