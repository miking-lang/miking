-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "accelerate.mc"
include "mi-lite.mc"
include "options.mc"
include "parse.mc"
include "javascript/compile.mc"
include "javascript/mcore.mc"
include "mexpr/phase-stats.mc"
include "mexpr/profiling.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/runtime-check.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/utest-generate.mc"
include "mexpr/constant-fold.mc"
include "ocaml/ast.mc"
include "ocaml/external-includes.mc"
include "ocaml/mcore.mc"
include "ocaml/wrap-in-try-with.mc"
include "pmexpr/demote.mc"
include "tuning/context-expansion.mc"
include "tuning/tune-file.mc"
include "jvm/compile.mc"
include "mlang/main.mc"
include "peval/compile.mc"
include "mexpr/generate-pprint.mc"

include "extrec/main.mc"

lang MCoreCompile =
  BootParser +
  PMExprDemote +
  MExprHoles +
  MExprCmp +
  MExprSym + MExprRemoveTypeAscription + MExprTypeCheck +
  MExprUtestGenerate + MExprRuntimeCheck + MExprProfileInstrument + MExprTypeAnnot +
  MExprPrettyPrint +
  MExprLowerNestedPatterns +
  MExprConstantFold +
  OCamlTryWithWrap + MCoreCompileLang + PhaseStats +
  SpecializeCompile +
  OldDPrintViaPprint + MExprGeneratePprint + GeneratePprintMissingCase +
  PprintTyAnnot + HtmlAnnotator +
  MExprToJson
end

lang TyAnnotFull = MExprPrettyPrint + TyAnnot + HtmlAnnotator + MetaVarTypePrettyPrint
end

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
    let log = mkPhaseLogState options.debugDumpPhases options.debugPhases in

    -- If option --debug-profile, insert instrumented profiling expressions
    -- in AST
    let ast =
      if options.debugProfile then instrumentProfiling ast
      else ast
    in
    endPhaseStatsExpr log "instrument-profiling" ast;

    let ast = symbolize ast in
    endPhaseStatsExpr log "symbolize" ast;

    let ast =
      removeMetaVarExpr
        (typeCheckExpr
           {typcheckEnvDefault with
            disableConstructorTypes = not options.enableConstructorTypes}
           ast)
    in
    endPhaseStatsExpr log "type-check" ast;
    (if options.debugTypeCheck then
       printLn (use TyAnnotFull in annotateMExpr ast);
       endPhaseStatsExpr log "debug-type-check" ast
     else ());

    let ast = compileSpecialize ast in

    -- If --runtime-checks is set, runtime safety checks are instrumented in
    -- the AST. This includes for example bounds checking on sequence
    -- operations.
    let ast = if options.runtimeChecks then injectRuntimeChecks ast else ast in
    endPhaseStatsExpr log "runtime-checks" ast;

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    let ast = generateUtest options.runTests ast in
    endPhaseStatsExpr log "generate-utest" ast;

    let ast =
      if and (options.enableConstantFold) (not options.disableOptimizations)
      then constantFold ast else ast
    in
    endPhaseStatsExpr log "constant folding" ast;
    (if options.debugConstantFold then
      printLn (expr2str ast) else ());

    let ast = lowerAll ast in
    endPhaseStatsExpr log "pattern-lowering" ast;
    (if options.debugShallow then
      printLn (expr2str ast) else ());

    let ast = if options.debugDprint
      then dprintToPprint ast
      else ast in
    endPhaseStatsExpr log "dprintToPprint" ast;

    let res =
      if options.toJVM then compileMCoreToJVM ast else
      if options.toJavaScript then compileMCoreToJS
        { compileJSOptionsEmpty with
          targetPlatform = parseJSTarget options.jsTarget
        , output = options.output
        , generalOptimizations = not options.disableJsGeneralOptimizations
        , tailCallOptimizations = not options.disableJsTCO
        } ast sourcePath
      else
        let ast = typeAnnot ast in
        endPhaseStatsExpr log "type-annot" ast;
        -- If option --debug-type-annot, then pretty-print the AST
        (if options.debugTypeAnnot then printLn (expr2str ast) else ());
        compileMCore ast
        { debugGenerate = lam ocamlProg. if options.debugGenerate then printLn ocamlProg else ()
        , exitBefore = lam. if options.exitBefore then exit 0 else ()
        , postprocessOcamlTops = lam tops. if options.runtimeChecks then wrapInTryWith tops else tops
        , compileOcaml = ocamlCompile options sourcePath
        } in
    endPhaseStatsExpr log "backend" ast;
    res

-- Main function for compiling a program
-- files: a list of files
-- options: the options structure to the main program
-- args: the program arguments to the executed program, if any
let compile = lam files. lam options : Options. lam args.
  use MCoreCompile in

  if options.mlangPipeline then
    printLn " * WARNING: You are using an experimental, unstable pipeline.";
    use MLangPipeline in
    iter (compileMLangToOcaml options compileWithUtests) files
  else if options.experimentalRecords then
    printLn " * WARNING: You are using an experimental, unstable pipeline.";
    use BigPipeline in
    iter (compileExtendedMLangToOcaml options compileWithUtests) files
  else
    let compileFile = lam file.
      let log = mkPhaseLogState options.debugDumpPhases options.debugPhases in
      let ast = parseParseMCoreFile {
        keepUtests = options.runTests,
        pruneExternalUtests = not options.disablePruneExternalUtests,
        pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
        findExternalsExclude = true,
        eliminateDeadCode = not options.keepDeadCode,
        keywords = mexprExtendedKeywords
      } file in
      endPhaseStatsExpr log "parsing" ast;
      let ast = makeKeywords ast in
      endPhaseStatsExpr log "make-keywords" ast;

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
      endPhaseStatsExpr log "accelerate" ast;

      -- Insert tuned values, or use default values if no .tune file present
      let ast = insertTunedOrDefaults options ast file in
      endPhaseStatsExpr log "tuning" ast;

      -- If option --debug-parse, then pretty print the AST
      (if options.debugParse then printLn (expr2str ast) else ());

      compileWithUtests options file ast; ()
    in
    if options.accelerate then compileAccelerate files options args
    else iter compileFile files
