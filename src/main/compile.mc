-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

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
include "tuning/context-expansion.mc"
include "tuning/tune-file.mc"
include "jvm/compile.mc"
include "peval/compile.mc"
include "mexpr/generate-pprint.mc"
include "mexpr/generate-utest.mc"

include "mexpr/invariants/in-scope.mc"
include "mexpr/invariants/definitions.mc"
include "mexpr/invariants/info.mc"

lang MCoreCompile =
  BootParser +
  MExprHoles +
  MExprCmp +
  KeywordMakerOpaque +
  MExprSym + MExprRemoveTypeAscription + MExprTypeCheck +
  MExprUtestGenerate + MExprRuntimeCheck + MExprProfileInstrument + MExprTypeAnnot +
  MExprPrettyPrint +
  MExprLowerNestedPatterns +
  MExprConstantFold +
  OCamlTryWithWrap + MCoreCompileLang + PhaseStats +
  SpecializeCompile +
  OldDPrintViaPprint + MExprGeneratePprint + GeneratePprintMissingCase +
  PprintTyAnnot + HtmlAnnotator +
  MExprToJson +
  ComposedMLangLoader + DPrintViaPprintLoader + StripUtestLoader + UtestLoader +
  MExprGenerateEq +

  UnboundErrorAttr + DefinedAttr + WithoutInfoAttr
  sem mkInvariantAttrs : () -> [Attr Loc]
  sem mkInvariantAttrs = | _ ->
    let scope =
      {_scopeEmpty () with tyConstructors = setOfSeq nameCmp (mapValues builtinTypeNames)} in
    [ InScopeAttr (filledThunk scope)
    , UnboundErrorAttr (mkThunk (lazyPure "UnboundErrorAttr#root"))
    , WithoutInfoAttr (mkThunk (lazyPure "WithoutInfoAttr#root"))
    , DefinedAttr (mkThunk (lazyPure "DefinedAttr#root"))
    ]
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
    let log = mkPhaseLogState options.debugDumpPhases options.debugPhases mkInvariantAttrs in

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

let compileViaLoader = lam options : Options. lam sourcePath.
  use MCoreCompile in
  let log = mkPhaseLogState options.debugDumpPhases options.debugPhases mkInvariantAttrs in

  let loader = mkLoader typcheckEnvDefault [] in
  endPhaseStatsProg log "mkLoader" {decls = getDecls loader, expr = unit_};

  let loader =
    if options.runTests then
      let filename = stdlibResolveFileOr (lam x. error x) "." sourcePath in
      let keepUtestIf = lam x.
        if x.static
        then match x.info with Info x
          then eqString x.filename filename
          else true
        else true in
      enableUtestGeneration keepUtestIf loader
    else addHook loader (StripUtestHook ()) in
  endPhaseStatsProg log
    (if options.runTests then "enable utests" else "disable utests")
    {decls = getDecls loader, expr = unit_};

  let loader = if options.debugDprint
    then enableDPrintViaPprint loader
    else loader in
  endPhaseStatsProg log
    (if options.debugDprint then "enable dprint-via-pprint" else "disable dprint-via-pprint")
    {decls = getDecls loader, expr = unit_};

  -- TODO(vipa, 2026-08-14): Original parsing also can prune external utests and do something about mexprExtendedKeywords
  -- TODO(vipa, 2026-08-14): insertTunedOrDefaults?
  -- TODO(vipa, 2026-08-14): Print AST if options.debugParse?

  -- TODO(vipa, 2026-08-14): if options.debugProfile, insert instrumentation for profiling

  let loader = (includeFileTypeExn (FMCore {includeMExpr = true}) "." sourcePath loader).1 in
  endPhaseStatsProg log "includeFileExn" {decls = getDecls loader, expr = unit_};

  let ast = buildFullAst loader in
  endPhaseStatsExpr log "buildFullAst" ast;

  let ast = removeMetaVarExpr ast in
  endPhaseStatsExpr log "removeMetaVarExpr" ast;

  (if options.debugTypeCheck then
    printLn (use TyAnnotFull in annotateMExpr ast);
    endPhaseStatsExpr log "debug-type-check" ast
   else ());

  -- TODO(vipa, 2026-08-14): compileSpecialize
  -- TODO(vipa, 2026-08-14): if options.runtimeChecks, injectRuntimeChecks
  -- TODO(vipa, 2026-08-14): if options.enableConstantFold and not options.disableOptimizations, constantFold
  -- TODO(vipa, 2026-08-14): if options.debugConstantFold, print ast

  let ast = lowerAll ast in
  endPhaseStatsExpr log "pattern-lowering" ast;
  (if options.debugShallow then
    printLn (expr2str ast) else ());

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
      -- let ast = typeAnnot ast in
      -- endPhaseStatsExpr log "type-annot" ast;
      -- -- If option --debug-type-annot, then pretty-print the AST
      -- (if options.debugTypeAnnot then printLn (expr2str ast) else ());
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
    iter (lam x. compileViaLoader options x; ()) files
  else
    let compileFile = lam file.
      let log = mkPhaseLogState options.debugDumpPhases options.debugPhases mkInvariantAttrs in
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

      -- Insert tuned values, or use default values if no .tune file present
      let ast = insertTunedOrDefaults options ast file in
      endPhaseStatsExpr log "tuning" ast;

      -- If option --debug-parse, then pretty print the AST
      (if options.debugParse then printLn (expr2str ast) else ());

      compileWithUtests options file ast; ()
    in
    iter compileFile files
