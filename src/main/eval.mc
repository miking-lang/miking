-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "basic-types.mc"
include "bool.mc"
include "common.mc"
include "list.mc"
include "name.mc"
include "option.mc"
include "options-type.mc"
include "options.mc"
include "parse.mc"
include "seq.mc"

include "annotate.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/const-arity.mc"
include "mexpr/constant-fold.mc"
include "mexpr/demote-recursive.mc"
include "mexpr/eval-staged.mc"
include "mexpr/keywords.mc"
include "mexpr/mexpr.mc"
include "mexpr/phase-stats.mc"
include "mexpr/pprint.mc"
include "mexpr/profiling.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/type-lift.mc"
include "mexpr/utest-generate.mc"
include "peval/ast.mc"


lang ExtMCore =
  BootParser + MExpr + MExprTypeCheck + MExprRemoveTypeAscription +
  MExprTypeCheck + MExprTypeLift + MExprUtestGenerate +
  MExprProfileInstrument + MExprEvalS + MExprDemoteRecursive +
  SpecializeAst + PhaseStats

  sem updateArgv : [String] -> Expr -> Expr
  sem updateArgv args =
  | TmConst {val = CArgv ()} -> seq_ (map str_ args)
  | t -> smap_Expr_Expr (updateArgv args) t

end

lang TyAnnotFull = MExprPrettyPrint + TyAnnot + HtmlAnnotator
end

lang ConstantFoldExt = MExprConstantFold + MExprArity
end

-- Main function for evaluating a program using the interpreter
-- files: a list of files
-- options: the options structure to the main program
-- args: the program arguments to the executed program, if any
let eval = lam files. lam options : Options. lam args.
  use ExtMCore in
  let log =
    mkPhaseLogState options.debugDumpPhases options.debugPhases (lam. []) in
  let evalFile = lam file.
    let ast = parseParseMCoreFile {
      keepUtests = options.runTests,
      keywords = specializeKeywords,
      pruneExternalUtests = not options.disablePruneExternalUtests,
      pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
      findExternalsExclude = false, -- the interpreter does not support externals
      eliminateDeadCode = not options.keepDeadCode
    } file in
    endPhaseStatsExpr log "parsing" ast;

    let ast = makeKeywords ast in
    endPhaseStatsExpr log "make-keywords" ast;

    (if options.debugParse then printLn (mexprToString ast) else ());
    endPhaseStatsExpr log "debug-parse" ast;

    let ast = updateArgv args ast in
    endPhaseStatsExpr log "update-argv" ast;

    let ast = symbolize ast in
    endPhaseStatsExpr log "symbolize" ast;

    let ast =
      if not options.disableOptimizations then demoteRecursive ast
      else ast in
    endPhaseStatsExpr log "demote-recursive" ast;

    let ast =
      if options.debugProfile then instrumentProfiling ast
      else ast in
    endPhaseStatsExpr log "instrument-profiling" ast;

    let ast =
      removeMetaVarExpr
        (typeInferExpr
           {typcheckEnvDefault with
            disableConstructorTypes = not options.enableConstructorTypes}
           ast) in
    endPhaseStatsExpr log "type-check" ast;
    (if options.debugTypeCheck then
       printLn (use TyAnnotFull in annotateMExpr ast);
       endPhaseStatsExpr log "debug-type-check" ast
     else ());

    let ast = generateUtest options.runTests ast in
    endPhaseStatsExpr log "generate-utest" ast;

    let ast =
      if not options.disableOptimizations then
        use ConstantFoldExt in constantFold ast
      else ast in
    endPhaseStatsExpr log "constant-folding" ast;
    (if options.debugConstantFold then printLn (expr2str ast) else ());
    endPhaseStatsExpr log "debug-constant-folding" ast;

    let cs = if options.debugStackTrace then Some (ref (callstackInit ()))
             else None () in
    let eval = evalSStageExpr cs ast in
    endPhaseStatsExpr log "stage-eval" ast;

    if options.exitBefore then exit 0
    else eval (Nil ()); () in
  iter evalFile files
