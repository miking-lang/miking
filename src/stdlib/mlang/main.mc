-- The main file of the MLang pipline.
-- The semantic function `compileMLangToOcaml`, takes a filepath as input. 
-- It then puts the program at this file through the MLang pipeline and then
-- compiles it to OCaml.

include "result.mc"
include "fileutils.mc"
include "compile.mc"
include "sys.mc"
include "map.mc"

include "compile.mc"
include "boot-parser.mc"
include "ast-builder.mc"
include "symbolize.mc"
include "composition-check.mc"
include "include-handler.mc"
include "language-composer.mc"
include "const-transformer.mc"
include "postprocess.mc"

include "mexpr/eval.mc"
include "mexpr/builtin.mc"
include "mexpr/ast-builder.mc"
include "mexpr/phase-stats.mc"
include "mexpr/pprint.mc"

lang MLangPipeline = MLangCompiler + BootParserMLang + 
                     MLangSym + MLangCompositionCheck +
                     MExprPrettyPrint + MExprEval + MExprEq + 
                     MLangConstTransformer + MLangIncludeHandler +
                     PhaseStats + LanguageComposer + PostProcess

  sem myEval : Expr -> Expr
  sem myEval =| e ->
    eval (evalCtxEmpty ()) e 

  -- TODO: re-add 'eval' through mlang-pipelineO

  -- TODO: add node count for MLang programs to phase-stats
  sem compileMLangToOcaml options runner =| filepath ->
    let log = mkPhaseLogState options.debugPhases in

    let p = parseAndHandleIncludes filepath in 
    endPhaseStats log "parsing-include-handling" uunit_;

    let p = constTransformProgram builtin p in
    endPhaseStats log "const-transformation" uunit_;

    let p = composeProgram p in 
    endPhaseStats log "language-inclusion-generation" uunit_;

    match symbolizeMLang symEnvDefault p with (_, p) in 
    endPhaseStats log "symbolization" uunit_;

    match result.consume (checkComposition p) with (_, res) in 
    endPhaseStats log "composition-check" uunit_;

    switch res 
      case Left errs then 
        iter raiseError errs ;
        never
      case Right env then
        let ctx = _emptyCompilationContext env in 
        let res = result.consume (compile ctx p) in 
        match res with (_, rhs) in 
        match rhs with Right expr in
        endPhaseStats log "mlang-mexpr-lower" expr;

        let expr = postprocess env.semSymMap expr in 
        endPhaseStats log "postprocess" expr;

        -- printLn (expr2str expr);

        runner options filepath expr;
        ()
    end
end