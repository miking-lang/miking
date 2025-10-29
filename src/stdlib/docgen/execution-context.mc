-- # Execution Context
--
-- This module defines the `ExecutionContext`, the central state threaded through all
-- stages of the documentation generation pipeline.
--
-- ## ExecutionContext fields
-- - `opt`      : Parsed CLI options.
-- - `mainFile` : Path of the main input file.
-- - `tokens`   : Tokens from the lexer (not always used directly).
-- - `docTree`  : Parsed documentation tree, if available.
-- - `ast`      : The Miking AST, if generated.
-- - `object`   : The extracted object tree, if built.
--
-- ## Step functions
-- Each stage of the pipeline is a `Step = ExecutionContext -> ExecutionContext`.
-- - `gen`     : Build MAst from the main file.
-- - `parse`   : Build DocTree from MAst.
-- - `extract` : Extract ObjectTree from DocTree.
-- - `label`   : Label ObjectTree with semantic metadata.
-- - `render`  : Generate documentation files.
-- - `serve`   : Start preview server.
--
-- If a step is called out of order, the `crash` function raises an error with details.
--
-- The ExecutionContext also provides a logger for each steps.

include "./options/docgen-options.mc"
include "./options/cast-options.mc"
include "./mast-gen/mast-generator.mc"
include "./parsing/parser.mc"
include "./extracting/extracter.mc"
include "./labeling/labeler.mc"
include "./rendering/renderer.mc"
include "./server/server.mc"

type ExecutionContext =  use TokenReader in {    
    opt: DocGenOptions,
    mainFile: String,
    tokens: [Token],
    docTree : Option DocTree,
    ast: Option MAst,
    object: Option ObjectTree
}

let execContextNew : DocGenOptions -> ExecutionContext = lam opt.
    if sysFileExists opt.file then
    {
        opt = opt,
        mainFile = opt.file,
        tokens = [],
        docTree = None {},
        object = None {},
        ast = None {}
    }
    else error (join ["The file ", opt.file, "doesn't exist."])

let crash = lam miss. lam func. lam should.
    error (join ["Execution context: ", miss, " is missing in the exection context, ", func, " function should be called after having call the ", should, " function."])

let buildLogger : ExecutionContext -> String -> Logger = lam ctx. lam step. if ctx.opt.debug then message "INFO" step else lam. ()
    
type Step = ExecutionContext -> ExecutionContext

let gen : Step = lam ctx.
    let log = buildLogger ctx "MExpr Generation" in
    { ctx with ast = Some (buildMAstFromFile log ctx.mainFile) }

let parse : Step =  lam ctx.
    match ctx.ast with Some ast then
    let log = buildLogger ctx "Parsing" in
    { ctx with docTree = Some (parse log ctx.mainFile ast ) }
    else crash "ast" "parse" "gen"
    
let extract : Step =  lam ctx.
    match ctx.docTree with Some docTree then
    let log = buildLogger ctx "Extracting" in 
    { ctx with object = Some (extract log docTree ctx.opt.letDepth ) }
    else crash "doc tree" "extract" "parse"

let label : Step =  lam ctx.
    match (ctx.object, ctx.ast) with (Some object, Some ast) then
    let log = buildLogger ctx "Labeling" in    
    { ctx with object = Some (label log object ast) }
    else crash "object" "label" "extract"

let render : Step =  lam ctx.
    match ctx.object with Some obj then
    let log = buildLogger ctx "Rendering" in 
    let opt = getRenderingOption ctx.opt log in
    render opt obj; ctx
    else crash "object" "render" "label (or extract)"

let serve : Step = use ObjectsRenderer in lam ctx.
    match ctx.object with Some obj then
    let log = buildLogger ctx "Serving" in
    let opt = getRenderingOption ctx.opt log in
    let link = objLink (objTreeObj obj) opt in
    let opt = getServeOption ctx.opt link in    
    startServer opt; ctx
    else crash "object" "serve" "render"
