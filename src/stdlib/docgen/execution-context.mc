include "./options/docgen-options.mc"
include "./options/cast-options.mc"
include "./scanning/scanner.mc"
include "./mast-gen/mast-generator.mc"
include "./parsing/parser.mc"
include "./naming/namer.mc"
include "./rendering/renderer.mc"
include "./server/server.mc"
include "docgen/parsing/token-readers.mc"
include "docgen/global/objects.mc"
include "basic-types.mc"
include "docgen/mast-gen/mast.mc"
include "docgen/scanning/scanning-output.mc"
include "docgen/naming/name-context.mc"
include "docgen/rendering/rendered-map.mc"
include "hashmap.mc"
include "docgen/global/logger.mc"
include "docgen/rendering/renderers/main-renderer.mc"
include "common.mc"
include "seq.mc"
include "string.mc"
include "docgen/global/util.mc"
include "docgen/rendering/renderers/objects-renderer.mc"

-- ExecutionContext is a mutable pipeline context.
-- Fields are progressively filled in the following order:
-- ast -> object -> nameContext -> renderedMap/searchDatas
-- Missing fields indicate that the corresponding pipeline step
-- has not been executed yet.
type ExecutionContext =
    use TokenReader in
    use Objects in {
    opt: DocGenOptions,
    userOutputFolder: String,
    currentFile: String,
    files: [FileToProcess],
    longestPrefix: String,

    ast: Option MAst,
    object: Option Object,
    nameContext: Option NameContext,

    renderedMap: RenderedMap,
    searchDatas: HashMap String String
}

let buildLogger : ExecutionContext -> String -> Logger =
    lam ctx. lam step.
    if ctx.opt.debug then message "[INFO]" step else lam. ()

-- Finalization step executed once after all files are processed.
let finalizeSearchIndex : ExecutionContext -> () =
    lam ctx.
    use Renderer in 
    let log = buildLogger ctx "Rendering" in 
    let ropt = getRenderingOption ctx.opt log (nameContextEmpty ()) (hashmapEmpty ()) in
    let ropt = { ropt with outDir = ctx.userOutputFolder } in
    let searchDatas = map (lam entry. { name = entry.0, link = entry.1 })
                      (hashmap2seq ctx.searchDatas) in
    renderSearchFile searchDatas ropt

let execCtxNext : ExecutionContext -> Option ExecutionContext =
    lam ctx.
    match ctx.files with [{ path = path, outDir = outDir }] ++ files then
          printLn (join ["Processing file ", path, "..."]);
          Some { ctx with
              ast = None {},
              object = None {},
              nameContext = None {},

              opt = { ctx.opt with outDir = outDir },
              currentFile = path,
              files = files
          }
    else
        finalizeSearchIndex ctx;
        printLn "Done!";
        None {}
        
let execContextNew : DocGenOptions -> Option ExecutionContext = lam opt.
    let scanningOptions = getScanningOptions opt in

    if opt.scanOnly then
        let scanRes = scan scanningOptions in -- Side effect only
        None {}
    else

    match scan scanningOptions with {
        inputs = files,
        longestPrefix = longestPrefix,
        onlyStdlib = onlyStdlib
    } in
    

    let lengthFile = length files in
    printLn (join ["About to process ", int2string lengthFile, " file", if eqi lengthFile 1 then "" else "s", "."]);
    let opt = if onlyStdlib then { opt with stdlibFolder = "" } else opt in

    let ctx = {
        opt = opt,
        currentFile = "",
        userOutputFolder = opt.outDir,
        longestPrefix = longestPrefix,
        files = files,
        renderedMap = renderedMapEmpty (),

        object = None {},
        ast = None {},
        nameContext = None {},
        searchDatas = hashmapEmpty ()
    } in
    execCtxNext ctx

-- Pipeline steps must be executed in the following order:
-- gen -> parse -> name -> render -> serve
let crash = lam miss. lam func. lam should.
    error (join [
        "Internal error: missing `", miss, "` in execution context.\n",
        "`", func, "` must be called after `", should, "`."
    ])
    
type Step = ExecutionContext -> ExecutionContext

let gen : Step = lam ctx.
    let log = buildLogger ctx "MExpr Generation" in
    let mast = buildMAstFromFile log ctx.currentFile in
    { ctx with ast = Some mast }

let parse : Step = lam ctx.
    match ctx.ast with Some ast then
    let log = buildLogger ctx "Parsing" in
    let opt = getParsingOptions log ctx.currentFile ctx.longestPrefix in
    let obj = parse opt ast in
    { ctx with object = Some obj }
    else crash "ast" "parse" "gen"

let name : Step =  lam ctx.
    match ctx.object with Some object then
    let log = buildLogger ctx "Naming" in
    let opt = getNamingOption ctx.opt in
    match name log opt object with {
        annotatedObj = annotatedObj,
        nameContext = nameContext
    } in
    { ctx with nameContext = Some nameContext, object = Some annotatedObj }
    else crash "object" "name" "extract"

-- After rendering a file, we may need to:
-- 1. Clean temporary source outputs
-- 2. Relocate stdlib files when rendering outside the user output folder
-- This is intentionally handled here to keep rendering side effects localized.
let render : Step =  lam ctx.
    match ctx.object with Some obj then
    match ctx.nameContext with Some nameContext then
    
    let log = buildLogger ctx "Rendering" in 
    let ropt = getRenderingOption { ctx.opt with outDir = ctx.userOutputFolder } log nameContext ctx.renderedMap in
    let renderingRes = render ropt obj in

    let searchDatas = foldl (lam acc. lam arg.
        hmInsert arg.name arg.link acc
    ) ctx.searchDatas renderingRes.searchDatas in
    
    (if neqString ctx.opt.outDir ctx.userOutputFolder then    
        let code = sysRemoveSrcFiles ctx.opt.outDir in
        (if neqi code 0 then renderingWarn "Failed to clean temporary source files." else ());

        if pathIsInStdlib ctx.longestPrefix then () else
        let newStdlibPath = normalizePath (join [ctx.opt.outDir, "/", ctx.opt.stdlibFolder]) in
        let actualStdlibPath = normalizePath (join [ctx.userOutputFolder, "/", ctx.opt.stdlibFolder]) in

        if isFolder newStdlibPath then
            let code = sysMoveDirContents actualStdlibPath newStdlibPath in
            if neqi code 0 then renderingWarn "Failed to move standard library contents." else ()
        else ()
    else ());

    { ctx with searchDatas = searchDatas, renderedMap = renderingRes.renderedMap }
    else crash "object" "render" "naming"
    else crash "name context" "render" "naming"

let serve : Step = use ObjectsRenderer in lam ctx.
    match ctx.object with Some obj then
    match ctx.nameContext with Some nameContext then
    let log = buildLogger ctx "Serving" in
    let opt = getRenderingOption ctx.opt log nameContext (hashmapEmpty ()) in -- Serving does not reuse renderedMap, so we give an empty one
    let link = objGetMyLink obj opt in

    let opt = getServeOption { ctx.opt with outDir = ctx.userOutputFolder } link in    
    startServer opt; ctx
    else crash "object" "serve" "render"
    else crash "name context" "serve" "name"    
