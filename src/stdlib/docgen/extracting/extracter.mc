-- # Extracter: generates ObjectTree from DocTree
--
-- This module implements the extractor:
-- - input: a parsed `DocTree`
-- - output: an `ObjectTree` representing documentation content
--
-- The parsing phase produces a `DocTree`, which is a relatively minimal structure
-- that captures the layout of the code. In the extracting phase, we transform this
-- `DocTree` into an `ObjectTree`. Objects also form a tree, with sub-objects, but
-- they carry more semantic information than the `DocTree`.
--
-- In this phase, look-ahead is allowed: we may inspect as many upcoming nodes
-- (children or descendants) of the current node as needed.
--
-- To compute the documentation of each object—the part we care about most—we must
-- capture the comments immediately above the block. We maintain a **comment buffer**
-- during extraction. Each time we encounter a comment, we add it to the buffer.
-- When we encounter something other than a comment, three cases apply:
--   * It is a `DocTree` node -> the buffer becomes the node’s documentation, then we clear it.
--   * It is a separator with **fewer than 2 newlines** -> we keep the buffer unchanged.  
--     This matters for indented constructs: documentation comments are often indented
--     and separated by whitespace. However, if the separator contains **more than one**
--     newline, we clear the buffer because it represents a break.
--   * Anything else -> we clear the buffer.
--
-- For each `DocTreeNode`, we inspect its `state` and compute the object (and its metadata)
-- from the children. For each object, we also compute a **name** and a **namespace**:
-- 1. **Name** — obtained from children if the node is a `let` (the next word), or from
--    the extraction context (e.g., utest names are numbered via a counter incremented
--    for each new utest).
-- 2. **Path** — the hierarchical location of an object. Example:
--    ```
--    let x = let y = 2 in 3
--    ```
--    If the code above is in `foo.mc`, the path of `x` is `foo.mc/`, and the path
--    of `y` is `foo.mc/x/`.
-- 3. **Extension** — a personalized extension based on the object kind, computed with
--    the Object API. This extension is necessary to distinguish
--    the folder that contains an object’s subelements from the object’s documentation
--    file itself.
--    Returning to the example, the full namespace of `x` is `foo.mc/x.let`, and `y`
--    is `foo.mc/x/y.let`. The final documentation file then ends with `.html` or `.md`
--    depending on the requested output format.

include "../parsing/parser.mc"
include "../parsing/doc-tree.mc"
include "../global/logger.mc"

include "../global/logger.mc"

include "fileutils.mc"

include "./util.mc"
include "./objects.mc"
include "./source-code-builder.mc"
include "./depth.mc"
        
-- Takes a tree and builds the objects
-- Comment buffer tracks consecutive comments between tokens
-- If a newline separator is hit, the buffer is cleared
let extract : Logger -> DocTree -> Option Int -> ObjectTree =
    use TokenReader in use BreakerChooser in use ObjectKinds in
    lam log. lam tree. lam depth.
    log "Beggining of extraction...";

     -- Entry point: tree must be Program node
    match tree with DocTreeNode { token = TokenProgram { content = content, includeSet = includeSet }, state = StateProgram {} } then
    let prefix = includeSetPrefix includeSet in
    
    -- Buffer of collected comments
    type CommentBuffer = [String] in

    -- Output of one extractRec step
    type ExtractRecOutput = { obj: Option ObjectTree, commentBuffer: CommentBuffer, sourceCodeBuilder: SourceCodeBuilder, utestCount: Int } in

    recursive
    let extractRec : (DocTree -> String -> CommentBuffer -> SourceCodeBuilder -> Bool -> Int -> Depth -> ExtractRecOutput ) =
    lam tree. lam namespace. lam commentBuffer. lam sourceCodeBuilder. lam inStdlib. lam utestCount. lam depth.

        let shouldClear : String -> Bool = lam content. gti (count (eqChar '\n') content) 1 in
        let sourceCodeBuilder = absorbWord sourceCodeBuilder tree in
        
        let defaultObject = lam namespace. lam isStdlib.
            let defaultObject = objWithNamespace defaultObject namespace in
            let defaultObject = objWithIsStdlib defaultObject isStdlib in
            if isStdlib then defaultObject else objWithPrefix defaultObject prefix
        in
    
        switch tree 
        case DocTreeNode { children = children, token = token, state = state } then

            -- Builds doc string from comments
            let buildDoc : [String] -> String = lam commentBuffer.
                let res = strJoin "  \n" (map (lam s. if strStartsWith " " s then s else cons ' ' s) commentBuffer) in
                match res with "" then "No documentation available here." else res in

            let finish : Object -> SourceCodeBuilder -> { builder: SourceCodeBuilder, obj: Object } = lam obj. lam sourceCodeBuilder.
                let sourceCode = finish sourceCodeBuilder in
                { obj = { obj with sourceCode = sourceCode.sourceCode }, builder = sourceCode.builder } in

            let obj = objWithIsStdlib (defaultObject namespace inStdlib) inStdlib in
            let doc = buildDoc (reverse commentBuffer) in

            -- Process children nodes
            let process : State -> [DocTree] -> String -> String -> String -> ObjectKind -> Int -> ExtractRecOutput =
                lam state. lam children. lam name. lam namespace. lam doc. lam kind. lam utestCount.
                
                let obj = { obj with name = name, kind = kind, doc = doc } in
                let obj = objWithNamespace obj namespace in
                match depthProcess depth obj with { obj = obj, depth = depth } in

                type Arg = { children: [ObjectTree], ctx: ExtractRecOutput } in
                let foldResult = foldl
                    (lam arg: Arg. lam s: DocTree.
                        let ctx = arg.ctx in
                        let ctx = extractRec s namespace ctx.commentBuffer ctx.sourceCodeBuilder inStdlib ctx.utestCount depth in
                        let children = match ctx.obj with Some obj then cons obj arg.children else arg.children in
                        { children = children, ctx = ctx })
                    { children = [], ctx = { commentBuffer = [], sourceCodeBuilder = sourceCodeBuilder, utestCount = utestCount, obj = None {} } }
                    children in
                    
                match finish obj foldResult.ctx.sourceCodeBuilder with { obj = obj, builder = sourceCodeBuilder } in
                let obj = ObjectNode { obj = obj, children = reverse foldResult.children } in
                { foldResult.ctx with obj = Some obj, sourceCodeBuilder = sourceCodeBuilder } in

            -- Dispatch by token type + state
            switch token case TokenWord { content = content } | TokenProgram { content = content } then
            switch state
            case StateProgram {} then
                recursive
                let extractProgramComments = lam children.
                    switch children
                    case [DocTreeLeaf { token = TokenComment { content = content } | TokenMultiLineComment { content = content } }] ++ rest then
                        let output = extractProgramComments rest in
                        { output with comments = cons content output.comments }
                    case [DocTreeLeaf { token = TokenSeparator { content = content } }] ++ rest then
                        if shouldClear content then { comments = [], children = children }
                        else extractProgramComments rest
                    case _ then { comments = [], children = children }
                    end
                in
                let extractRes = extractProgramComments children in
                process state children content content
                    (buildDoc extractRes.comments)
                    (ObjProgram {})
                    utestCount

            case StateMexpr {} then
                process state children "mexpr" (getNamespace namespace "mexpr" "") doc (ObjMexpr {}) utestCount

            case (StateUse {} | StateTopUse {}) then
                let name = getName children in
                let obj = { obj with name = name.word, kind = ObjUse {} } in
                let sourceCodeBuilder = foldl absorbWord sourceCodeBuilder children in
                match finish obj sourceCodeBuilder with { obj = obj, builder = sourceCodeBuilder } in
                { obj = Some (ObjectNode { obj = obj, children = [] }), commentBuffer = [], sourceCodeBuilder = sourceCodeBuilder, utestCount = utestCount }

            case StateTopUtest {} | StateUtest {} then
                let name = int2string utestCount in
                process state children name (getNamespace namespace name "utest") doc (ObjUtest {}) (addi utestCount 1)
            case StateRec {} | StateTopRec {} then
                process state children "" namespace doc (ObjRecursiveBloc {}) utestCount 
            case state then
                -- Look for '=' in children
                recursive let goToEqual = lam children.
                    switch nthWord children 0
                    case Some { word = "=", rest = rest } then rest
                    case Some { rest = rest } then goToEqual rest
                    case None {} then []
                    end in
                
                let name = getName children in
                let kind = switch state
                    case (StateLet {} | StateTopLet {} | StateRecLet {}) then
                        let rec = match state with StateLet {} | StateTopLet {} then false else true in
                        let children = goToEqual children in
                        let children = skipUseIn children in
                        -- Extract params if any
                        let args = extractParams children in
                        ObjLet { rec = rec, args = args, ty = None {} }
                    case StateSem {} then
                        ObjSem { langName = extractLastNamespaceElement namespace, variants = extractVariants (goToEqual children), ty = None {} }
                    case StateSyn {} then ObjSyn { langName = extractLastNamespaceElement namespace, variants = extractVariants (goToEqual children) }
                    case StateLang {} then ObjLang { parents = extractParents name.rest }
                    case (StateCon {} | StateTopCon {}) then
                        let t =
                            match nthWord name.rest 0 with Some { word = ":", rest = typedef } then
                                extractType (skipUseIn typedef)
                            else
                                extractingWarn (join ["The constructor ", name.word, " is typeless."]);
                                ""
                        in
                        ObjCon { t = t }

                    case (StateType {} | StateTopType {}) then
                        let t = match nthWord name.rest 0 with Some { word = "=", rest = typedef } then
                                Some (extractType typedef) else None {} in
                        ObjType { t = t }

                    end in
                let namespace = getNamespace namespace name.word (getFirstWord kind) in
                process state children name.word namespace doc kind utestCount
                end
            case _ then
               error (concat "Not covered: " (toString state))
            end
        case DocTreeLeaf { token = token, state = state } then
            let defaultRes = { commentBuffer = [], sourceCodeBuilder = sourceCodeBuilder, obj = None {}, utestCount = utestCount } in
            -- Leaf dispatch
            switch token
            case TokenComment { content = content } | TokenMultiLineComment { content = content }then
                { defaultRes with commentBuffer = cons content commentBuffer }
            case TokenSeparator { content = content } then
                -- Clear comment buffer if more than  one \n found
                if shouldClear content then defaultRes
                else { defaultRes with commentBuffer = commentBuffer }
            case TokenStr {} | TokenWord {} | TokenRecursiveEnder {} then defaultRes
            end
        case DocTreeIncludeNode  { token = TokenInclude { content = content }, state = state, tree = tree, path = path, isStdlib = isStdlib } then
            -- Load included file
            let defaultObject = defaultObject path isStdlib in
            let defaultObject = objWithKind defaultObject (ObjInclude { pathInFile = content }) in
            let defaultObject = objWithName defaultObject path in
            let emptyInclude = ObjectNode { obj = defaultObject, children = [] } in

            let defaultRes = { commentBuffer = [], sourceCodeBuilder = sourceCodeBuilder, obj = Some emptyInclude, utestCount = utestCount } in
            match tree with Some tree then
                log (concat "Extracting on: " path);
                let res = extractRec tree path [] (newSourceCodeBuilder ()) isStdlib utestCount depth in
                match res with { obj = Some (ObjectNode { obj = progObj, children = children } & progObjTree) } then
                    let includeObj = { progObj with renderIt = false, isStdlib = isStdlib, kind = ObjInclude { pathInFile = content }, sourceCode = sourceCodeEmpty () } in
                    
                    { defaultRes with obj = Some (ObjectNode { obj = includeObj, children = [ progObjTree ] })  }
                else
                    extractingWarn "Found a leaf at the root of a Program"; defaultRes
            else defaultRes
        end
    in

    let obj = match (extractRec tree content [] (newSourceCodeBuilder ()) false 0 (depthCreate depth)).obj with Some obj then
        obj
    else
        error "Extraction failed: extractRec returned None" in
    
    obj

    else error "Extraction failed: the top node of the output tree should always be a program."
