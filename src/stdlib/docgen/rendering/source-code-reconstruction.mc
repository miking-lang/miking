-- # Source Code Reconstruction
--
-- Rebuilds a structured `TreeSourceCode` from a flat `SourceCode` stream and a list of
-- pre-rendered children (`RenderingData`). Children are interleaved at `None` markers.

include "../extracting/source-code-builder.mc"
include "../extracting/source-code-word.mc"
include "../extracting/objects.mc"
include "./rendering-types.mc"

-- Reconstructs code by streaming tokens and inserting child blocks at separators.
-- Returns a list of `TreeSourceCode` nodes preserving original order and structure.
let reconstructSourceCode : SourceCode -> [RenderingData] -> [TreeSourceCode] = 
    lam code. lam children. use ObjectKinds in
    
    let children = filter (lam s. match s.obj.kind with ObjInclude {} then false else true) children in
    type Arg = {
        tree: [TreeSourceCode],
        children: [RenderingData],
        buffer: [SourceCodeWord]
    } in
    let tree = foldl (lam a: Arg. lam word: Option SourceCodeWord.
        switch word
        case Some w then { a with buffer = cons w a.buffer}
        case None {} then
            match a.children with [child] ++ children then
                match a.buffer with [] then
                    { a with tree = cons (TreeSourceCodeNode child) a.tree, children = children }
                else
                    { tree = concat [TreeSourceCodeNode child, TreeSourceCodeSnippet (reverse a.buffer)] a.tree, children = children, buffer = [] }
            else
                renderingWarn "Child array should not be empty at this point";
                a
        end) { tree = [], children = children, buffer = [] } code in
    (match tree.children with [] then () else renderingWarn "Not all children have been processed.");
    reverse (match tree.buffer with [] then tree.tree else cons (TreeSourceCodeSnippet (reverse tree.buffer)) tree.tree)
   
