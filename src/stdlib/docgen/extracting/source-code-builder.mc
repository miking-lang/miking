-- # Code Source Reconstruction Utilities
--
-- This module implements a minimalist system to reconstruct the source code
-- associated with each `Object` in the documentation tree.
-- 
-- To see the logic of source-code representation, see source-code.mc


include "../parsing/doc-tree.mc"
include "./source-code.mc"
include "../global/logger.mc"

-- An empty source code
let sourceCodeEmpty : () -> SourceCode = lam . []
        
-- ## SourceCodeBuilder
--
-- Accumulates source code tokens while traversing the `DocTree`.
-- When entering a `DocTreeNode`, a new builder context is pushed.
-- When finishing a node, the buffer is returned and the parent context is restored.
type SourceCodeBuilder
con SourceCodeNode : { parent: Option SourceCodeBuilder, buffer: SourceCode } -> SourceCodeBuilder
    
-- ## absorbWord
--
-- Adds a token from the `DocTree` to the current builder.
-- - If the word is a `Leaf`, it's added as `Some word`.
-- - If the word is a `Node`, we inject a `None {}` into the parent
--   and start a fresh buffer for the child node.
let absorbWord : SourceCodeBuilder -> DocTree -> SourceCodeBuilder =
    use TokenReader in lam builder. lam word.
    match builder with SourceCodeNode { buffer = buffer, parent = parent } in
    let token = (match word with DocTreeNode { token = token } | DocTreeLeaf { token = token } | DocTreeIncludeNode { token = token } in token) in
    let token = sourceCodeWordFormat token in
    switch word
    case DocTreeNode {} then
        let buffer = cons (None {}) buffer in
        let parent = SourceCodeNode { parent = parent, buffer = buffer } in
        SourceCodeNode { parent = Some parent, buffer = [Some token] }
    case DocTreeLeaf {} | DocTreeIncludeNode {} then
        let buffer = cons (Some token) buffer in
        SourceCodeNode { parent = parent, buffer = buffer }
    end

-- ## finish
--
-- Completes the current builder scope and returns:
-- - the restored parent builder
-- - the reversed buffer containing the current block's source
let finish : SourceCodeBuilder -> { builder: SourceCodeBuilder, sourceCode: SourceCode } = lam builder.
    match builder with SourceCodeNode { parent = Some parent, buffer = buffer } then
        match parent with SourceCodeNode { parent = parent, buffer = parentBuffer  } in
        { builder = SourceCodeNode { parent = parent, buffer = parentBuffer }, sourceCode = reverse buffer }
    else match builder with SourceCodeNode { buffer = buffer } in
        extractingWarn "finish: Builder parent should never be empty at this point";
        { builder = builder, sourceCode = reverse buffer }

-- Returns a new SourceCodeBuilder
let newSourceCodeBuilder : () -> SourceCodeBuilder = lam . SourceCodeNode { buffer = [], parent = None {} }

