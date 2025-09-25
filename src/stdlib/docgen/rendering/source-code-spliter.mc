-- # source-code-spliter.mc
--
-- This module provides utilities to split source code into structured parts,
-- in order to support **syntax highlighting** and **collapsible code blocks** in the documentation.
--
-- ## Overview
-- Source code is represented as `TreeSourceCode` nodes (tokens or sub-blocks).
-- This module identifies logical split points (keywords, operators, etc.)
-- and separates the code into:
-- - **left**: code before the main split (e.g., `let x =`)
-- - **right**: code after the split (e.g., `3`)
-- - **trimmed**: trailing comments/separators that should not appear in the current block,
--   but instead be passed upwards in the tree reconstruction.
--
-- This design avoids recomputing syntax highlighting and ensures toggle buttons
-- and folding behavior can be preserved consistently.

include "../parsing/lexing/token-readers.mc"
include "./rendering-types.mc"


-- ## Trimmed
--
-- Represents what remains in the `right` side of the split, either raw or already formatted.
type Trimmed
con TrimmedFormated : String -> Trimmed
con TrimmedNotFormated : [SourceCodeWord] -> Trimmed

-- ## SourceCodeSplit
--
-- The result of a split operation.
-- - `left`: Code before the split (e.g., `let x =`)
-- - `right`: Code after the split (e.g., `3`)
-- - `trimmed`: The rest of the right side, composed of comments and separators
type SourceCodeSplit = { left: [TreeSourceCode], right: [TreeSourceCode], trimmed: Trimmed }


-- sourceCodeSplit
--
-- Splits a TreeSourceCode array into two parts, based on semantic keywords and delimiters.
-- - Recognizes patterns like `let x = ...`, `con T : ...`, etc.
-- - Special-cases `use`, `lang`, `utest`, etc.
--
-- Behavior:
-- - Detects key language constructs (`let`, `type`, `sem`, `con`, `lang`, etc.)
-- - Splits on their defining symbol (`=`, `:`, etc.)
-- - Handles special cases like `use`, `recursive`, `utest`, and `mexpr`
-- - Preserves trailing comments/separators separately in `trimmed`
let sourceCodeSplit : [TreeSourceCode] -> SourceCodeSplit = use TokenReader in lam arr.
    let finish = lam left. lam right.
        let rightRev = reverse right in
        switch rightRev
        case [TreeSourceCodeSnippet arr] ++ rightRev then
            let arr = reverse arr in
            match splitOnR (lam w. match w with { word = TokenMultiLineComment {} | TokenComment {} | TokenSeparator {} } then false else true) arr with
                { left = trimmedRight, right = trimmedLeft } in
            let trimmedLeft = TreeSourceCodeSnippet (reverse trimmedLeft) in
            let trimmedRight = TrimmedNotFormated (reverse trimmedRight) in
            { left = left, right = reverse (cons trimmedLeft rightRev), trimmed = trimmedRight }
        case [TreeSourceCodeNode data] ++ rightRev then
            let right = reverse (cons (TreeSourceCodeNode { data with trimmed = [] }) rightRev) in
            { left = left, right = right, trimmed = TrimmedFormated data.trimmed }
        case [] then { left = arr, right = [], trimmed = TrimmedNotFormated []}
        end 
    in

    let mergeAndFinish = lam left. lam right1. lam right2.
        finish [TreeSourceCodeSnippet left] (cons (TreeSourceCodeSnippet right1) right2) in
    match arr with [TreeSourceCodeSnippet buffer] ++ right then
        match buffer with [{ word = TokenWord {} } & x1] ++ rest then
    
        let splitAndReturn = lam split: String.
            match splitOnL (lam w. match w with { word = word } in eqString (lit word) split) rest with
                { left = left, right = rest } in
            mergeAndFinish (cons x1 left) rest right in
        switch content x1.word
        case "let" | "type" | "sem" | "syn" then splitAndReturn "="
        case "con" then splitAndReturn ":"
        case "use" | "recursive" then finish arr []
        case "utest" | "mexpr" then mergeAndFinish [x1] rest right
        case "lang" then
            match splitOnL (lam w. match w with { word = TokenWord {} } then true else false) rest with
                { left = left, right = rest } in
            mergeAndFinish (cons x1 left) rest right

        case _ then finish [] arr
        end
        else
            finish [] arr
    else finish [] arr
