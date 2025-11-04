-- # Rendering Types and Utilities
--
-- This module defines the core types and utilities used to represent and render source code for display purposes
--
-- It abstracts the notion of source code into a tree structure and enables rendering with or
-- without previews (e.g., collapsible code sections).

include "../extracting/objects.mc"

-- This structure holds all the formatted code data related to a single source object.
--
-- - `left`: the code segment before the split point (e.g., `let x`)
-- - `right`: the code segment after the split (e.g., `= 42`)
-- - `trimmed`: extra comments and separators of the code.
-- - `obj`: the original object the code comes from
type RenderingData = {
    left : String,
    right : String,
    trimmed : String,
    row: String,
    obj: Object,
    tests: String,
    rowTests: String
}

-- An abstract tree representation of source code. It supports:
type TreeSourceCode

-- A formatted code node, created from a `RenderingData` record.
-- Typically used for child objects that were already rendered.    
con TreeSourceCodeNode : RenderingData -> TreeSourceCode -- Formated code

-- A raw snippet of `SourceCodeWord`s that has not yet been rendered.
-- Typically represents a sequence of tokens like `let x =`.
con TreeSourceCodeSnippet : [SourceCodeWord] -> TreeSourceCode -- Array of not formated word
