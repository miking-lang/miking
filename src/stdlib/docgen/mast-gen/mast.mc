-- # MAst Module
--
-- This module defines the MAst structure.
-- It contains the full Miking compiler expression along with the IncludeSet
-- storing the file contents.

include "mexpr/ast.mc"
include "./include-set.mc"
include "./parsing-file.mc"

-- Represents the Miking AST paired with its IncludeSet.
type MAst = use MExprAst in {
     expr: Expr,
     includeSet: IncludeSet ParsingFile
}
