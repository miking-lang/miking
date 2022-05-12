-- Performs a well-formed check of a PMExpr AST. This ensures that:
-- * Sequences do not contain elements of functional type.
-- * The accumulator of a foldl and parallelReduce is not of functional type.
-- * The accumulator and the sequence elements of parallelReduce have the same
--   type.
--
-- These type checks assume that the provided AST is valid according to the
-- MExpr type checking.

include "pmexpr/ast.mc"

-- An extensible language fragment for defining well-formedness rules on
-- expressions.
lang WellFormed
  syn WellFormedError =

  -- Translates a well-formedness error node to a string by pretty-printing it.
  sem pprintWellFormedError : WellFormedError -> String

  -- Defines the well-formedness relation for an expression. A well-formed
  -- expression will return the accumulated sequence of errors, while one that
  -- is ill-formed will return the accumulator extended with errors
  -- corresponding to the failed well-formedness checks.
  sem wellFormedExprH : [WellFormedError] -> Expr -> [WellFormedError]

  -- Checks well-formedness within an AST node. The result is a possibly empty
  -- sequence of well-formedness errors.
  sem wellFormedExpr : Expr -> [WellFormedError]
  sem wellFormedExpr =
  | t -> reverse (wellFormedExprH [] t)

  sem wellFormedTypeH : [WellFormedError] -> Type -> [WellFormedError]

  sem wellFormedType =
  | t -> reverse (wellFormedTypeH [] t)

  sem wellFormed =
  | t ->
    let errors = wellFormedExpr t in
    if null errors then ()
    else
      let msg = strJoin "\n" (map pprintWellFormedError errors) in
      error (join ["Well-formedness check failed\n", msg])
end
