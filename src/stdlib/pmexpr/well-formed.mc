-- Applies static as well as dynamic well-formedness checks on a provided
-- accelerate AST. The definition of these checks and which guarantees they
-- provide depend on which backend it targets. The checks assume that the
-- provided AST has been type-checked.

include "pmexpr/ast.mc"

-- An extensible language fragment for defining well-formedness rules on
-- expressions.
lang WellFormed = Ast
  syn WFError =

  -- Defines a name for the well-formedness backend. This is used when
  -- reporting well-formedness errors.
  sem wellFormednessBackendName : () -> String

  -- Translates a well-formedness error node to an info-string tuple which can
  -- be passed to errorMulti.
  sem pprintWellFormedError : WFError -> (Info, String)

  -- Defines the well-formedness relation for an expression. A well-formed
  -- expression will return the accumulated sequence of errors, while one that
  -- is ill-formed will return the accumulator extended with errors
  -- corresponding to the failed well-formedness checks.
  sem wellFormedExprH : [WFError] -> Expr -> [WFError]

  -- Checks well-formedness within an AST node. The result is a possibly empty
  -- sequence of well-formedness errors.
  sem wellFormedExpr : Expr -> [WFError]
  sem wellFormedExpr =
  | t -> reverse (wellFormedExprH [] t)

  sem wellFormedTypeH : [WFError] -> Type -> [WFError]

  sem wellFormedType : Type -> [WFError]
  sem wellFormedType =
  | t -> reverse (wellFormedTypeH [] t)

  sem wellFormed : Expr -> ()
  sem wellFormed =
  | t ->
    let errors = wellFormedExpr t in
    if null errors then ()
    else
      let cmpSection = lam a. lam b.
        match (a, b) with ((i1, s1), (i2, s2)) in
        let c = infoCmp i1 i2 in
        if eqi c 0 then cmpString s1 s2 else c in
      let eqSection = lam a. lam b. eqi (cmpSection a b) 0 in
      let sections =
        distinctSorted
         eqSection
            (sort
              cmpSection
              (map pprintWellFormedError errors)) in
      let msg = join ["Well-formedness check failed for ",
                      wellFormednessBackendName (), " backend."] in
      errorMulti sections msg
end
