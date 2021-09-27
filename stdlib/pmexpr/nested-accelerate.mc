-- Defines a language fragment that reports an error if nested accelerate terms
-- are used in the AST. This step assumes all accelerate terms have been
-- replaced with let-expressions, and that the AST has been lambda lifted.
--
-- This step assumes the pattern transformation, where recursion is eliminated,
-- at which point we know no recursive bindings remain in the program.

include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"

lang PMExprNestedAccelerate = PMExprAst
  sem _reportNestedAccelerateError =
  | info /- : Info -/ ->
    infoErrorExit info "Nested accelerate terms are not supported"

  sem containsMarkedTerm (marked : Set Name) (flag : Bool) =
  | TmVar t -> if flag then flag else setMem t.ident marked
  | t -> sfold_Expr_Expr (containsMarkedTerm marked) flag t

  sem reportNestedAccelerate (accelerated : Set Name) =
  | t ->
    let marked = reportNestedAccelerateH accelerated t in
    ()

  sem reportNestedAccelerateH (marked : Set Name) =
  | TmLet t ->
    let marked =
      if containsMarkedTerm marked false t.body then
        if setMem t.ident marked then
          _reportNestedAccelerateError t.info
        else setInsert t.ident marked
      else marked
    in
    reportNestedAccelerateH marked t.inexpr
  | t -> marked
end
