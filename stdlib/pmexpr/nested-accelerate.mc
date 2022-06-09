-- Defines a function for checking whether nested accelerated expressions occur
-- within the program. This is currently not supported, so we explicitly
-- prevent it.
--
-- This can easily be checked after the extraction has taken place. The key
-- observation is that the accelerated expressions are the entry points of the
-- accelerated code, produced from extraction. Therefore, if the accelerated
-- code contains a call to one of these functions, the original program makes
-- use of nested acceleration.

include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"

let _nestedAccMsg = join [
  "The accelerated expression is used within another accelerated expression, ",
  "which is not supported."]

lang PMExprNestedAccelerate = PMExprAst
  sem checkIdentifiers : Set Name -> Expr -> ()
  sem checkIdentifiers env =
  | TmVar t ->
    if setMem t.ident env then
      errorSingle [t.info] _nestedAccMsg
    else ()
  | t -> sfold_Expr_Expr (lam. lam t. checkIdentifiers env t) () t

  sem containsNestedAccelerate : Set Name -> Expr -> ()
  sem containsNestedAccelerate env =
  | TmLet t ->
    checkIdentifiers env t.body;
    containsNestedAccelerate env t.inexpr
  | TmRecLets t ->
    iter (lam bind. checkIdentifiers env bind.body) t.bindings;
    containsNestedAccelerate env t.inexpr
  | TmType t -> containsNestedAccelerate env t.inexpr
  | TmConDef t -> containsNestedAccelerate env t.inexpr
  | TmUtest t -> containsNestedAccelerate env t.next
  | TmExt t -> containsNestedAccelerate env t.inexpr
  | _ -> ()

  sem checkNestedAccelerate : Set Name -> Expr -> ()
  sem checkNestedAccelerate accelerateIds =
  | t -> containsNestedAccelerate accelerateIds t
end
