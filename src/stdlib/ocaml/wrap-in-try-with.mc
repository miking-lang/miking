-- Defines a language fragment which wraps an OCaml AST in a try-with
-- expression that captures exceptions thrown in the generated OCaml code and
-- prints an MExpr-specific error message along with the OCaml exception and
-- its backtrace. The backtraces are always enabled and printed for uncaught
-- exceptions, so when this is applied the user does not need to use the
-- OCAMLRUNPARAM=b to enable it.

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/ast.mc"

lang OCamlTryWithWrap = MExprAst + OCamlAst
  sem wrapTopInTryWith (acc : (Expr, [Top])) =
  | (OTopVariantTypeDecl _ | OTopCExternalDecl _) & t ->
    (acc.0, snoc acc.1 t)
  | OTopLet t ->
    let letExpr = TmLet {
      ident = t.ident, tyAnnot = t.tyBody, tyBody = t.tyBody, body = t.body,
      inexpr = unit_, ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()} in
    (bind_ acc.0 letExpr, acc.1)
  | OTopRecLets t ->
    let toRecLetBinding = lam bind : OCamlTopBinding.
      { ident = bind.ident, tyAnnot = bind.tyBody, tyBody = bind.tyBody
      ,  body = bind.body, info = NoInfo ()} in
    let recLetExpr = TmRecLets {
      bindings = map toRecLetBinding t.bindings, inexpr = unit_,
      ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()} in
    (bind_ acc.0 recLetExpr, acc.1)
  | OTopExpr t -> (bind_ acc.0 t.expr, acc.1)
  | OTopTryWith t -> error "Nested try-with expressions currently not supported"

  sem wrapInTryWith =
  | tops /- [Top] -/ ->
    match foldl wrapTopInTryWith (unit_, []) tops with (tryExpr, tops) in
    let enableBacktracesTop = OTopLet {
      ident = nameSym "",
      tyBody = TyRecord {fields = mapEmpty cmpSID, info = NoInfo ()},
      body = OTmExprExt {expr = "Printexc.record_backtrace true"}} in
    let excId = nameSym "exc" in
    let withExpr = bindall_ [
      ulet_ "" (appf2_ (OTmVarExt {ident = "Printf.printf"})
        (OTmString {text = "MExpr runtime error: %s\\n"})
        (app_ (OTmVarExt {ident = "Printexc.to_string"}) (nvar_ excId))),
      ulet_ "" (OTmExprExt {expr = "Printexc.print_backtrace Stdlib.stdout"}),
      OTmExprExt {expr = "Stdlib.exit 1"}] in
    let tryWithTop = OTopTryWith {
      try = tryExpr,
      arms = [(npvar_ excId, withExpr)]} in
    snoc (cons enableBacktracesTop tops) tryWithTop
end
