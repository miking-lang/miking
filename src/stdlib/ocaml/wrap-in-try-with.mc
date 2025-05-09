-- Defines a language fragment which wraps an OCaml AST in a try-with
-- expression that captures exceptions thrown in the generated OCaml code and
-- prints an MExpr-specific error message along with the OCaml exception and
-- its backtrace. The backtraces are always enabled and printed for uncaught
-- exceptions, so when this is applied the user does not need to use the
-- OCAMLRUNPARAM=b to enable it.

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/ast.mc"
include "either.mc"

lang OCamlTryWithWrap = MExprAst + OCamlAst
  sem wrapTopInTryWith : Top -> Either Decl Top
  sem wrapTopInTryWith =
  | (OTopVariantTypeDecl _ | OTopCExternalDecl _) & t ->
    Right t
  | OTopLet t ->
    let letDecl = DeclLet {
      ident = t.ident, tyAnnot = t.tyBody, tyBody = t.tyBody, body = t.body,
      info = NoInfo ()} in
    Left letDecl
  | OTopRecLets t ->
    let toDeclLetRecord = lam bind : OCamlTopBinding.
      { ident = bind.ident, tyAnnot = bind.tyBody, tyBody = bind.tyBody
      ,  body = bind.body, info = NoInfo ()} in
    let recLetDecl = DeclRecLets {bindings = map toDeclLetRecord t.bindings, info = NoInfo ()} in
    Left recLetDecl
  | OTopExpr t -> Left (nulet_ (nameSym "") t.expr)
  | OTopTryWith t -> error "Nested try-with expressions currently not supported"

  sem wrapInTryWith =
  | tops /- [Top] -/ ->
    match eitherPartition (map wrapTopInTryWith tops) with (decls, tops) in
    let enableBacktracesTop = OTopLet {
      ident = nameSym "",
      tyBody = TyRecord {fields = mapEmpty cmpSID, info = NoInfo ()},
      body = OTmExprExt {expr = "Printexc.record_backtrace true"}} in
    let excId = nameSym "exc" in
    let withExpr = bindall_ [
      ulet_ "" (appf2_ (OTmVarExt {ident = "Printf.printf"})
        (OTmString {text = "MExpr runtime error: %s\\n"})
        (app_ (OTmVarExt {ident = "Printexc.to_string"}) (nvar_ excId))),
      ulet_ "" (OTmExprExt {expr = "Printexc.print_backtrace Stdlib.stdout"})]
      (OTmExprExt {expr = "Stdlib.exit 1"}) in
    match decls with decls ++ [DeclLet {body = body}] in
    let tryWithTop = OTopTryWith {
      try = bindall_ decls body,
      arms = [(npvar_ excId, withExpr)]} in
    snoc (cons enableBacktracesTop tops) tryWithTop
end
