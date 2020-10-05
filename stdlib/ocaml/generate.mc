include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"

lang OCamlGenerate = MExprAst + OCamlAst
  sem generate =
  | t -> smap_Expr_Expr generate t
end

lang OCamlTest = OCamlGenerate + OCamlPrettyPrint

mexpr

use OCamlTest in

generate (addi_ (int_ 1) (int_ 2))
