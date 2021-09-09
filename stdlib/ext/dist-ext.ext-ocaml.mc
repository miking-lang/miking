

include "map.mc"
include "ocaml/ast.mc"

let distExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("myExternalExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ , libraries = [] }
    ])
  ]
