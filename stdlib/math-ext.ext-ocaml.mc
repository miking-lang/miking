include "ocaml/ast.mc"

let mathExtMap =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("exp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ }
    ])
  ]
