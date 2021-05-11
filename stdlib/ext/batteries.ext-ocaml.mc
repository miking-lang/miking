include "ocaml/ast.mc"

let batteries =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("batteriesZero", [
      { ident = "BatInt.zero", ty = tyint_, libraries = ["batteries"] }
    ])
  ]
