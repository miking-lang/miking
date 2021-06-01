include "ocaml/ast.mc"

let extTestBatteriesMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("batteriesZero", [
      { ident = "BatInt.zero", ty = tyint_, libraries = ["batteries"] }
    ])
  ]
