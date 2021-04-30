include "ocaml/ast.mc"

let mathExtMap =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("exp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("atan", [
      { ident = "Float.atan", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("sin", [
      { ident = "Float.sin", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("cos", [
      { ident = "Float.cos", ty = tyarrow_ tyfloat_ tyfloat_ }
    ])
  ]
