include "map.mc"
include "ocaml/ast.mc"

let mathExtMap =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("externalExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ , libraries = [] }
    ]),
    ("externalAtan", [
      { ident = "Float.atan", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("externalSin", [
      { ident = "Float.sin", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("externalCos", [
      { ident = "Float.cos", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("externalAtan2", [
      { ident = "Float.atan2",
        ty = tyarrows_ [tyfloat_, tyfloat_, tyfloat_],
        libraries = [] }
    ])
  ]
