include "ocaml/ast.mc"

let mathExtMap =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("exp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ , libraries = [] }
    ]),
    ("atan", [
      { ident = "Float.atan", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("sin", [
      { ident = "Float.sin", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("cos", [
      { ident = "Float.cos", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("externalAtan2", [
      { ident = "Float.atan2",
        ty = tyarrows_ [tyfloat_, tyfloat_, tyfloat_],
        libraries = [] }
    ])
  ]
