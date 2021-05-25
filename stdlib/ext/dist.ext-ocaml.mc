

include "ocaml/ast.mc"

let dist =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("gaussianSample", [
      { ident = "Boot.Dist.gaussianSample",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ])
  ]
