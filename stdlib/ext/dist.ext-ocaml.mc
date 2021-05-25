

include "ocaml/ast.mc"

let dist =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("gaussianSample", [
      { ident = "Boot.Dist.gaussianSample",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ]),
    ("gaussianPDF", [
      { ident = "Boot.Dist.gaussianPDF",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)) , libraries = ["owl"] }
    ]),
    ("gaussianLogPDF", [
      { ident = "Boot.Dist.gaussianLogPDF",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)) , libraries = ["owl"] }
    ])
  ]
