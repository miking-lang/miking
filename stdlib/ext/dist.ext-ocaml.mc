

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
    ]),
    ("bernoulliSample", [
      { ident = "Boot.Dist.bernoulliSample",
        ty = tyarrow_ tyfloat_ tyint_ , libraries = ["owl"] }
    ]),
    ("bernoulliPDF", [
      { ident = "Boot.Dist.bernoulliPDF",
        ty = tyarrow_ tyint_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ]),
    ("bernoulliLogPDF", [
      { ident = "Boot.Dist.bernoulliLogPDF",
        ty = tyarrow_ tyint_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ]),
    ("binomialSample", [
      { ident = "Boot.Dist.binomialSample",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyint_ tyint_) , libraries = ["owl"] }
    ]),
    ("binomialPDF", [
      { ident = "Boot.Dist.binomialPDF",
        ty = tyarrow_ tyint_ (tyarrow_ tyfloat_ (tyarrow_ tyint_ tyfloat_)) , libraries = ["owl"] }
    ]),
    ("binomialLogPDF", [
      { ident = "Boot.Dist.binomialLogPDF",
        ty = tyarrow_ tyint_ (tyarrow_ tyfloat_ (tyarrow_ tyint_ tyfloat_)) , libraries = ["owl"] }
    ]),
    ("betaSample", [
      { ident = "Boot.Dist.betaSample",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ]),
    ("betaPDF", [
      { ident = "Boot.Dist.betaPDF",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)) , libraries = ["owl"] }
    ]),
    ("betaLogPDF", [
      { ident = "Boot.Dist.betaLogPDF",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)) , libraries = ["owl"] }
    ]),
    ("exponentialSample", [
      { ident = "Boot.Dist.exponentialSample",
        ty = tyarrow_ tyfloat_ tyfloat_ , libraries = ["owl"] }
    ]),
    ("exponentialPDF", [
      { ident = "Boot.Dist.exponentialPDF",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ]),
    ("exponentialLogPDF", [
      { ident = "Boot.Dist.exponentialLogPDF",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ])
  ]
