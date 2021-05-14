

include "ocaml/ast.mc"

let dist =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("externalGaussianSample", [
      { ident = "Owl_base_stats_dist_gaussian.gaussian_rvs",
        ty = tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_) , libraries = ["owl"] }
    ])
  ]
