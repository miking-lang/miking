include "map.mc"
include "ocaml/ast.mc"

let matrixExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("externalMatrixExponential", [
      { expr = "Owl_linalg_generic.expm",
        ty = tyarrows_ [otygenarrayclayoutfloat_, otygenarrayclayoutfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalMatrixTranspose", [
      { expr = "Owl_dense.Matrix.D.transpose",
        ty = tyarrows_ [otygenarrayclayoutfloat_, otygenarrayclayoutfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalMatrixMulFloat", [
      { expr = "Owl_dense.Matrix.D.( $* )",
        ty = tyarrows_ [tyfloat_, otygenarrayclayoutfloat_, otygenarrayclayoutfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalMatrixMul", [
      { expr = "Owl_dense.Matrix.D.( *@ )",
        ty = tyarrows_ [otygenarrayclayoutfloat_, otygenarrayclayoutfloat_, otygenarrayclayoutfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalMatrixElemMul", [
      { expr = "Owl_dense.Matrix.D.( * )",
        ty = tyarrows_ [otygenarrayclayoutfloat_, otygenarrayclayoutfloat_, otygenarrayclayoutfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalMatrixElemAdd", [
    { expr = "Owl_dense.Matrix.D.( + )",
      ty = tyarrows_ [otygenarrayclayoutfloat_, otygenarrayclayoutfloat_, otygenarrayclayoutfloat_],
      libraries = ["owl"],
      cLibraries = []
    }
  ])
  ]
