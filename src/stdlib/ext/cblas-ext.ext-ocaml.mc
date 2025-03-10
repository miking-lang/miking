include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["boot", "owl"], cLibraries = [] }

let cblasExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("cblasRowMajor", [
      impl {
        expr = "Owl_cblas_basic.CblasRowMajor",
        ty = otyopaque_
      }
    ]),
    ("cblasColMajor", [
      impl {
        expr = "Owl_cblas_basic.CblasColMajor",
        ty = otyopaque_
      }
    ]),
    ("cblasLayoutEq", [
      impl {
        expr = "(fun (x : Owl_cblas_basic.cblas_layout) (y : Owl_cblas_basic.cblas_layout) -> x = y)",
        ty = tyarrows_ [otyopaque_, otyopaque_, tybool_]
      }
    ]),
    ("cblasNoTrans", [
      impl {
        expr = "Owl_cblas_basic.CblasNoTrans",
        ty = otyopaque_
      }
    ]),
    ("cblasTrans", [
      impl {
        expr = "Owl_cblas_basic.CblasTrans",
        ty = otyopaque_
      }
    ]),
    ("cblasConjTrans", [
      impl {
        expr = "Owl_cblas_basic.CblasConjTrans",
        ty = otyopaque_
      }
    ]),
    ("cblasTransEq", [
      impl {
        expr = "(fun (x : Owl_cblas_basic.cblas_transpose) (y : Owl_cblas_basic.cblas_transpose) -> x = y)",
        ty = tyarrows_ [otyopaque_, otyopaque_, tybool_]
      }
    ]),
    ("cblasUpperTriag", [
      impl {
        expr = "Owl_cblas_basic.CblasUpper",
        ty = otyopaque_
      }
    ]),
    ("cblasLowerTriag", [
      impl {
        expr = "Owl_cblas_basic.CblasLower",
        ty = otyopaque_
      }
    ]),
    ("cblasTriagEq", [
      impl {
        expr = "(fun (x : Owl_cblas_basic.cblas_uplo) (y : Owl_cblas_basic.cblas_uplo) -> x = y)",
        ty = tyarrows_ [otyopaque_, otyopaque_, tybool_]
      }
    ]),
    ("cblasNonUnitDiag", [
      impl {
        expr = "Owl_cblas_basic.CblasNonUnit",
        ty = otyopaque_
      }
    ]),
    ("cblasUnitDiag", [
      impl {
        expr = "Owl_cblas_basic.CblasUnit",
        ty = otyopaque_
      }
    ]),
    ("cblasDiagEq", [
      impl {
        expr = "(fun (x : Owl_cblas_basic.cblas_diag) (y : Owl_cblas_basic.cblas_diag) -> x = y)",
        ty = tyarrows_ [otyopaque_, otyopaque_, tybool_]
      }
    ]),
    ("cblasLeftSide", [
      impl {
        expr = "Owl_cblas_basic.CblasLeft",
        ty = otyopaque_
      }
    ]),
    ("cblasRightSide", [
      impl {
        expr = "Owl_cblas_basic.CblasRight",
        ty = otyopaque_
      }
    ]),
    ("cblasSideEq", [
      impl {
        expr = "(fun (x : Owl_cblas_basic.cblas_side) (y : Owl_cblas_basic.cblas_side) -> x = y)",
        ty = tyarrows_ [otyopaque_, otyopaque_, tybool_]
      }
    ]),
    ("externalCblasAxpy", [
      impl {
        expr = "Owl_cblas_basic.axpy",
        ty = tyall_ "a" (tyarrows_ [
          tyint_, tyvar_ "a", otyopaque_, tyint_, otyopaque_, tyint_, otyunit_])
      }
    ]),
    ("externalCblasCopy", [
      impl {
        expr = "Owl_cblas_basic.copy",
        ty = (tyarrows_ [
          tyint_, otyopaque_, tyint_, otyopaque_, tyint_, otyunit_])
      }
    ]),
    ("externalCblasScal", [
      impl {
        expr = "Owl_cblas_basic.scal",
        ty = tyall_ "a" (tyarrows_ [
          tyint_, tyvar_ "a", otyopaque_, tyint_, otyunit_])
      }
    ]),
    ("externalCblasGemv", [
      impl {
        expr = "Owl_cblas_basic.gemv",
        ty = tyall_ "a" (tyarrows_ [
          otyopaque_, otyopaque_,
          tyint_, tyint_,
          tyvar_ "a",
          otyopaque_, tyint_,
          otyopaque_, tyint_,
          tyvar_ "a",
          otyopaque_, tyint_,
          otyunit_
        ])
      }
    ]),
    ("externalCblasGemm", [
      impl {
        expr = "Owl_cblas_basic.gemm",
        ty = tyall_ "a" (tyarrows_ [
          otyopaque_, otyopaque_, otyopaque_,
          tyint_, tyint_, tyint_,
          tyvar_ "a",
          otyopaque_, tyint_,
          otyopaque_, tyint_,
          tyvar_ "a",
          otyopaque_, tyint_,
          otyunit_
        ])
      }
    ])
  ]
