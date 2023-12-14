include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["sundialsml"], cLibraries = [] }

let tyrealarray = otyvarext_ "Sundials.RealArray.t" []

let sundialsExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("nvectorSerialWrap", [
      impl {
        expr = "Nvector_serial.wrap",
        ty = tyarrow_ (otybaarrayclayoutfloat_ 1) otyopaque_
      }
    ]),
    ("nvectorSerialUnwrap", [
      impl {
        expr = "Nvector_serial.unwrap",
        ty = tyarrow_ otyopaque_ (otybaarrayclayoutfloat_ 1)
      }
    ]),
    ("sundialsMatrixDense", [
      impl {
        expr = "Sundials.Matrix.dense",
        ty = tyarrows_ [tyint_, otyopaque_]
      }
    ]),
    ("sundialsMatrixDenseUnwrap", [
      impl {
        expr = "Sundials.Matrix.Dense.unwrap",
        ty = tyarrows_ [otyopaque_, (otybaarrayclayoutfloat_ 2)]
      }
    ]),
    ("sundialsMatrixDenseGet", [
      impl {
        expr = "Sundials.Matrix.Dense.get",
        ty = tyarrows_ [otyopaque_, tyint_, tyint_, tyfloat_]
      }
    ]),
    ("sundialsMatrixDenseSet", [
      impl {
        expr = "Sundials.Matrix.Dense.set",
        ty = tyarrows_ [otyopaque_, tyint_, tyint_, tyfloat_, otyunit_]
      }
    ]),
    ("sundialsMatrixDenseUpdate", [
      impl {
        expr = "Sundials.Matrix.Dense.update",
        ty = tyarrows_ [
          otyopaque_, tyint_, tyint_, tyarrow_ tyfloat_ tyfloat_, otyunit_
        ]
      }
    ]),
    ("sundialsNonlinearSolverNewtonMake", [
      impl {
        expr = "Sundials_NonlinearSolver.Newton.make",
        ty =
          tyarrows_ [
            otyopaque_,
            otyopaque_
          ]
      }
    ]),
    ("sundialsNonlinearSolverFixedPointMake", [
      impl {
        expr = "Sundials_NonlinearSolver.FixedPoint.make",
        ty =
          tyarrows_ [
            otylabel_ "acceleration_vectors" tyint_,
            otyopaque_,
            otyopaque_
          ]
      }
    ])
  ]
