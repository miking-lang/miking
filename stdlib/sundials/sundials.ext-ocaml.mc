include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : Type }.
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
