include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["sundialsml"], cLibraries = [] }

let tyrealarray = otyvarext_ "Sundials.RealArray.t" []
let tyidatriple = otyvarext_ "Ida.triple"
let tyidajacobianarg =
  otyvarext_ "Ida.jacobian_arg" [tyidatriple [tyrealarray], tyrealarray]

let tyidajacf =
  tyarrows_ [
    otyrecordext_
      tyidajacobianarg
      [
        { label = "jac_t", asLabel = "t", ty = tyfloat_ },
        { label = "jac_y", asLabel = "y", ty = otybaarrayclayoutfloat_ 1 },
        { label = "jac_y'", asLabel = "yp", ty = otybaarrayclayoutfloat_ 1 },
        { label = "jac_res", asLabel = "res", ty = otybaarrayclayoutfloat_ 1 },
        { label = "jac_coef", asLabel = "c", ty = tyfloat_ },
        { label = "jac_tmp", asLabel = "tmp",
          ty = otytuple_ [
            otybaarrayclayoutfloat_ 1,
            otybaarrayclayoutfloat_ 1,
            otybaarrayclayoutfloat_ 1
        ] }
      ],
    otyopaque_,
    otyunit_
]

let tyidaresf =
  tyarrows_ [
    tyfloat_,
    otybaarrayclayoutfloat_ 1,
    otybaarrayclayoutfloat_ 1,
    otybaarrayclayoutfloat_ 1,
    otyunit_
]

let tyidarootf = tyidaresf

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
    ("idaDlsDense", [
      impl {
        expr = "Ida.Dls.dense",
        ty = tyarrows_ [otyopaque_, otyopaque_, otyopaque_]
      }
    ]),
    ("idaDlsSolverJacf", [
      impl {
        expr = "Ida.Dls.solver",
        ty =
          tyarrows_ [
            otylabel_ "jac" tyidajacf,
            otyopaque_,
            otyopaque_
          ]
      }
    ]),
    ("idaDlsSolver", [
      impl {
        expr = "Ida.Dls.solver",
        ty =
          tyarrows_ [
            otyopaque_,
            otyopaque_
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
    ]),
    ("idaVarIdAlgebraic", [
      impl { expr = "Ida.VarId.algebraic", ty = tyfloat_ }
    ]),
    ("idaVarIdDifferential", [
      impl { expr = "Ida.VarId.differential", ty = tyfloat_ }
    ]),
    ("idaSSTolerances", [
      impl {
        expr = "fun rtol atol -> Ida.SStolerances (rtol, atol)",
        ty = tyarrows_ [tyfloat_, tyfloat_, otyopaque_]
      }
    ]),
    ("idaRetcode", [
      impl {
        expr =
"function
  | Ida.Success ->
      0
  | Ida.StopTimeReached ->
      1
  | Ida.RootsFound ->
      2",
        ty = tyarrow_ otyopaque_ tyint_
      }
    ]),
    ("idaInit", [
      impl {
        expr = "Ida.init",
        ty = tyarrows_ [
          otyopaque_,
          otylabel_ "nlsolver" otyopaque_,
          otylabel_ "lsolver" otyopaque_,
          tyidaresf,
          otylabel_ "varid" otyopaque_,
          otylabel_ "roots" (otytuple_ [tyint_, tyidarootf]),
          tyfloat_,
          otyopaque_,
          otyopaque_,
          otyopaque_
        ]
      }
    ]),
    ("idaCalcICYaYd", [
      impl {
        expr = "Ida.calc_ic_ya_yd'",
        ty = tyarrows_ [
               otyopaque_,
               tyfloat_,
               otylabel_ "y" otyopaque_,
               otylabel_ "y'" otyopaque_,
               otyunit_
        ]
      }
    ]),
    ("idaSolveNormal", [
      impl {
        expr = "Ida.solve_normal",
        ty = tyarrows_ [
               otyopaque_,
               tyfloat_,
               otyopaque_,
               otyopaque_,
               otytuple_ [tyfloat_, otyopaque_]
        ]
      }
    ]),
    ("idaReinit", [
      impl {
        expr = "Ida.reinit",
        ty = tyarrows_ [
          otyopaque_,
          otylabel_ "roots" (otytuple_ [tyint_, tyidarootf]),
          tyfloat_,
          otyopaque_,
          otyopaque_,
          otyunit_
        ]
      }
    ])
  ]
