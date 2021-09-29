include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["sundialsml"], cLibraries = [] }

let tyrealarray = otyvarext_ "Sundials.RealArray.t" []
let tyidatriple = otyvarext_ "Ida.triple"
let tyidajacobianargra =
  otyvarext_ "Ida.jacobian_arg" [tyidatriple tyrealarray, tyrealarray]

let tyidajacf =
  tyarrows_ [
    otyrecord_
      tyidajacobianargra
      [
        ("jac_t", tyfloat_),
        ("jac_y", otybaarrayclayoutfloat_ 1),
        ("jac_y'", otybaarrayclayoutfloat_ 1),
        ("jac_res", otybaarrayclayoutfloat_ 1),
        ("jac_coef", tyfloat_),
        ("jac_tmp", otytuple_
                      [otybaarrayclayoutfloat_ 1,
                       otybaarrayclayoutfloat_ 1,
                       otybaarrayclayoutfloat_ 1])
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
    ("externalSundialsRealArrayCreate", [
      impl { expr = "Sundials.RealArray.create", ty = tyarrow_ tyint_ otyopaque_}
    ]),
    ("externalNvectorSerialWrap", [
      impl {
        expr = "Nvector_serial.wrap",
        ty = tyarrow_ (otybaarrayclayoutfloat_ 1) otyopaque_
      }
    ]),
    ("externalNvectorSerialUnwrap", [
      impl {
        expr = "Nvector_serial.unwrap",
        ty = tyarrow_ otyopaque_ (otybaarrayclayoutfloat_ 1)
      }
    ]),
    ("externalSundialsMatrixDense", [
      impl {
        expr = "Sundials.Matrix.dense",
        ty = tyarrows_ [tyint_, otyopaque_]
      }
    ]),
    ("externalSundialsMatrixDenseUnwrap", [
      impl {
        expr = "Sundials.Matrix.Dense.unwrap",
        ty = tyarrows_ [otyopaque_, (otybaarrayclayoutfloat_ 2)]
      }
    ]),
    ("externalIdaDlsDense", [
      impl {
        expr = "Ida.Dls.dense",
        ty = tyarrows_ [otyopaque_, otyopaque_, otyopaque_]
      }
    ]),
    ("externalIdaDlsSolverJacf", [
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
    ("externalIdaDlsSolver", [
      impl {
        expr = "Ida.Dls.solver",
        ty =
          tyarrows_ [
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
    ("externalIdaSSTolerances", [
      impl {
        expr = "fun rtol atol -> Ida.SStolerances (rtol, atol)",
        ty = tyarrows_ [tyfloat_, tyfloat_, otyopaque_]
      }
    ]),
    ("externalIdaRetcode", [
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
    ("externalIdaInit", [
      impl {
        expr = "Ida.init",
        ty = tyarrows_ [
          otyopaque_,
          otyopaque_,
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
    ("externalIdaCalcICYaYd", [
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
    ("externalIdaSolveNormal", [
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
    ("externalIdaReinit", [
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
