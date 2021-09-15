include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { ident : String, ty : Type }.
  { ident = arg.ident, ty = arg.ty, libraries = ["sundialsml"], cLibraries = [] }

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
      impl { ident = "Sundials.RealArray.create", ty = tyarrow_ tyint_ otyopaque_}
    ]),
    ("externalNvectorSerialWrap", [
      impl {
        ident = "Nvector_serial.wrap",
        ty = tyarrow_ (otybaarrayclayoutfloat_ 1) otyopaque_
      }
    ]),
    ("externalNvectorSerialUnwrap", [
      impl {
        ident = "Nvector_serial.unwrap",
        ty = tyarrow_ otyopaque_ (otybaarrayclayoutfloat_ 1)
      }
    ]),
    ("externalSundialsMatrixDense", [
      impl {
        ident = "Sundials.Matrix.dense",
        ty = tyarrows_ [tyint_, otyopaque_]
      }
    ]),
    ("externalSundialsMatrixDenseUnwrap", [
      impl {
        ident = "Sundials.Matrix.Dense.unwrap",
        ty = tyarrows_ [otyopaque_, (otybaarrayclayoutfloat_ 2)]
      }
    ]),
    ("externalIdaDlsDense", [
      impl {
        ident = "Ida.Dls.dense",
        ty = tyarrows_ [otyopaque_, otyopaque_, otyopaque_]
      }
    ]),
    ("externalIdaDlsSolverJacf", [
      impl {
        ident = "Ida.Dls.solver",
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
        ident = "Ida.Dls.solver",
        ty =
          tyarrows_ [
            otyopaque_,
            otyopaque_
          ]
      }
    ]),
    ("idaVarIdAlgebraic", [
      impl { ident = "Ida.VarId.algebraic", ty = tyfloat_ }
    ]),
    ("idaVarIdDifferential", [
      impl { ident = "Ida.VarId.differential", ty = tyfloat_ }
    ]),
    ("externalIdaSSTolerances", [
      impl {
        ident = "Boot.Sundials_wrapper.ida_ss_tolerances",
        ty = tyarrows_ [tyfloat_, tyfloat_, otyopaque_]
      }
    ]),
    ("externalIdaRetcode", [
      impl {
        ident = "Boot.Sundials_wrapper.ida_retcode",
        ty = tyarrow_ otyopaque_ tyint_
      }
    ]),
    ("externalIdaInit", [
      impl {
        ident = "Ida.init",
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
        ident = "Ida.calc_ic_ya_yd'",
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
        ident = "Ida.solve_normal",
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
        ident = "Ida.reinit",
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
