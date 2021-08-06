include "map.mc"
include "ocaml/ast.mc"

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
      { ident = "Sundials.RealArray.create",
        ty = tyarrow_ tyint_ otyopaque_,
        libraries = ["sundialsml"] }
    ]),
    ("externalNvectorSerialWrap", [
      { ident = "Nvector_serial.wrap",
        ty = tyarrow_ (otybaarrayclayoutfloat_ 1) otyopaque_,
        libraries = ["sundialsml"] }
    ]),
    ("externalNvectorSerialUnwrap", [
      { ident = "Nvector_serial.unwrap",
        ty = tyarrow_ otyopaque_ (otybaarrayclayoutfloat_ 1),
        libraries = ["sundialsml"] }
    ]),
    ("externalSundialsMatrixDense", [
      { ident = "Sundials.Matrix.dense",
        ty = tyarrows_ [tyint_, otyopaque_],
        libraries = ["sundialsml"] }
    ]),
    ("externalSundialsMatrixDenseUnwrap", [
      { ident = "Sundials.Matrix.Dense.unwrap",
        ty = tyarrows_ [otyopaque_, (otybaarrayclayoutfloat_ 2)],
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaDlsDense", [
      { ident = "Ida.Dls.dense",
        ty = tyarrows_ [otyopaque_, otyopaque_, otyopaque_],
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaDlsSolverJacf", [
      { ident = "Ida.Dls.solver",
        ty =
          tyarrows_ [
            otylabel_ "jac" tyidajacf,
            otyopaque_,
            otyopaque_
          ],
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaDlsSolver", [
      { ident = "Ida.Dls.solver",
        ty =
          tyarrows_ [
            otyopaque_,
            otyopaque_
          ],
        libraries = ["sundialsml"] }
    ]),
    ("idaVarIdAlgebraic", [
      { ident = "Ida.VarId.algebraic",
        ty = tyfloat_,
        libraries = ["sundialsml"] }
    ]),
    ("idaVarIdDifferential", [
      { ident = "Ida.VarId.differential",
        ty = tyfloat_,
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaSSTolerances", [
      { ident = "Boot.Sundials_wrapper.ida_ss_tolerances",
        ty = tyarrows_ [tyfloat_, tyfloat_, otyopaque_],
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaRetcode", [
      { ident = "Boot.Sundials_wrapper.ida_retcode",
        ty = tyarrow_ otyopaque_ tyint_,
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaInit", [
      { ident = "Ida.init",
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
        ],
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaCalcICYaYd", [
      { ident = "Ida.calc_ic_ya_yd'",
        ty = tyarrows_ [
               otyopaque_,
               tyfloat_,
               otylabel_ "y" otyopaque_,
               otylabel_ "y'" otyopaque_,
               otyunit_
        ],
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaSolveNormal", [
      { ident = "Ida.solve_normal",
        ty = tyarrows_ [
               otyopaque_,
               tyfloat_,
               otyopaque_,
               otyopaque_,
               otytuple_ [tyfloat_, otyopaque_]
        ],
        libraries = ["sundialsml"] }
    ]),
    ("externalIdaReinit", [
      { ident = "Ida.reinit",
        ty = tyarrows_ [
          otyopaque_,
          otylabel_ "roots" (otytuple_ [tyint_, tyidarootf]),
          tyfloat_,
          otyopaque_,
          otyopaque_,
          otyunit_
        ],
        libraries = ["sundialsml"] }
    ])
  ]
