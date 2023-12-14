include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["sundialsml"], cLibraries = [] }

let tyrealarray = otyvarext_ "Sundials.RealArray.t" []

let tycvoderhs =
  tyarrows_ [
    tyfloat_,
    otybaarrayclayoutfloat_ 1,
    otybaarrayclayoutfloat_ 1,
    otyunit_
]

let cvodeExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("cvodeDlsDense", [
      impl {
        expr = "Cvode.Dls.dense",
        ty = tyarrows_ [otyopaque_, otyopaque_, otyopaque_]
      }
    ]),
    ("cvodeDlsSolver", [
      impl {
        expr = "Cvode.Dls.solver",
        ty =
          tyarrows_ [
            otyopaque_,
            otyopaque_
          ]
      }
    ]),
    ("cvodeSSTolerances", [
      impl {
        expr = "fun rtol atol -> Cvode.SStolerances (rtol, atol)",
        ty = tyarrows_ [tyfloat_, tyfloat_, otyopaque_]
      }
    ]),
    ("cvodeLMMAdams", [
      impl {
        expr = "Cvode.Adams",
        ty = otyopaque_
      }
    ]),
    ("cvodeLMMBDF", [
      impl {
        expr = "Cvode.BDF",
        ty = otyopaque_
      }
    ]),
    ("cvodeInit", [
      impl {
        expr = "Cvode.init",
        ty = tyarrows_ [
          otyopaque_,
          otyopaque_,
          otylabel_ "lsolver" otyopaque_,
          tycvoderhs,
          tyfloat_,
          otyopaque_,
          otyopaque_
        ]
      }
    ]),
    ("cvodeSolveNormal", [
      impl {
        expr = "
begin
  let solve_normal s tend y =
    try
      match Cvode.solve_normal s tend y with
      | (tend, Cvode.Success) -> (tend, (0, -1))
      | (tend, Cvode.RootsFound) -> (tend, (1, -1))
      | (tend, Cvode.StopTimeReached ) -> (tend, (2, -1))
    with
    | Cvode.IllInput -> (tend, (3, 0))
    | Cvode.TooClose -> (tend, (3, 1))
    | Cvode.TooMuchWork -> (tend, (3, 2))
    | Cvode.TooMuchAccuracy -> (tend, (3, 3))
    | Cvode.ErrFailure -> (tend, (3, 4))
    | Cvode.ConvergenceFailure -> (tend, (3, 5))
    | Cvode.LinearInitFailure -> (tend, (3, 6))
    | Cvode.LinearSetupFailure _ -> (tend, (3, 7))
    | Cvode.LinearSolveFailure _ -> (tend, (3, 8))
    | Cvode.RhsFuncFailure -> (tend, (3, 9))
    | Cvode.FirstRhsFuncFailure -> (tend, (3, 10))
    | Cvode.RepeatedRhsFuncFailure -> (tend, (3, 11))
    | Cvode.UnrecoverableRhsFuncFailure -> (tend, (3, 12))
    | Cvode.RootFuncFailure -> (tend, (3, 13))
    | _ -> (tend, (3, -1))
  in solve_normal
end
",
        ty = tyarrows_ [
               otyopaque_,
               tyfloat_,
               otyopaque_,
               otytuple_ [tyfloat_, otytuple_ [tyint_, tyint_]]
        ]
      }
    ]),
    ("cvodeSetStopTime", [
      impl {
        expr = "Cvode.set_stop_time",
        ty = tyarrows_ [otyopaque_, tyfloat_, otyunit_]
      }
    ])
  ]
