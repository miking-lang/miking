include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  {
    expr = arg.expr,
    ty = arg.ty,
    libraries = ["ipoptml"],
    cLibraries = ["ipopt"]
  }

let tyvec = otybaarrayclayoutfloat_ 1
let tyevalf = tyarrow_ tyvec tyfloat_
let tyevalgradf = tyarrows_ [tyvec, tyvec, otyunit_]
let tyevalg = tyarrows_ [tyvec, tyvec, otyunit_]
let tystructure = otyarray_ (otytuple_ [tyint_, tyint_])
let tyevaljacg = tyarrows_ [tyvec, tyvec, otyunit_]
let tyevalh = tyarrows_ [
  otylabel_ "sigma" tyfloat_,
  otylabel_ "x" tyvec,
  otylabel_ "lambda" tyvec,
  otylabel_ "h" tyvec,
  otyunit_
]

let ipoptExtMap =
  mapFromSeq cmpString
  [
    ("externalIpoptApplicationReturnStatusRetcode", [
      impl {
        expr = "Ipoptml.application_return_status_retcode",
        ty = tyarrow_ otyopaque_ tyint_
      }
    ]),
    ("externalIpoptCreateNLP", [
      impl {
        expr = "Ipoptml.create_nlp",
        ty = tyarrows_ [
          otylabel_ "eval_f" tyevalf,
          otylabel_ "eval_grad_f" tyevalgradf,
          otylabel_ "eval_g" tyevalg,
          otylabel_ "jac_g_structure" tystructure,
          otylabel_ "eval_jac_g" tyevaljacg,
          otylabel_ "h_structure" tystructure,
          otylabel_ "eval_h" tyevalh,
          otylabel_ "lb" tyvec,
          otylabel_ "ub" tyvec,
          otylabel_ "constraints_lb" tyvec,
          otylabel_ "constraints_ub" tyvec,
          otyopaque_
        ]
      }
    ]),
    ("externalIpoptAddStrOption", [
      impl {
        expr = "Ipoptml.add_str_option",
        ty = tyarrows_ [otyopaque_, otystring_, otystring_, otyunit_]
      }
    ]),
    ("externalIpoptAddNumOption", [
      impl {
        expr = "Ipoptml.add_num_option",
        ty = tyarrows_ [otyopaque_, otystring_, tyfloat_, otyunit_]
      }
    ]),
    ("externalIpoptAddIntOption", [
      impl {
        expr = "Ipoptml.add_int_option",
        ty = tyarrows_ [otyopaque_, otystring_, tyint_, otyunit_]
      }
    ]),
    ("externalIpoptSolve", [
      impl {
        expr = "Ipoptml.solve",
        ty = tyarrows_ [otyopaque_, tyvec, otyopaque_]
      }
    ])
  ]
