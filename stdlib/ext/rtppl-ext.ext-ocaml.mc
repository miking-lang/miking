include "map.mc"
include "ocaml/ast.mc"

let tyts_ = tytuple_ [tyint_, tyfloat_]
let impl = lam arg : {expr : String, ty : Type }.
  [ { expr = arg.expr, ty = arg.ty, libraries = ["rtppl-support"], cLibraries = ["rt"] } ]

let rtpplExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("lvRead", impl { expr = "Rtppl.lv_read", ty = tyarrow_ tyint_ tyts_ }),
    ("lvWrite", impl { expr = "Rtppl.lv_write", ty = tyarrows_ [tyint_, tyts_, otyunit_] }),
    ( "setSignalHandler"
    , impl { expr = "Rtppl.set_signal_handler"
           , ty = tyarrows_ [tyint_, tyarrow_ tyint_ otyunit_, otyunit_] } ),
    ( "clockGetTime"
    , impl { expr = "Rtppl.clock_get_time"
           , ty = tyarrow_ otyunit_ (otytuple_ [tyint_, tyint_])} ),
    ( "clockNanosleep"
    , impl { expr = "Rtppl.clock_nanosleep"
           , ty = tyarrow_ (otytuple_ [tyint_, tyint_]) otyunit_ } )
  ]
