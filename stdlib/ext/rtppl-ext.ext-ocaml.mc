include "map.mc"
include "ocaml/ast.mc"

let tyts_ = tytuple_ [tyint_, tyunknown_]
let impl = lam arg : {expr : String, ty : use Ast in Type }.
  [ { expr = arg.expr, ty = arg.ty, libraries = ["rtppl-support"], cLibraries = ["rt"] } ]

let timespec = otytuple_ [tyint_, tyint_]
let readDistTy = lam ty. otyarray_ (otytuple_ [tyfloat_, ty])
let writeDistTy = lam ty. otytuple_ [otyarray_ ty, otyarray_ tyfloat_]

let rtpplExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ( "setSigintHandler"
    , impl { expr = "Rtppl.set_signal_handler Sys.sigint"
           , ty = tyarrow_ (tyarrow_ tyint_ otyunit_) otyunit_ } ),
    ( "getMonotonicTime"
    , impl { expr = "Rtppl.get_monotonic_time"
           , ty = tyarrow_ otyunit_ timespec} ),
    ( "getWallClockTime"
    , impl { expr = "Rtppl.get_wall_clock_time"
           , ty = tyarrow_ otyunit_ timespec} ),
    ( "getProcessCpuTime"
    , impl { expr = "Rtppl.get_process_cpu_time"
           , ty = tyarrow_ otyunit_ timespec} ),
    ( "clockNanosleep"
    , impl { expr = "Rtppl.clock_nanosleep"
           , ty = tyarrow_ timespec otyunit_ } ),
    ( "rtpplSetMaxPriority"
    , impl { expr = "Rtppl.set_max_priority"
           , ty = tyarrow_ otyunit_ tyint_ } ),
    ( "rtpplSetPriority"
    , impl { expr = "Rtppl.set_priority"
           , ty = tyarrow_ tyint_ tyint_ } ),
    ( "rtpplOpenFileDescriptor"
    , impl { expr = "Rtppl.open_file_descriptor"
           , ty = tyarrows_ [otystring_, tyint_, tyint_] } ),
    ( "rtpplCloseFileDescriptor"
    , impl { expr = "Rtppl.close_file_descriptor"
           , ty = tyarrow_ tyint_ otyunit_ } ),
    ( "rtpplReadInt"
    , impl { expr = "Rtppl.read_int"
           , ty = tyarrow_ tyint_ (otyarray_ (otytuple_ [timespec, tyint_])) } ),
    ( "rtpplWriteInt"
    , impl { expr = "Rtppl.write_int"
           , ty = tyarrows_ [tyint_, otytuple_ [timespec, tyint_], otyunit_] } ),
    ( "rtpplReadFloat"
    , impl { expr = "Rtppl.read_float"
           , ty = tyarrow_ tyint_ (otyarray_ (otytuple_ [timespec, tyfloat_])) } ),
    ( "rtpplWriteFloat"
    , impl { expr = "Rtppl.write_float"
           , ty = tyarrows_ [tyint_, otytuple_ [timespec, tyfloat_], otyunit_] } ),
    ( "rtpplReadIntRecord"
    , impl { expr = "Rtppl.read_int_record"
           , ty = tyarrows_ [tyint_, tyint_, otyarray_ (otytuple_ [timespec, tyunknown_])] } ),
    ( "rtpplWriteIntRecord"
    , impl { expr = "Rtppl.write_int_record"
           , ty = tyarrows_ [tyint_, tyint_, otytuple_ [timespec, tyunknown_], otyunit_] } ),
    ( "rtpplReadFloatRecord"
    , impl { expr = "Rtppl.read_float_record"
           , ty = tyarrows_ [tyint_ ,tyint_, otyarray_ (otytuple_ [timespec, tyunknown_])] } ),
    ( "rtpplWriteFloatRecord"
    , impl { expr = "Rtppl.write_float_record"
           , ty = tyarrows_ [tyint_, tyint_, otytuple_ [timespec, tyunknown_], otyunit_] } ),
    ( "rtpplReadDistFloat"
    , impl { expr = "Rtppl.read_dist_float"
           , ty = tyarrow_ tyint_ (otyarray_ (otytuple_ [timespec, readDistTy tyfloat_])) } ),
    ( "rtpplWriteDistFloat"
    , impl { expr = "Rtppl.write_dist_float"
           , ty = tyarrows_ [tyint_, otytuple_ [timespec, writeDistTy tyfloat_], otyunit_] } ),
    ( "rtpplReadDistFloatRecord"
    , impl { expr = "Rtppl.read_dist_float_record"
           , ty = tyarrows_ [tyint_, tyint_, otyarray_ (otytuple_ [timespec, readDistTy tyunknown_])] } ),
    ( "rtpplWriteDistFloatRecord"
    , impl { expr = "Rtppl.write_dist_float_record"
           , ty = tyarrows_ [tyint_, tyint_, otytuple_ [timespec, writeDistTy tyunknown_], otyunit_] } )
  ]
