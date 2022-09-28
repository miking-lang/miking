include "map.mc"
include "ocaml/ast.mc"

let fdTy = tyint_
let payloadTy = otyarray_ tyfloat_
let impl = lam arg : {expr : String, ty : Type }.
  [ { expr = arg.expr, ty = arg.ty, libraries = ["rtppl"], cLibraries = [] } ]

let rtpplExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("openFd", impl { expr = "Rtppl.open_fd", ty = tyarrows_ [otystring_, fdTy] }),
    ("readFd", impl { expr = "Rtppl.read_fd", ty = tyarrows_ [fdTy, tyint_, payloadTy] }),
    ("writeFd", impl { expr = "Rtppl.write_fd", ty = tyarrows_ [fdTy, payloadTy, otyunit_] })
  ]
