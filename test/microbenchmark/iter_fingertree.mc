
include "benchmarkcommon.mc"
include "iter.ml"

mexpr

let iterf = lam n.
  iter (lam. ()) (createFingerTree n (lam i. i))
in

repeat (lam. iterf n)
2
