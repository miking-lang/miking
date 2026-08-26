
include "benchmarkcommon.mc"
include "iter.mc"

mexpr

let iterf = lam n.
  iter (lam. ()) (createRope n (lam i. i))
in

bc_repeat (lam. iterf n)
