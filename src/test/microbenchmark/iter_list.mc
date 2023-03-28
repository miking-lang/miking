
include "benchmarkcommon.mc"
include "iter.ml"

mexpr

let iterf = lam n.
  iter (lam. ()) (createList n (lam i. i))
in

bc_repeat (lam. iterf n)
