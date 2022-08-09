include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"

mexpr

let foldf = lam n.
  foldl addi 0 (createList n (lam i. i));
  ()
in

repeat (lam. foldf 100000)
