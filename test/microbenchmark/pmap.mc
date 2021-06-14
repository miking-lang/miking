
include "benchmarkcommon.mc"
include "multicore/pseq.mc"
include "map.ml"

mexpr

let pmapf = lam n.
  pmap (addi 1) (create n (lam i. i))
in

repeat (lam. pmapf n)
