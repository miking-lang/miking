
include "benchmarkcommon.mc"
include "multicore/pseq.mc"
include "fold.ml"

mexpr

let pfoldf = lam n.
  pfold addi 0 (create n (lam i. i))
in

repeat (lam. pfoldf n)
