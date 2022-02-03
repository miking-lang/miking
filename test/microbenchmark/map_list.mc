
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "map_n.ml"

mexpr

let workload = 30 in
recursive let fibonacci = lam n.
  if lti n 3 then 1
  else addi (fibonacci (subi n 1)) (fibonacci (subi n 2))
in

let mapf = lam n.
  map (lam. fibonacci workload) (createList n (lam i. i))
in

repeat (lam. mapf n)
