
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "map_n.ml"

mexpr

let mapf = lam n.
  map (addi 1) (createRope n (lam i. i))
in

-- iter (lam x. print (int2string x)) (mapf n);

bc_repeat (lam. mapf n)
