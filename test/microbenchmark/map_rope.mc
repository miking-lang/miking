
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "map.ml"

mexpr

let mapf = lam n.
  map (addi 1) (createRope n (lam i. i))
in

-- iter (lam x. print (int2string x)) (mapf n);

repeat (lam. mapf n)
