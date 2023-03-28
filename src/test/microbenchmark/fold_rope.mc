
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "fold.ml"

mexpr

let foldf = lam n.
  foldl addi 0 (createRope n (lam i. i))
in

-- printLn (int2string (foldf n));

bc_repeat (lam. foldf n)
