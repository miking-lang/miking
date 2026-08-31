
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "fold.mc"

mexpr

let foldf = lam n.
  foldl addi 0 (createList n (lam i. i))
in

-- printLn (int2string (foldf n));

bc_repeat (lam. foldf n)
