
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "fold.ml"

mexpr

let foldf = lam n.
  foldl addi 0 (createFingerTree n (lam i. i))
in

-- printLn (int2string (foldf n));

repeat (lam. foldf n)
