
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "fold.ml"

mexpr

let foldl = lam f. lam acc. lam s.
  recursive let rec = lam acc. lam s.
    match s with [] then acc
    else match s with [a] ++ ss then rec (f acc a) ss
    else never
  in rec acc s
in

let foldf = lam n.
  foldl addi 0 (createRope n (lam i. i))
in

-- printLn (int2string (foldf n));

bc_repeat (lam. foldf n)
