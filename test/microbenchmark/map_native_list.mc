
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "map_n.ml"

mexpr

let map = lam f. lam s.
  recursive let rec = lam s.
    match s with [] then []
    else match s with [a] then [f a]
    else match s with [a] ++ ss then cons (f a) (rec ss)
    else never
  in rec s
in

let mapf = lam n.
  map (addi 1) (createList n (lam i. i))
in

-- iter (lam x. print (int2string x)) (mapf n);

bc_repeat (lam. mapf n)
