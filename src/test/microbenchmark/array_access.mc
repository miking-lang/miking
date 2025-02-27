include "common.mc"
include "benchmarkcommon.mc"
include "ext/arr-ext.mc"

mexpr

let for_ = lam from. lam to. lam f.
  recursive let rec = lam i.
    if leqi i to then f i; rec (addi i 1) else ()
  in rec from
in

let n = 10000 in
let a = arrMake n 0 in
let bm = lam.
  arrSetExn a (randIntU 0 n) (randIntU 0 n);
  for_ 0 (subi n 2) (lam i. arrSetExn a i (arrGetExn a (addi i 1)));
  print (float2string (int2float (arrGetExn a (randIntU 0 n))))
in

bc_repeat bm
