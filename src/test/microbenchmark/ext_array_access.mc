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
let a = extArrMakeUninit extArrKindFloat64 n in
let bm = lam.
  extArrSetExn a (randIntU 0 n) (int2float (randIntU 0 n));
  for_ 0 (subi n 2) (lam i. extArrSetExn a i (extArrGetExn a (addi i 1)));
  print (float2string (extArrGetExn a (randIntU 0 n)))
in

bc_repeat bm
