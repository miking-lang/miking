include "ext/mat-ext.mc"
include "benchmarkcommon.mc"

let n = 100

let mat1 = matMakeUninit extArrKindFloat64 n n
let mat2 = matMakeUninit extArrKindFloat64 n n
let acc = ref 0.

let benchmark = lam.
  bc_repeat (lam.
    matSetExn mat1 (randIntU 0 n) (randIntU 0 n) (int2float (randIntU 0 1));
    matSetExn mat2 (randIntU 0 n) (randIntU 0 n) (int2float (randIntU 0 1));
    let mat3 = matMulExn mat1 mat2 in
    modref acc (addf (deref acc) (matGetExn mat1 (randIntU 0 n) (randIntU 0 n))));
  print (float2string (deref acc))

mexpr

-- Benchmark
benchmark ()
