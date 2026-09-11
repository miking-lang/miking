include "ext/mat-ext.mc"
include "ext/arr-ext.mc"
include "benchmarkcommon.mc"

let loop_ = lam n. lam f.
  recursive let recur = lam i.
    if geqi i n then () else f i; recur (addi i 1)
  in
  recur 0

let matMul
  = lam mat1. lam mat2. lam mat3.
    loop_ mat3.m (lam i. loop_ mat3.n (lam j. matSetExn mat3 i j 0.));
    loop_ mat3.m (lam i.
      loop_ mat3.n (lam j.
        loop_ mat1.m (lam k.
          matSetExn mat3 i j
            (addf
               (matGetExn mat3 i j)
               (mulf (matGetExn mat1 k j) (matGetExn mat2 i k))))))

let n = 100

let mat1 = matMakeUninit extArrKindFloat64 n n
let mat2 = matMakeUninit extArrKindFloat64 n n
let mat3 = matMakeUninit extArrKindFloat64 n n

let benchmark = lam.
  bc_repeat (lam.
    matSetExn mat1 (randIntU 0 n) (randIntU 0 n) (int2float (randIntU 0 1));
    matSetExn mat2 (randIntU 0 n) (randIntU 0 n) (int2float (randIntU 0 1));
    matMul mat1 mat2 mat3);
  print (float2string (matGetExn mat3 (randIntU 0 n) (randIntU 0 n)))

mexpr

-- Benchmark
benchmark ()
