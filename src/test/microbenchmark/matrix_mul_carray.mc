include "benchmarkcommon.mc"

type Mat = Tensor[Float]

let loop_ = lam n. lam f.
  recursive let recur = lam i.
    if geqi i n then () else f i; recur (addi i 1)
  in
  recur 0

let matMul : Mat -> Mat -> Mat -> ()
  = lam mat1. lam mat2. lam mat3.
    match (tensorShape mat1, tensorShape mat2, tensorShape mat3) with
      ([m1, n1], [m2, n2], [m3, n3])
    then
      loop_ m3 (lam i. loop_ n3 (lam j. tensorSetExn mat3 [i, j] 0.));
      loop_ m3 (lam i.
        loop_ n3 (lam j.
          loop_ m1 (lam k.
            tensorSetExn mat3 [i, j]
              (addf
                 (tensorGetExn mat3 [i, j])
                 (mulf
                    (tensorGetExn mat1 [k, j])
                    (tensorGetExn mat2 [i, k]))))))
    else error "Invalid input"

let n = 100

let mat1 = tensorCreateUninitFloat [n, n]
let mat2 = tensorCreateUninitFloat [n, n]
let mat3 = tensorCreateUninitFloat [n, n]
let acc = ref 0.

let benchmark = lam.
  bc_repeat (lam.
    tensorSetExn mat1 [randIntU 0 n, randIntU 0 n] (int2float (randIntU 0 1));
    tensorSetExn mat2 [randIntU 0 n, randIntU 0 n] (int2float (randIntU 0 1));
    matMul mat1 mat2 mat3;
    modref acc (addf (deref acc) (tensorGetExn mat3 [randIntU 0 n, randIntU 0 n])));
  print (float2string (deref acc))

mexpr

-- Benchmark
benchmark ()
