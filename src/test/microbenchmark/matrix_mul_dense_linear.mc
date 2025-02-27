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
      loop_ m3 (lam i. loop_ n3 (lam j. tensorLinearSetExn mat3 (addi (muli i n1) j) 0.));
      loop_ m3 (lam i.
        loop_ n3 (lam j.
          loop_ m1 (lam k.
            tensorLinearSetExn mat3 (addi (muli i n2) j)
              (addf
                 (tensorLinearGetExn mat3 (addi (muli i n2) j))
                 (mulf
                    (tensorLinearGetExn mat1 (addi (muli k n2) j))
                    (tensorLinearGetExn mat2 (addi (muli i n2) k)))))))
    else error "Invalid input"

let n = 100

let mat1 = tensorCreateDense [n, n] (lam. 0.)
let mat2 = tensorCreateDense [n, n] (lam. 0.)
let mat3 = tensorCreateDense [n, n] (lam. 0.)
let acc = ref 0.

let benchmark = lam.
  bc_repeat (lam.
    tensorLinearSetExn mat1 (randIntU 0 (muli n n)) (int2float (randIntU 0 1));
    tensorLinearSetExn mat2 (randIntU 0 (muli n n)) (int2float (randIntU 0 1));
    matMul mat1 mat2 mat3;
    modref acc (addf (deref acc) (tensorLinearGetExn mat3 (randIntU 0 (muli n n)))));
  print (float2string (deref acc))

mexpr

-- Benchmark
benchmark ()
