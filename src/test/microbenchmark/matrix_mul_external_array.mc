include "ext/arr-ext.mc"
include "benchmarkcommon.mc"

type Mat = (Int, Int, Arr Float)

let loop_ = lam n. lam f.
  recursive let recur = lam i.
    if geqi i n then () else f i; recur (addi i 1)
  in
  recur 0

let matMul : Mat -> Mat -> Mat -> ()
  = lam mat1. lam mat2. lam mat3.
    match (mat1, mat2, mat3) with
      ((m1, n1, a1), (m2, n2, a2), (m3, n3, a3))
    then
      loop_ m3 (lam i. loop_ n3 (lam j. arrSetExn a3 (addi (muli i n1) j) 0.));
      loop_ m3 (lam i.
        loop_ n3 (lam j.
          loop_ m1 (lam k.
            arrSetExn a3 (addi (muli i n2) j)
              (addf
                 (arrGetExn a3 (addi (muli i n2) j))
                 (mulf
                    (arrGetExn a1 (addi (muli k n2) j))
                    (arrGetExn a2 (addi (muli i n2) k)))))))
    else error "Invalid input"

let n = 100

let mat1 = (n, n, arrMakeUninitFloat (muli n n))
let mat2 = (n, n, arrMakeUninitFloat (muli n n))
let mat3 = (n, n, arrMakeUninitFloat (muli n n))
let acc = ref 0.

let benchmark = lam.
  bc_repeat (lam.
    arrSetExn mat1.2 (randIntU 0 (muli n n)) (int2float (randIntU 0 1));
    arrSetExn mat2.2 (randIntU 0 (muli n n)) (int2float (randIntU 0 1));
    matMul mat1 mat2 mat3;
    modref acc (addf (deref acc) (arrGetExn mat1.2 (randIntU 0 (muli n n)))));
  print (float2string (deref acc))

mexpr

-- Benchmark
benchmark ()
