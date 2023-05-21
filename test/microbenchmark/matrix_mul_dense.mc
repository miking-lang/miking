include "matrix_mul_common.mc"

let matMul : Tensor[Float] -> Tensor[Float] -> Tensor[Float] -> ()
  = lam mat1. lam mat2. lam mat3.
  match tensorShape mat1 with [m1, n1] in
  match tensorShape mat2 with [m2, n2] in
  match tensorShape mat3 with [m3, n3] in
  if
    and
      (eqi n1 m2)
      (and
         (eqi m1 m3)
         (eqi n2 n3))
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

mexpr

-- Benchmark
benchmark tensorCreateDense matMul ();

-- Test
-- test mat_mul;
-- Expect
-- [
-- 	[0., 1., 2.],
-- 	[3., 4., 5.],
-- 	[6., 7., 8.]
-- ][
-- 	[0., 1., 2.],
-- 	[3., 4., 5.],
-- 	[6., 7., 8.]
-- ][
-- 	[15., 18., 21.],
-- 	[42., 54., 66.],
-- 	[69., 90., 111.]
-- ]
()
