-- Runs a naive implementation of matrix multiplication using both the default
-- OCaml generation and the accelerated generation, to compare their
-- performance and also to ensure they get the same results.
--
-- We use matrices of integers because the addition of floating-point values is
-- technically not an associative operation, so the compiler cannot parallelize
-- folds over such operations. This results in significant improvements over
-- the default version.

include "common.mc"
include "string.mc"

let transposeSq : [[Int]] -> [[Int]] = lam m.
  -- We use this utest to express that m is a square matrix.
  utest length m with length (head m) in
  let n = length m in
  let g : Int -> Int -> Int = lam i. lam j.
    get (get m j) i
  in
  let f = lam i. create n (g i) in
  create n f

let addProd : [Int] -> [Int] -> Int = lam row. lam col.
  recursive let work : [Int] -> [Int] -> [Int] = lam row. lam col.
    if null row then []
    else if null col then []
    else
      let rh = head row in
      let ch = head col in
      let rt = tail row in
      let ct = tail col in
      cons (muli rh ch) (work rt ct)
  in
  foldl addi 0 (work row col)

let matMulSq : [[Int]] -> [[Int]] -> [[Int]] = lam a. lam b.
  -- We use the below utests to express size equality constraints on the
  -- dimensions of a and b.
  utest length a with length b in
  utest length a with length (head a) in
  utest length a with length (head b) in
  let b = transposeSq b in
  map (lam aRow. map (addProd aRow) b) a

let matSumSq : [[Int]] -> Int = lam m.
  foldl addi 0 (map (foldl addi 0) m)

mexpr

-- If we increase this value, the accelerated code will become faster relative
-- to the pure OCaml code.
let n = 128 in
let a = create n (lam. create n (lam. randIntU 0 10)) in
let b = create n (lam. create n (lam. randIntU 0 10)) in
let t0 = wallTimeMs () in
let c1 = matMulSq a b in
let cpu = matSumSq c1 in
let t1 = wallTimeMs () in
let c2 = accelerate (matMulSq a b) in
let gpu = accelerate (matSumSq c2) in
let t2 = wallTimeMs () in
utest cpu with gpu using eqi in
()
