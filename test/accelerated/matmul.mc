-- Runs a naive implementation of matrix multiplication on both CPU and GPU, to
-- compare their performance and also to ensure they get the same results.
--
-- We use matrices of integers because the addition of floating-point values is
-- technically not an associative operation, so the compiler cannot parallelize
-- folds over such operations. This results in significant improvements over
-- the CPU-only version.

include "common.mc"
include "string.mc"

let transposeSq : [[Int]] -> [[Int]] = lam m.
  let n = length m in
  create n
    (lam i : Int.
      let inner : [Int] = create n (lam j : Int. get (get m j) i) in
      inner)

let addProd : [Int] -> [Int] -> Int = lam row. lam col.
  recursive let work = lam row. lam col.
    if null row then []
    else if null col then []
    else cons (muli (head row) (head col)) (work (tail row) (tail col))
  in
  foldl addi 0 (work row col)

let matMulSq : [[Int]] -> [[Int]] -> [[Int]] = lam a. lam b.
  let b = transposeSq b in
  map
    (lam aRow : [Int].
      let row : [Int] = map (addProd aRow) b in
      row)
    a

let matSumSq : [[Int]] -> Int = lam m.
  foldl addi 0 (map (foldl addi 0) m)

mexpr

let n = 1024 in
let a : [[Int]] = create n (lam. create n (lam. randIntU 0 10)) in
let b : [[Int]] = create n (lam. create n (lam. randIntU 0 10)) in
let t0 = wallTimeMs () in
let c1 : [[Int]] = matMulSq a b in
let cpu : Int = matSumSq c1 in
let t1 = wallTimeMs () in
let c2 : [[Int]] = accelerate (matMulSq a b) in
let gpu : Int = accelerate (matSumSq c2) in
let t2 = wallTimeMs () in
printLn (join ["CPU time: ", float2string (divf (subf t1 t0) 1000.0)]);
printLn (join ["GPU time: ", float2string (divf (subf t2 t1) 1000.0)]);
if eqi cpu gpu then
  printLn "CPU and GPU found the same result"
else
  printLn "CPU and GPU got different results";
  printLn (join ["CPU result: ", int2string cpu]);
  printLn (join ["GPU result: ", int2string gpu])
