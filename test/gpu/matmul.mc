-- 

include "common.mc"

let transposeSq : [[Float]] -> [[Float]] = lam m.
  let n = length m in
  create n (lam i. create n (lam j. get (get m j) i))

let addProd : [Float] -> [Float] -> Float = lam row. lam col.
  recursive let work = lam row. lam col.
    if null row then []
    else if null col then []
    else
      cons (mulf (head row) (head col)) (work (tail row) (tail col))
  in
  -- This should really be compiled into a reduce
  foldl addf 0.0 (work row col)

let matMulSq : [[Float]] -> [[Float]] -> [[Float]] = lam a. lam b.
  let n = length a in
  let b = transposeSq b in
  map
    (lam aRow.
      let res = map (addProd aRow) b in
      subsequence res 0 n)
    a

let matSumSq : [[Float]] -> Float = lam m.
  -- These expressions should become reduce...
  foldl addf 0.0 (map (foldl addf 0.0) m)

mexpr

let randFloat = lam.
  divf (int2float (randIntU 0 10000)) 1000.0
in

let n = 1024 in
let a : [[Float]] = create n (lam. create n (lam. randFloat ())) in
let b : [[Float]] = create n (lam. create n (lam. randFloat ())) in
let t0 = wallTimeMs () in
let s = accelerate (matSumSq (matMulSq a b)) in
let t1 = wallTimeMs () in
printLn (join ["Computation time: ", float2string (divf (subf t1 t0) 1000.0)]);
printLn (join ["Result: ", float2string s])
