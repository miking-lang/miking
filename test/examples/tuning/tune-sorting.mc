include "common.mc"
include "string.mc"

-- mi tune test/examples/tuning/tune-sorting.mc -- --verbose --input 100 --input 10000 --method exhaustive

let init = lam n. lam f.
  -- 0 = FingerTree, 1 = List, 2 = Rope
  let repr = holeIntRange {min = 0, max = 2, depth = 1, default = 0} in

  match repr with 0 then
    createFingerTree n f
  else match repr with 1 then
    createList n f
  else match repr with 2 then
    createRope n f
  else never

-- Sorting
recursive
  let quickSort = lam cmp. lam seq.
    match seq with [] then []
    else match seq with [h] ++ t then
      let lr = partition (lam x. lti (cmp x h) 0) t in
      concat (quickSort cmp lr.0) (cons h (quickSort cmp lr.1))
    else never
end

mexpr

let qsort = quickSort subi in
let msort = mergeSort subi in
let s = [4,0,negi 1, 5, 3, 1, 1] in
let sorted = [negi 1, 0, 1, 1, 3, 4, 5] in
utest qsort s with sorted in
utest msort s with sorted in

let n = string2int (get argv 1) in
let seed = 5 in
let maxVal = 1000000 in

randSetSeed seed;

let s1 = init n (lam. randIntU 0 1000000) in
let s1 = qsort s1 in
-- iter (lam x. print (concat (int2string x) " ")) s1;

let s2 = init n (lam. randIntU 0 1000000) in
let s2 = msort s2 in
-- iter (lam x. print (concat (int2string x) " ")) s2;

()
