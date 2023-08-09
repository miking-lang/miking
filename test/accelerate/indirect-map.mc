-- Uses the map intrinsic indirectly, by calling a function that uses it from
-- the accelerate expression.
include "common.mc"
include "string.mc"

let f : [Int] -> [Int] = lam s.
  map (addi 1) s

let sum : [Int] -> Int = lam s.
  foldl addi 0 s

mexpr

let n : Int = 10000 in
let s1 : [Int] = create n (lam i. i) in
let s2 : [Int] = accelerate (f s1) in
let s3 : [Int] = accelerate (f s2) in

utest addi (sum s2) n with sum s3 in
()
