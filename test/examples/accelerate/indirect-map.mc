-- Uses the map intrinsic indirectly, by calling a function that uses it from
-- the accelerate expression.
include "common.mc"
include "string.mc"

let f : [Int] -> [Int] = lam s.
  (let m : (Int -> Int) -> [Int] -> [Int] = map in m) (lam x : Int. addi 1 x) s

let sum : [Int] -> Int = lam s.
  (let f : (Int -> Int -> Int) -> Int -> [Int] -> Int = foldl in f) addi 0 s

mexpr

let n : Int = 10000 in
let s1 : [Int] = create n (lam i. i) in
let s2 : [Int] = accelerate (f s1) in
let s3 : [Int] = accelerate (f s2) in

utest addi (sum s2) n with sum s3 in
printLn (int2string (sum s2));
printLn (int2string (sum s3))