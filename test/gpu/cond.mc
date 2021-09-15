-- Conditional use of accelerated code, with decisions made based on runtime
-- values.

include "common.mc" -- printLn

let _sum : [Int] -> Int = lam s.
  foldl addi 0 s

let sum : [Int] -> Int = lam s.
  if geqi (length s) 1000 then
    printLn "Computing sum on GPU...";
    accelerate (_sum s)
  else
    printLn "Computing sum on CPU...";
    _sum s

mexpr

let randSeq = lam n. create n (lam. randIntU 0 1000) in

let s1 = sum (randSeq 100) in
let s2 = sum (randSeq 500) in
let s3 = sum (randSeq 1000) in
()
