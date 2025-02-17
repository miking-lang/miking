-- Conditional use of accelerated code, with decisions made based on runtime
-- values.

include "common.mc" -- printLn

let add : Int -> Int -> Int = lam x. lam y. addi x y

let _sum : [Int] -> Int = lam s. reduce add 0 s

let sum : [Int] -> Int = lam s.
  if geqi (length s) 1000 then
    accelerate (_sum s)
  else
    _sum s

mexpr

let randSeq = lam n. create n (lam. randIntU 0 1000) in

let s1 = sum (randSeq 100) in
let s2 = sum (randSeq 500) in
let s3 = sum (randSeq 1000) in
()
