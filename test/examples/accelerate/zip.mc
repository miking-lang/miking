include "common.mc" -- printLn
include "string.mc" -- int2string

mexpr

let zip : [Int] -> [Int] -> Int = lam a. lam b.
  utest length a with length b in
  parallelReduce addi 0 (parallelMap2 (lam x : Int. lam y : Int. addi x y) a b)
in

let s1 : [Int] = create 100 (lam i. i) in
let s2 : [Int] = create 100 (lam i. subi 100 i) in
let x : Int = accelerate (
  utest length s1 with length s2 in
  zip s1 s2) in
printLn (int2string x)
