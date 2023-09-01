include "common.mc" -- printLn
include "string.mc" -- int2string

mexpr

let add : Int -> Int -> Int = lam x. lam y. addi x y in

let zip : [Int] -> [Int] -> Int = lam a. lam b.
  utest length a with length b in
  reduce add 0 (map2 add a b)
in

let s1 : [Int] = create 100 (lam i. i) in
let s2 : [Int] = create 100 (lam i. subi 100 i) in
let x : Int = accelerate (
  utest length s1 with length s2 in
  zip s1 s2) in
utest x with 10000 in
()
