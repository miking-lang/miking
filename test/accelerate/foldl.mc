include "common.mc"
include "string.mc"

let f : Int -> Int -> Int = lam x. lam y. addi x y

mexpr

let n = 1000 in
let s = create n (lam i. i) in
let x = accelerate (loop 1 (lam. ()); foldl f 0 s) in
utest x with divi (muli n (subi n 1)) 2 in
()
