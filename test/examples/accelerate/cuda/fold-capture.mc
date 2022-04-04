include "common.mc"
include "string.mc"

let t : Tensor[Int] = tensorCreateCArrayInt [5] (lam i. get i 0)

let tensorGetInt : Tensor[Int] -> [Int] -> Int = lam t. lam i.
  (let g : Tensor[Int] -> [Int] -> Int = tensorGetExn in g) t i

mexpr

let s : [Int] = [1,2,3] in
let x : Int = accelerate (
  (let f : (Int -> Int -> Int) -> Int -> [Int] -> Int = foldl in f)
    (lam acc : Int. lam i : Int. addi acc (tensorGetInt t [i])) 0 s
) in
printLn (int2string x)
