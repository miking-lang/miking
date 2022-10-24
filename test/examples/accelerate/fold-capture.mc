include "common.mc"
include "string.mc"

let t : Tensor[Int] = tensorCreateCArrayInt [5] (lam i. get i 0)

mexpr

let s : [Int] = [1,2,3] in
let x : Int = accelerate (
  seqLoopAcc 1 0 (lam. lam.
    foldl (lam acc. lam i. addi acc (tensorGetExn t [i])) 0 s)
) in
printLn (int2string x)
