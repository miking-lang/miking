include "common.mc"
include "string.mc"

let t1 : Tensor[Int] = tensorCreateCArrayInt [2] (lam. 1)
let t2 : Tensor[Int] = tensorCreateCArrayInt [4] (lam. 2)
let s : [Tensor[Int]] = [t1, t2]

mexpr

let z = accelerate (
  loop 1 (lam. ());
  let fst = get s 0 in
  let snd = get s 1 in
  let x = tensorGetExn fst [0] in
  let y = tensorGetExn snd [0] in
  addi x y
) in

utest z with 3 in
()
