include "common.mc"

let sumTensor : Tensor[Float] -> Float = lam t.
  let sh : [Int] = (let s : Tensor[Float] -> [Int] = tensorShape in s) t in
  let n : Int =
    (let f : (Int -> Int -> Int) -> Int -> [Int] -> Int = foldl in f)
      (lam x : Int. lam y : Int. addi x y) 0 sh in
  let cols : Int = (let g : [Int] -> Int -> Int = get in g) sh 1 in
  seqLoopAcc 0.0 n (lam acc : Float. lam i : Int.
    let r = divi i cols in
    let c = modi i cols in
    let x : Float =
      (let g : Tensor[Float] -> [Int] -> Float = tensorGetExn in g)
        t [r, c] in
    addf acc x)

let randFloat : () -> Float = lam.
  let r = randIntU 1 1000 in
  divf 1.0 (int2float r)

mexpr

let sh = [1000, 2000] in
let s : [Tensor[Float]] =
  create 5 (lam. tensorCreateCArrayFloat sh (lam. randFloat ())) in

let x : Float = accelerate (
  (let f : (Float -> Tensor[Float] -> Float) -> Float -> [Tensor[Float]] -> Float = foldl in f)
    (lam acc : Float. lam x : Tensor[Float]. addf acc (sumTensor x))
    0.0 s
) in

printLn (float2string x)
