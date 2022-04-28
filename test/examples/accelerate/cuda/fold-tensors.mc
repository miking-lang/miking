include "common.mc"

let tensorGetFloat : Tensor[Float] -> [Int] -> Float = lam t. lam sh.
  (let g : Tensor[Float] -> [Int] -> Float = tensorGetExn in g)
    t sh

let tensorSetFloat : Tensor[Float] -> [Int] -> Float -> () = lam t. lam sh. lam v.
  (let s : Tensor[Float] -> [Int] -> Float -> () = tensorSetExn in s)
    t sh v

let sumTensor : Tensor[Float] -> Float = lam t.
  let sh : [Int] = (let s : Tensor[Float] -> [Int] = tensorShape in s) t in
  let n : Int = foldl muli 1 sh in
  let cols : Int = get sh 1 in
  seqLoopAcc 0.0 n (lam acc : Float. lam i : Int.
    let r = divi i cols in
    let c = modi i cols in
    let x : Float = tensorGetFloat t [r,c] in
    addf acc x)

let addTensor : (Int, Int) -> Float -> Tensor[Float] -> Float =
  lam rc. lam acc. lam t.
  match rc with (row, col) in
  addf acc (tensorGetFloat t [row, col])

let randFloat : () -> Float = lam.
  let r = randIntU 1 1000 in
  divf 1.0 (int2float r)

mexpr

let rows = 1000 in
let cols = 2000 in
let sh = [rows, cols] in
let n : Int = foldl muli 1 sh in
let out : Tensor[Float] = tensorCreateCArrayFloat sh (lam. 0.0) in
let s : [Tensor[Float]] =
  create 5 (lam. tensorCreateCArrayFloat sh (lam. randFloat ())) in

accelerate (
  parallelLoop n (lam i : Int.
    let r = divi i cols in
    let c = modi i cols in
    let n : Int = (let l : [Tensor[Float]] -> Int = length in l) s in
    let x : Float =
      seqLoopAcc 0.0 n
        (lam acc : Float. lam i : Int.
          let t : Tensor[Float] =
            (let g : [Tensor[Float]] -> Int -> Tensor[Float] = get in g)
              s i in
          addf acc (tensorGetFloat t [r,c])) in
    tensorSetFloat out [r,c] x)
);

let x = sumTensor out in
printLn (float2string x)
