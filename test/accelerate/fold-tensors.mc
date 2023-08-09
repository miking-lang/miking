include "common.mc"

let sumTensor : Tensor[Float] -> Float = lam t.
  let sh = tensorShape t in
  let n = foldl muli 1 sh in
  let cols = get sh 1 in
  seqLoopAcc 0.0 n (lam acc : Float. lam i : Int.
    let r = divi i cols in
    let c = modi i cols in
    let x = tensorGetExn t [r,c] in
    addf acc x)

let addTensor : (Int, Int) -> Float -> Tensor[Float] -> Float =
  lam rc. lam acc. lam t.
  match rc with (row, col) in
  addf acc (tensorGetExn t [row, col])

let randFloat : () -> Float = lam.
  let r = randIntU 1 1000 in
  divf 1.0 (int2float r)

mexpr

let rows = 1000 in
let cols = 2000 in
let sh = [rows, cols] in
let n = foldl muli 1 sh in
let out1 = tensorCreateCArrayFloat sh (lam. 0.0) in
let out2 = tensorCreateCArrayFloat sh (lam. 0.0) in
let s : [Tensor[Float]] =
  create 5 (lam. tensorCreateCArrayFloat sh (lam. randFloat ())) in

let op = lam out.
  loop n (lam i.
    let r = divi i cols in
    let c = modi i cols in
    let n = length s in
    let x =
      seqLoopAcc 0.0 n
        (lam acc. lam i.
          let t = get s i in
          addf acc (tensorGetExn t [r,c])) in
    tensorSetExn out [r,c] x)
in
let x = accelerate (op out1) in
let y = op out2 in
utest sumTensor out1 with sumTensor out2 in
()
