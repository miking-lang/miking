include "math.mc"

let f : Float -> Float -> Float = lam x. lam y.
  pow (addf (cos x) 1.5) (exp (addf (sin y) 1.))

let multiply : Int -> Int -> Int = lam x. lam y. muli x y

let sumTensor : Tensor[Float] -> Float = lam t.
  let sh : [Int] = tensorShape t in
  let n : Int = foldl multiply 1 sh in
  seqLoopAcc 0.0 n
    (lam acc : Float. lam i : Int.
      let x = divi i 100 in
      let y = modi i 100 in
      let rhs = tensorGetExn t [x,y] in
      addf acc rhs)

mexpr

let shape = [100, 100] in
let t1 = tensorCreateCArrayFloat shape (lam. 0.0) in
let t2 = tensorCreateCArrayFloat shape (lam. 0.0) in
let n : Int = foldl multiply 1 shape in

let op = lam out.
  loop n
    (lam i : Int.
      let x = divi i 100 in
      let y = modi i 100 in
      let v = f (int2float x) (int2float y) in
      let sh = [x, y] in
      tensorSetExn out sh v);
  sumTensor out

in

let x = accelerate (op t1) in
let y = op t2 in
utest x with y in
()
