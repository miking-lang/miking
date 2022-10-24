include "common.mc" -- printLn

let tensorSum : Tensor[Float] -> Float = lam t.
  let sh = tensorShape t in
  let n = foldl muli 1 sh in
  let sum = ref 0.0 in
  let t = tensorReshapeExn t [n] in
  loop n (lam i : Int. modref sum (addf (deref sum) (tensorGetExn t [i])));
  deref sum

mexpr

let shape = [5,5,5] in
let a : Tensor[Float] = tensorCreateCArrayFloat shape (lam. 1.0) in
let b : Tensor[Float] = tensorCreateCArrayFloat shape (lam. 2.0) in
let c : Tensor[Float] = tensorCreateCArrayFloat shape (lam. 0.0) in
let n : Int = foldl muli 1 shape in

accelerate (
  seqLoop n
    (lam i : Int.
      let x = modi i 5 in
      let y = modi (divi i 5) 5 in
      let z = modi (divi i 25) 5 in
      let sh = [x,y,z] in
      let fst : Float = tensorGetExn a sh in
      let snd : Float = tensorGetExn b sh in
      tensorSetExn c sh (addf fst snd))
);

printLn (concat "Sum on CPU: " (float2string (tensorSum c)));

-- Create a fresh tensor so that we don't reuse the same values for 'c'.
let c = tensorCreateCArrayFloat shape (lam. 0.0) in

accelerate (
  loop n
    (lam i : Int.
      let x = modi i 5 in
      let y = modi (divi i 5) 5 in
      let z = modi (divi i 25) 5 in
      let sh = [x,y,z] in
      let fst : Float = tensorGetExn a sh in
      let snd : Float = tensorGetExn b sh in
      tensorSetExn c sh (addf fst snd))
);

printLn (concat "Sum on GPU: " (float2string (tensorSum c)))
