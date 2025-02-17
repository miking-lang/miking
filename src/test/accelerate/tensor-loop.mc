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
let a = tensorCreateCArrayFloat shape (lam. 1.0) in
let b = tensorCreateCArrayFloat shape (lam. 2.0) in
let c = tensorCreateCArrayFloat shape (lam. 0.0) in
let n = foldl muli 1 shape in

accelerate (
  seqLoop n
    (lam i.
      let x = modi i 5 in
      let y = modi (divi i 5) 5 in
      let z = modi (divi i 25) 5 in
      let sh = [x,y,z] in
      let fst = tensorGetExn a sh in
      let snd = tensorGetExn b sh in
      tensorSetExn c sh (addf fst snd))
);

-- Create a fresh tensor so that we don't reuse the same values for 'c'.
let d = tensorCreateCArrayFloat shape (lam. 0.0) in

accelerate (
  loop n
    (lam i.
      let x = modi i 5 in
      let y = modi (divi i 5) 5 in
      let z = modi (divi i 25) 5 in
      let sh = [x,y,z] in
      let fst = tensorGetExn a sh in
      let snd = tensorGetExn b sh in
      tensorSetExn d sh (addf fst snd))
);

utest tensorSum c with tensorSum d in
()
