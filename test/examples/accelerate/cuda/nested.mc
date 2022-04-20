include "common.mc"

let tensorGetFloat : Tensor[Float] -> [Int] -> Float = lam t. lam idx.
  (let g : Tensor[Float] -> [Int] -> Float = tensorGetExn in g)
    t idx

lang NestedDataTypeLang
  syn DataType =
  | Direct Tensor[Float]
  | Indirect {a : [Tensor[Float]], b : Float}
  | NonTensor Float

  sem eval : DataType -> Float
  sem eval =
  | Direct t -> tensorGetFloat t [0]
  | Indirect t ->
    let ta : [Tensor[Float]] = t.a in
    let t : Tensor[Float] =
      (let g : [Tensor[Float]] -> Int -> Tensor[Float] = get in g) ta 0 in
    tensorGetFloat t [0]
  | NonTensor f -> f
end

mexpr

use NestedDataTypeLang in

let s1 : DataType = NonTensor 3.5 in
let s2 : DataType = Direct (tensorCreateCArrayFloat [1] (lam. 6.5)) in
let x : Float = accelerate (addf (eval s1) (eval s2)) in
let y : Float = addf (eval s1) (eval s2) in
printLn (join [float2string x, " ", float2string y])
