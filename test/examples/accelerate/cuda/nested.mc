include "common.mc"

lang NestedDataTypeLang
  syn DataType =
  | Direct Tensor[Float]
  | Indirect {a : [Tensor[Float]], b : Float}
  | NonTensor Float

  sem eval : DataType -> Float
  sem eval =
  | Direct t -> tensorGetExn t [0]
  | Indirect t ->
    let ta : [Tensor[Float]] = t.a in
    let t : Tensor[Float] = get ta 0 in
    tensorGetExn t [0]
  | NonTensor f -> f
end

mexpr

use NestedDataTypeLang in

let s1 : DataType = NonTensor 3.5 in
let s2 : DataType = Direct (tensorCreateCArrayFloat [1] (lam. 6.5)) in
let x : Float = accelerate (addf (eval s1) (eval s2)) in
let y : Float = addf (eval s1) (eval s2) in
printLn (join [float2string x, " ", float2string y])
