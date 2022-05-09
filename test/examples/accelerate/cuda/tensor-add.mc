include "common.mc"
include "string.mc"
include "tensor.mc"

mexpr

let dim = [2,3,4] in
let t = tensorCreateCArrayInt dim (cartesianToLinearIndex dim) in

-- You can either return the new tensor directly.
let t = accelerate
(
  let a = tensorGetExn t [1,2,3] in
  let b = tensorGetExn t [1,1,1] in
  let c = addi a b in
  tensorSetExn t [0,0,0] c;
  t
) in
printLn (int2string (tensorGetExn t [0,0,0]));

-- Or you can return unit, in which case the tensor will still have been updated.
accelerate
(
  let a = tensorGetExn t [1,2,2] in
  let b = tensorGetExn t [0,1,2] in
  let c = addi a b in
  tensorSetExn t [0,0,0] c
);

printLn (int2string (tensorGetExn t [0,0,0]))
