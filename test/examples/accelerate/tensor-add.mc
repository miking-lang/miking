include "common.mc"
include "string.mc"
include "tensor.mc"

mexpr

let dim = [2,3,4] in
let t = tensorCreateCArrayInt dim (cartesianToLinearIndex dim) in

-- The tensor is updated inside the accelerate, and this side-effect is
-- propagated back, as shown in the following print expression.
accelerate
(
  let a = tensorGetExn t [1,2,2] in
  let b = tensorGetExn t [0,1,2] in
  let c = addi a b in
  tensorSetExn t [0,0,0] c
);

printLn (int2string (tensorGetExn t [0,0,0]))
