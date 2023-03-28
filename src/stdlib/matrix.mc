-- Matrix functions

include "ext/matrix-ext.mc"

let matrixCreate: [Int] -> [Float] -> Tensor[Float] =
  tensorOfSeqExn tensorCreateCArrayFloat

let rvecCreate: Int -> [Float] -> Tensor[Float] = lam dim. matrixCreate [1,dim]

let cvecCreate: Int -> [Float] -> Tensor[Float] = lam dim. matrixCreate [dim,1]

let vecToSeqExn: all a. Tensor[a] -> [a] = lam t.
  let sh = tensorShape t in
  let n =
    match tensorShape t with [1,n] | [n,1] then n
    else error "Not a vector in vecToSeqExn"
  in
  tensorToSeqExn (tensorReshapeExn t [n])

mexpr

let _m = tensorOfSeqExn tensorCreateCArrayFloat in
let _m13 = _m [1,3] in
let _m31 = _m [3,1] in
let _eqf = lam f1. lam f2. eqi 0 (cmpfApprox 0.01 f1 f2) in
let _eqm = tensorEq _eqf in

utest vecToSeqExn (_m13 [1., 2., 3.]) with [1., 2., 3.] using eqSeq eqf in
utest vecToSeqExn (_m31 [1., 2., 3.]) with [1., 2., 3.] using eqSeq eqf in

()
