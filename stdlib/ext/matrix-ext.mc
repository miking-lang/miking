-- External (float) matrix functions, where we represent matrices using tensors.

include "math.mc"
include "tensor.mc"

external externalMatrixExponential : Tensor[Float] -> Tensor[Float]
let matrixExponential = lam m. externalMatrixExponential m

external externalMatrixTranspose : Tensor[Float] -> Tensor[Float]
let matrixTranspose = lam m. externalMatrixTranspose m

external externalMatrixMulFloat : Float -> Tensor[Float] -> Tensor[Float]
let matrixMulFloat = lam f. lam m. externalMatrixMulFloat f m

external externalMatrixMul : Tensor[Float] -> Tensor[Float] -> Tensor[Float]
let matrixMul = lam m1. lam m2. externalMatrixMul m1 m2

mexpr

let _m = tensorOfSeqExn tensorCreateCArrayFloat [3,3] in
let _eqf = lam f1. lam f2. eqi 0 (cmpfApprox 0.01 f1 f2) in
let _eqm = tensorEq _eqf in

let t = tensorCreateCArrayFloat [3,3] (lam. 1.) in
utest matrixExponential t with
  let d = 7.36185 in
  let o = 6.36185 in
  _m [d, o, o,
      o, d, o,
      o, o, d]
using _eqm in

utest matrixTranspose
   (_m [1., 2., 3.,
        4., 5., 6.,
        7., 8., 9.])
with
   (_m [1., 4., 7.,
        2., 5., 8.,
        3., 6., 9.])
using _eqm in

utest matrixMulFloat
   2.0
   (_m [1., 2., 3.,
        4., 5., 6.,
        7., 8., 9.])
with
   (_m [2., 4., 6.,
        8., 10., 12.,
        14., 16., 18.])
using _eqm in

utest matrixMul
   (_m [1., 2., 3.,
        4., 5., 6.,
        7., 8., 9.])
   (_m [1., 2., 3.,
        4., 5., 6.,
        7., 8., 9.])
with
   (_m [30.,  36.,  42.,
        66.,  81.,  96.,
        102., 126., 150.])
using _eqm in

()
