-- Matrix functions

include "ext/matrix-ext.mc"

let matrixCreate: [Int] -> [Float] -> Tensor[Float] =
  tensorOfSeqExn tensorCreateCArrayFloat

let rvecCreate: Int -> [Float] -> Tensor[Float] = lam dim. matrixCreate [1,dim]

let cvecCreate: Int -> [Float] -> Tensor[Float] = lam dim. matrixCreate [dim,1]
