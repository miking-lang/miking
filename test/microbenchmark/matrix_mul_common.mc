include "benchmarkcommon.mc"

let loop_ = lam n. lam f.
  recursive let recur = lam i.
    if geqi i n then () else f i; recur (addi i 1)
  in
  recur 0

let n = 10

let _create_benchmark_data = lam tcreate.
  let mat1 =
    tcreate [n, n] (lam. int2float (randIntU 0 10))
  in
  let mat2 = tensorCopy mat1 in
  let mat3 = tensorCopy mat1 in
  (mat1, mat2, mat3)

let create_benchmark_data_dense = lam.
  _create_benchmark_data tensorCreateDense

let create_benchmark_data_carray = lam.
  _create_benchmark_data tensorCreateCArrayFloat

let benchmark = lam tcreate. lam matMul. lam.
  match _create_benchmark_data tcreate with (mat1, mat2, mat3) in
  let n = subi n 1 in
  let randomSet = lam mat. lam.
    tensorSetExn mat [randIntU 0 n, randIntU 0 n] (int2float (randIntU 0 10))
  in
  let randomGet = lam mat. lam.
    tensorGetExn mat [randIntU 0 n, randIntU 0 n]
  in
  let sum = ref 0. in
  bc_repeat (lam.
    randomSet mat1 ();
    randomSet mat2 ();
    matMul mat1 mat2 mat3;
    modref sum (addf (deref sum) (randomGet mat3 ())));
  print (float2string (deref sum))

let test = lam mat_mul.
  let mat1 = tensorCreateDense [9] (lam idx. int2float (head idx)) in
  let mat1 = tensorReshapeExn mat1 [3, 3] in
  let mat2 = tensorCopy mat1 in
  let mat3 = tensorCopy mat1 in
  mat_mul mat1 mat2 mat3;
  print (tensor2string float2string mat1);
  print (tensor2string float2string mat2);
  print (tensor2string float2string mat3);
  ()
