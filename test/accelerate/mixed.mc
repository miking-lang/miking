-- Example where we use acceleration using the CUDA and Futhark backends,
-- respectively.

let tensorGet : Tensor[Int] -> Int -> Int = lam t. lam i.
  tensorGetExn t [i]

let tensorSet : Tensor[Int] -> Int -> Int -> () = lam t. lam i. lam v.
  tensorSetExn t [i] v

let tensorAdd : Tensor[Int] -> Tensor[Int] -> Tensor[Int] -> () =
  lam a. lam b. lam out.
  let n = get (tensorShape a) 0 in
  accelerate (
    loop n (lam i. tensorSet out i (addi (tensorGet a i) (tensorGet b i))))

let tensorSum : Tensor[Int] -> Int = lam t.
  let sum = ref 0 in
  let n = get (tensorShape t) 0 in
  loop n (lam i. modref sum (addi (deref sum) (tensorGet t i)));
  deref sum

let seqAdd : [Int] -> [Int] -> [Int] = lam s1. lam s2.
  accelerate (map2 addi s1 s2)

let seqSum : [Int] -> Int = lam s.
  foldl addi 0 s

mexpr

let n = 100 in

let t = tensorCreateCArrayInt [muli 3 n] (lam. randIntU 0 100) in
let t1 = tensorSubExn t 0 100 in
let t2 = tensorSubExn t 100 100 in
let t3 = tensorSubExn t 200 100 in
tensorAdd t1 t2 t3;
utest addi (tensorSum t1) (tensorSum t2) with tensorSum t3 in

let s = create (muli 2 n) (lam. randIntU 0 100) in
match splitAt s n with (s1, s2) in
let s3 = seqAdd s1 s2 in
utest addi (seqSum s1) (seqSum s2) with seqSum s3 in

()
