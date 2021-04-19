-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the tensor intrinsics.

include "option.mc"
include "seq.mc"

type Tensor a

let _prod = foldl muli 1

let _rowMajorOfsToIndex = lam shape. lam k.
  let f = lam kis. lam d.
    let k = kis.0 in
    let is = kis.1 in
    (divi k d, cons (modi k d) is)
  in
  (foldl f (k, []) shape).1

-- Folds `f` over the range `start` `stop` using accumulator `acc`
let indexFoldu : (a -> Int -> a) -> a -> Int -> Int -> a =
lam f. lam acc. lam start. lam stop.
  recursive let work = lam acc. lam i.
    if lti i stop then work (f acc i) (addi i 1) else acc
  in
  work acc start

utest indexFoldu (lam seq. lam i. snoc seq i) [] 0 4 with [0, 1, 2, 3]
utest indexFoldu (lam seq. lam i. snoc seq i) [] 0 0 with [] using (eqSeq eqi)
utest indexFoldu (lam seq. lam i. snoc seq i) [] 1 4 with [1, 2, 3]
utest indexFoldu (lam seq. lam i. snoc seq i) [] 2 1 with [] using (eqSeq eqi)


-- Folds `f` over the indexes up to `shape` in row-major order and accumulator
-- `acc`
let indexFoldRM : (a -> [Int] -> a) -> a -> [Int] -> a =
lam f. lam acc. lam shape.
  let size = _prod shape in
  recursive let work = lam acc. lam k.
    if lti k size then
      let is = _rowMajorOfsToIndex shape k in
      work (f acc is) (addi k 1)
    else acc
  in
  work acc 0

utest indexFoldRM (lam seq. lam is. snoc seq is) [] []
with [[]] using eqSeq (eqSeq eqi)

utest indexFoldRM (lam seq. lam is. snoc seq is) [] [2, 2]
with [[0, 0], [0, 1], [1, 0], [1, 1]] using eqSeq (eqSeq eqi)


-- Folds `f` over the indexes of `shape` in row-major order with accumulator
-- `acc`. If `f acc is` is `None ()` then the result is `None ()`.
let optionIndexFoldRMM : (a -> [Int] -> Option a) -> a -> [Int] -> Option a =
lam f. lam acc. lam shape.
  let size = _prod shape in
  recursive let work = lam acc. lam k.
    if lti k size then
      let is = _rowMajorOfsToIndex shape k in
      let res =  f acc is in
      match res with Some acc then
        work acc (addi k 1)
      else match res with None _ then
        None ()
      else never
    else Some acc
  in
  work acc 0

utest optionFoldlM (lam acc. lam x. if lti x 4 then Some x else None ())
        0 [1,2,2,4]
with None () using optionEq (eqSeq (eqSeq eqi))

utest optionIndexFoldRMM
  (lam seq. lam is.
     if lti (length seq) 5 then Some (snoc seq is) else None ())
  []
  []
with Some [[]] using optionEq (eqSeq (eqSeq eqi))

utest optionIndexFoldRMM
  (lam seq. lam is.
     if lti (length seq) 5 then Some (snoc seq is) else None ())
  []
  [2, 2]
with Some [[0, 0], [0, 1], [1, 0], [1, 1]] using optionEq (eqSeq (eqSeq eqi))

utest optionIndexFoldRMM
  (lam seq. lam is.
     if lti (length seq) 3 then Some (snoc seq is) else None ())
  []
  [2, 2]
with None () using optionEq (eqSeq (eqSeq eqi))


-- Construct a rank 1 tensor from a non-empty sequence `seq`.
let tensorOfSeqOrElse : (Unit -> Tensor a) -> [a] -> Tensor a =
lam f. lam seq.
  let n = length seq in
  if eqi n 0 then f ()
  else
    tensorCreate [n] (lam is. get seq (get is 0))

let tensorOfSeqExn : [a] -> Tensor a =
  tensorOfSeqOrElse (lam. error "Empty seq in tensorOfSeqExn")


-- Construct a sequence from a rank 1 tensor `t`.
let tensorToSeqOrElse : (Unit -> [a]) -> Tensor a -> [a] =
lam f. lam t.
  if neqi (tensorRank t) 1 then f ()
  else
    let n = get (tensorShape t) 0 in
    unfoldr (lam i. if lti i n
               then Some (tensorGetExn t [i], addi i 1) else None ())
            0

let tensorToSeqExn : Tensor a -> [a] =
  tensorToSeqOrElse (lam. error "Not rank 1 tensor in tensorToSeqExn")

utest tensorToSeqExn (tensorOfSeqExn [1, 2, 3, 4]) with [1, 2, 3, 4]
using eqSeq eqi


-- Create a tensor filled with values `v`.
let tensorRepeat : [Int] -> a -> Tensor a =
lam shape. lam v.
  tensorCreate shape (lam. v)

utest
  let t = tensorRepeat [4] 0 in
  tensorToSeqExn t
with [0, 0, 0, 0] using eqSeq eqi


-- The number of elements in a tensor `t`.
let tensorSize : Tensor a -> Int =
lam t. _prod (tensorShape t)

utest tensorSize (tensorCreate [1, 2, 3] (lam. 0)) with 6
utest tensorSize (tensorCreate [] (lam. 0)) with 1


-- Map the elements of `t1` to the elements of `t2` using the function `f`,
-- where `t1` and `t2` has to have the same shape.
let tensorMapOrElse : (Unit -> Unit) -> (a -> b) -> Tensor a -> Tensor b -> Unit =
lam f. lam g. lam t1. lam t2.
  if eqSeq eqi (tensorShape t1) (tensorShape t2) then
    let n = tensorSize t1 in
    let v1 = tensorReshapeExn t1 [n] in
    let v2 =  tensorReshapeExn t2 [n] in
    tensorIteri (lam i. lam e. tensorSetExn v2 [i] (g (tensorGetExn e [])))
                v1
  else f ()

let tensorMapExn =
  tensorMapOrElse (lam. error "Tensor shape mismatch in tensorMap")

utest
  let t1 = tensorOfSeqExn [1, 2, 3, 4] in
  let t2 = tensorCreate [4] (lam. []) in
  tensorMapExn (lam x. [x]) t1 t2;
  tensorToSeqExn t2
with [[1], [2], [3], [4]]

utest
  let t = tensorOfSeqExn [1, 2, 3, 4] in
  tensorMapExn (addi 1) t t;
  tensorToSeqExn t
with [2, 3, 4, 5]

utest
  let t = tensorRepeat [] 0 in
  tensorMapExn (addi 1) t t;
  tensorGetExn t []
with 1


-- Fill a tensor `t` with values `v`.
let tensorFill : Tensor a -> a -> Unit =
lam t. lam v. tensorMapExn (lam. v) t t

utest
  let t = tensorOfSeqExn [1, 2, 3, 4] in
  tensorFill t 0;
  tensorToSeqExn t
with [0, 0, 0, 0]


-- Element-wise equality of tensor `t1` and `t2` using `eq`
let eqTensor : (a -> b -> Bool) -> Tensor a -> Tensor b -> Bool =
lam eq. lam t1. lam t2.
  if eqSeq eqi (tensorShape t1) (tensorShape t2) then
    let n = tensorSize t1 in
    let v1 = tensorReshapeExn t1 [n] in
    let v2 = tensorReshapeExn t2 [n] in

    recursive let work = lam i.
      if lti i n then
        if eq (tensorGetExn v1 [i]) (tensorGetExn v2 [i]) then
          work (addi i 1)
        else false
      else true
    in

    work 0

  else false

utest
  let t1 = tensorRepeat [] 0 in
  let t2 = tensorRepeat [1] 0 in
  eqTensor eqi t1 t2
with false

utest
  let t1 = tensorRepeat [2, 3] 0 in
  let t2 = tensorRepeat [3, 2] 0 in
  eqTensor eqi t1 t2
with false

utest
  let t1 = tensorRepeat [2, 3] 0 in
  let t2 = tensorRepeat [2, 3] 0 in
  eqTensor eqi t1 t2
with true

utest
  let t1 = tensorRepeat [2, 3] [0] in
  let t2 = tensorRepeat [2, 3] 0 in
  eqTensor (lam x. lam y. eqi (head x) y) t1 t2
with true

utest
  let t1 = tensorOfSeqExn [1, 2] in
  let t2 = tensorOfSeqExn [1, 3] in
  eqTensor eqi t1 t2
with false

mexpr

-- Tensors are mutable data structures and can be of up to rank 16. The index
-- of an element is represented as a sequence of integers.

-- We construct tensors using `tensorCreate shape f`, where `shape` is a
-- sequence denoting the shape of the tensor and `f` is a function taking a
-- index as an argument and returning the element at that index.

-- We can construct a zero-order tensor with value 'a' as
let t0 = tensorCreate [] (lam. 'a') in
utest tensorRank t0 with 0 in
utest tensorShape t0 with [] in

-- We can access and mutate elements in a tensor using
utest tensorSetExn t0 [] 'b' with () in
utest tensorGetExn t0 [] with 'b' in

-- We can construct a rank 1 tensor (i.e. vector) as
let t1 = tensorCreate [9] (lam i. addi (get i 0) 1) in
utest tensorToSeqExn t1 with [1, 2, 3, 4, 5, 6, 7, 8, 9] in
-- where `tensorToSeqExn` is defined in `tensor.mc`

-- We can reshape our rank 1 tensor into a rank 2 tensor (i.e. a matrix).
let t2 = tensorReshapeExn t1 [3, 3] in

-- Reshape does no copying and the data is shared between `t1` and `t2`
tensorSetExn t2 [0, 0] 2;
utest tensorGetExn t1 [0] with 2 in

-- We can slice the second row from `t2` as
let r2 = tensorSliceExn t2 [1] in
utest tensorToSeqExn r2 with [4, 5, 6] in

-- Slicing reduces the rank of the tensor
utest tensorRank r2 with 1 in

-- We can slice multiple dimensions at once
let e = tensorSliceExn t2 [1, 1] in
utest tensorGetExn e [] with 5 in
utest tensorRank e with 0 in

-- A slice shares data with the original tensor and no copying of data is done.
tensorFill r2 0;
utest tensorToSeqExn t1 with [2, 2, 3, 0, 0, 0, 7, 8, 9] in
-- where we use `tensorFill` from `tensor.mc`

-- We can get a subset of the rows of t2 by restricting its 0th dimension.
let s1 = tensorSubExn t2 1 2 in
utest tensorShape s1 with [2, 3] in
utest tensorToSeqExn (tensorReshapeExn s1 [6]) with [0, 0, 0, 7, 8, 9] in

-- We can also copy the content of one tensor to another
let s2 = tensorSubExn t2 0 2 in
utest tensorCopyExn s1 s2 with () in

-- As before, none of these operations (except copy) does any copying
-- and the data is shared.
utest tensorToSeqExn t1 with [0, 0, 0, 7, 8, 9, 7, 8, 9] in

()
