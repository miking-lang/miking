-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the tensor intrinsics.

include "seq.mc"

type Tensor a

-- Construct a rank 1 tensor from a non-empty sequence.
let tensorOfSeqOrElse : (Unit -> Tensor a) -> [a] -> Tensor a =
lam f. lam seq.
  let n = length seq in
  if eqi n 0 then f ()
  else
    tensorCreate [n] (lam is. get seq (get is 0))

-- Construct a sequence from a rank 1 tensor.
let tensorToSeqOrElse : (Unit -> [a]) -> Tensor a -> [a] =
lam f. lam t.
  if neqi (tensorRank t) 1 then f ()
  else
    let n = get (tensorShape t) 0 in
    unfoldr (lam i. if lti i n
               then Some (tensorGetExn t [i], addi i 1) else None ())
            0

let tensorOfSeqExn : [a] -> Tensor a =
  tensorOfSeqOrElse (lam. error "Empty seq in tensorOfSeqExn")

let tensorToSeqExn : Tensor a -> [a] =
  tensorToSeqOrElse (lam. error "Not rank 1 tensor in tensorToSeqExn")

utest tensorToSeqExn (tensorOfSeqExn [1, 2, 3, 4]) with [1, 2, 3, 4]


-- The number of elements in a tensor.
let tensorSize : Tensor a -> Int =
lam t.
  foldl muli 1 (tensorShape t)

utest tensorSize (tensorCreate [1, 2, 3] (lam. 0)) with 6
utest tensorSize (tensorCreate [] (lam. 0)) with 1

-- Map the elements of t1 to the elements of t2 using the function f, where t1
-- and t2 has to have the same shape.
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


-- Fill a tensor with values.
let tensorFill : Tensor a -> a -> Unit =
lam t. lam v. tensorMapExn (lam. v) t t

utest
  let t = tensorOfSeqExn [1, 2, 3, 4] in
  tensorFill t 0;
  tensorToSeqExn t
with [0, 0, 0, 0]


-- Create a tensor filled with values.
let tensorRepeat : [Int] -> a -> Tensor a =
lam shape. lam v.
  tensorCreate shape (lam. v)

utest
  let t = tensorRepeat [4] 0 in
  tensorToSeqExn t
with [0, 0, 0, 0]

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
