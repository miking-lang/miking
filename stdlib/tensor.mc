-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the tensor intrinsics.

include "option.mc"
include "seq.mc"

-- Default to dense tensors
let tensorCreate = tensorCreateDense

let _prod = foldl muli 1

let _rowMajorOfsToIndex = lam shape. lam k.
  let f = lam kis : (Int, [Int]). lam d : Int.
    let k = kis.0 in
    let is = kis.1 in
    (divi k d, cons (modi k d) is)
  in
  let r : (Int, [Int]) = foldl f (k, []) shape in
  r.1

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

-- Construct a tensor of shape `shape` from a sequence `seq`.
let tensorOfSeqOrElse :
  (Unit -> Tensor[a]) ->
  ([Int] -> ([Int] -> a) -> Tensor[a]) ->
  [Int] ->
  [a] ->
  Tensor[a] =
lam f. lam tcreate. lam shape. lam seq.
  let n = length seq in
  if neqi n (_prod shape) then f ()
  else
    let t = tcreate [n] (lam is. get seq (get is 0)) in
    tensorReshapeExn t shape

let tensorOfSeqExn
  : ([Int] -> ([Int] -> a) -> Tensor[a]) -> [Int] -> [a] -> Tensor[a] =
  tensorOfSeqOrElse
    (lam. error "Empty seq in tensorOfSeqExn")

-- Construct a sequence from a rank 1 tensor `t`.
let tensorToSeqOrElse : (Unit -> [a]) -> Tensor[a] -> [a] =
lam f. lam t.
  if neqi (tensorRank t) 1 then f ()
  else
    let n = get (tensorShape t) 0 in
    unfoldr (lam i. if lti i n
               then Some (tensorGetExn t [i], addi i 1) else None ())
            0

let tensorToSeqExn : Tensor[a] -> [a] =
  tensorToSeqOrElse (lam. error "Not rank 1 tensor in tensorToSeqExn")

utest tensorToSeqExn (tensorOfSeqExn tensorCreateCArrayInt [0] [])
with []

utest tensorToSeqExn (tensorOfSeqExn tensorCreateCArrayInt [4] [1, 2, 3, 4])
with [1, 2, 3, 4] using eqSeq eqi

utest
  tensorToSeqExn
    (tensorOfSeqExn tensorCreateCArrayFloat [4] [1., 2., 3., 4.])
with [1., 2., 3., 4.] using eqSeq eqf

utest tensorToSeqExn (tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4])
with [1, 2, 3, 4] using eqSeq eqi

-- Create a tensor filled with values `v`.
let tensorDenseRepeat : [Int] -> a -> Tensor[a] =
lam shape. lam v.
  tensorCreateDense shape (lam. v)

utest
  let t = tensorDenseRepeat [4] 0 in
  tensorToSeqExn t
with [0, 0, 0, 0] using eqSeq eqi


-- The number of elements in a tensor `t`.
let tensorSize : Tensor[a] -> Int =
lam t. _prod (tensorShape t)

utest tensorSize (tensorCreateDense [1, 2, 3] (lam. 0)) with 6
utest tensorSize (tensorCreateDense [] (lam. 0)) with 1


-- Map the elements of `t1` to the elements of `t2` via the function `f`,
-- where `t1` and `t2` has to have the same shape.
let tensorMapOrElse
  : (Unit -> Unit) -> (a -> b) -> Tensor[a] -> Tensor[b] -> Unit =
lam f. lam g. lam t1. lam t2.
  if eqSeq eqi (tensorShape t1) (tensorShape t2) then
    let n = tensorSize t1 in
    let v1 = tensorReshapeExn t1 [n] in
    let v2 =  tensorReshapeExn t2 [n] in
    tensorIterSlice
      (lam i. lam e. tensorSetExn v2 [i] (g (tensorGetExn e [])))
      v1
  else f ()

let tensorMapExn =
  tensorMapOrElse (lam. error "Tensor shape mismatch in tensorMap")

utest
  let t1 = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  let t2 = tensorCreateDense [4] (lam. []) in
  tensorMapExn (lam x. [x]) t1 t2;
  tensorToSeqExn t2
with [[1], [2], [3], [4]]

utest
  let t = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  tensorMapExn (addi 1) t t;
  tensorToSeqExn t
with [2, 3, 4, 5]

utest
  let t = tensorDenseRepeat [] 0 in
  tensorMapExn (addi 1) t t;
  tensorGetExn t []
with 1


-- Applies function `f` to the elements of `t`.
let tensorMapSelf : (a -> a) -> Tensor[a] -> Unit =
  lam f. lam t. tensorMapExn f t t

utest
  let t = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  tensorMapSelf (addi 1) t;
  tensorToSeqExn t
with [2, 3, 4, 5]


-- Map the index and elements of `t1` to the elements of `t2` via the function
-- `f`, where `t1` and `t2` has to have the same shape.
let tensorMapiOrElse
  : (Unit -> Unit) -> ([Int] -> a -> b) -> Tensor[a] -> Tensor[b] -> Unit =
lam f. lam g. lam t1. lam t2.
  let shape = tensorShape t1 in
  if eqSeq eqi shape (tensorShape t2) then
    let n = tensorSize t1 in
    let v1 = tensorReshapeExn t1 [n] in
    let v2 =  tensorReshapeExn t2 [n] in
    tensorIterSlice
      (lam i. lam e.
        tensorSetExn
          v2
          [i]
          (g (_rowMajorOfsToIndex shape i) (tensorGetExn e [])))
      v1
  else f ()

let tensorMapiExn =
  tensorMapiOrElse (lam. error "Tensor shape mismatch in tensorMap")

utest
  let t1 = tensorOfSeqExn tensorCreateDense [2, 2] [1, 2, 3, 4] in
  let t2 = tensorCreateDense [2, 2] (lam. ([], 0)) in
  tensorMapiExn (lam is. lam x. (is, x)) t1 t2;
  tensorToSeqExn (tensorReshapeExn t2 [tensorSize t2])
with [([0, 0], 1), ([0, 1], 2), ([1, 0], 3), ([1, 1], 4)]

let tensorMapiSelf : ([Int] -> a -> a) -> Tensor[a] -> Unit =
  lam f. lam t. tensorMapiExn f t t


-- Element-wise equality of tensor `t1` and `t2` using `eq`
let eqTensor : (a -> b -> Bool) -> Tensor[a] -> Tensor[b] -> Bool =
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
  let t1 = tensorDenseRepeat [] 0 in
  let t2 = tensorDenseRepeat [1] 0 in
  eqTensor eqi t1 t2
with false

utest
  let t1 = tensorDenseRepeat [2, 3] 0 in
  let t2 = tensorDenseRepeat [3, 2] 0 in
  eqTensor eqi t1 t2
with false

utest
  let t1 = tensorDenseRepeat [2, 3] 0 in
  let t2 = tensorDenseRepeat [2, 3] 0 in
  eqTensor eqi t1 t2
with true

utest
  let t1 = tensorDenseRepeat [2, 3] [0] in
  let t2 = tensorDenseRepeat [2, 3] 0 in
  eqTensor (lam x. lam y. eqi (head x) y) t1 t2
with true

utest
  let t1 = tensorOfSeqExn tensorCreateDense [2] [1, 2] in
  let t2 = tensorOfSeqExn tensorCreateDense [2] [1, 3] in
  eqTensor eqi t1 t2
with false


-- Left folds `f acc t` over the zero'th dimension of `t1`, where `acc` is the
-- accumulator and `t` is the i'th slice of `t1`.
let tensorFoldlSlice
  : (b -> Tensor[a] -> b) -> b -> Tensor[a] -> b =
  lam f. lam acc. lam t1.
  let accr = ref acc in
  tensorIterSlice
    (lam i. lam t.
      let acc = f (deref accr) t in
      modref accr acc)
    t1;
  deref accr

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorFoldlSlice (lam acc. lam t. addi acc (tensorGetExn t [])) 0 t
with 6


-- Left folds `f acc el` over all elements `el` of `t` in row-major order,
-- where `acc` is the accumulator.
let tensorFoldl : (b -> a -> b) -> b -> Tensor[a] -> b =
  lam f. lam acc. lam t.
  let t = tensorReshapeExn t [tensorSize t] in
  tensorFoldlSlice (lam acc. lam t. f acc (tensorGetExn t [])) acc t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorFoldl addi 0 t
with 6

-- Iterates through the elements of `t` in row-major order, applying the
-- function `f` on each index and element.
let tensorIteri : ([Int] -> a -> Unit) -> Tensor[a] -> Unit =
  lam f. lam t.
  let shape = tensorShape t in
  let t = tensorReshapeExn t [tensorSize t] in
  tensorIterSlice
    (lam i. lam t. f (_rowMajorOfsToIndex shape i) (tensorGetExn t [])) t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorIteri (lam i. lam x. tensorSetExn t i (addi x x)) t;
  tensorToSeqExn t
with [2, 4, 6]


-- Iterates through the elements of `t` in row-major order, applying the
-- function `f` on each element.
let tensorIter : (a -> Unit) -> Tensor[a] -> Unit =
  lam f. tensorIteri (lam. lam x. f x)


-- The maximum element in `t` as defined by `cmp`.
let tensorMax : (a -> a -> Int) -> Tensor[a] -> a =
  lam cmp. lam t.
    if eqi (tensorRank t) 0 then tensorGetExn t []
    else
      let t = tensorReshapeExn t [tensorSize t] in
      tensorFoldlSlice
        (lam max. lam t.
          let x = tensorGetExn t [] in
          if gti (cmp x max) 0 then x else max)
        (tensorGetExn t [0])
        t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorMax subi t
with 3

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  tensorMax subi t
with 6


-- The minimum element in `t` as defined by `cmp`.
let tensorMin : (a -> a -> Int) -> Tensor[a] -> a =
  lam cmp. lam t. tensorMax (lam x. lam y. cmp y x) t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorMin subi t
with 1

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  tensorMin subi t
with 1


-- Finds element and index `Some (el, i)` in `t` satisfying predicate `p`. If
-- no such element is found then `None` is returned.
let tensorFindi : (a -> Bool) -> Tensor[a] -> Option (a, [Int]) =
  lam p. lam t.
    let n = tensorSize t in
    let shape = tensorShape t in
    let t = tensorReshapeExn t [n] in
    recursive let work = lam i.
      if lti i n then
        let e = tensorGetExn t [i] in
        if p e then Some (e, _rowMajorOfsToIndex shape i)
        else work (addi i 1)
      else None ()
    in
    work 0

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  match tensorFindi (eqi 1) t with Some x then x else (negi 1, [])
with (1, [0])

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  match tensorFindi (eqi 3) t with Some x then x else (negi 1, [])
with (3, [1,0])


-- Finds element `Some el` in `t` satisfying predicate `p`. If
-- no such element is found then `None` is returned.
let tensorFind : (a -> Bool) -> Tensor[a] -> Option a =
  lam p. lam t.
    let x = tensorFindi p t in
    match x with Some (x, _) then Some x
    else match x with None _ then None ()
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  match tensorFind (eqi 1) t with Some x then x else negi 1
with 1

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  match tensorFind (eqi 3) t with Some x then x else negi 1
with 3


-- Finds index `Some i` in `t` of element satisfying predicate `p`. If no such
-- element is found then `None` is returned.
let tensorIndex : (a -> Bool) -> Tensor[a] -> Option [Int] =
  lam p. lam t.
    let x = tensorFindi p t in
    match x with Some (_, is) then Some is
    else match x with None _ then None ()
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  match tensorIndex (eqi 1) t with Some x then x
  else []
with [0]

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  match tensorIndex (eqi 3) t with Some x then x
  else []
with [1,0]


-- `true` if `p x` for some `x` in `t`, else `false`.
let tensorAny : (a -> Bool) -> Tensor[a] -> Bool =
  lam p. lam t.
    let x = tensorFindi p t in
    match x with Some _ then true
    else match x with None _ then false
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  tensorAny (eqi 3) t
with true

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  tensorAny (eqi 7) t
with false


-- `true` if `p x` for all `x` in `t`, else `false`.
let tensorAll : (a -> Bool) -> Tensor[a] -> Bool =
  lam p. lam t.
    let x = tensorFindi (lam x. not (p x)) t in
    match x with Some _ then false
    else match x with None _ then true
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  tensorAll (gti 7) t
with true

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  tensorAll (gti 6) t
with false


-- All dims of tensor `t` are equal.
let tensorDimsEqual = lam t.
  let shape = tensorShape t in
  if null shape then true
  else all (eqi (head shape)) (tail shape)

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 2] [1, 2, 3, 4] in
  tensorDimsEqual t
with true

utest
  let t = tensorOfSeqExn tensorCreateDense [1, 4] [1, 2, 3, 4] in
  tensorDimsEqual t
with false


-- Filter elements of `t` given predicate `p`.
let tensorFilter : (a -> Bool) -> Tensor[a] -> [a] =
  lam p. lam t.
    let t = tensorReshapeExn t [tensorSize t] in
    tensorFoldlSlice
      (lam a. lam t.
        let e = tensorGetExn t [] in
        if p e then snoc a e else a)
      []
      t

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3] [1, 2, 3, 4, 5, 6] in
  tensorFilter (lti 3) t
with [4, 5, 6]

mexpr

-- Tensors are mutable data structures and can be of up to rank 16. The index
-- of an element is represented as a sequence of integers.

-- We construct tensors using `tensorCreateDense shape f`, where `shape` is a
-- sequence denoting the shape of the tensor and `f` is a function taking a
-- index as an argument and returning the element at that index.

-- We can construct a zero-order tensor with value 'a' as
let t0 = tensorCreateDense [] (lam. 'a') in
utest tensorRank t0 with 0 in
utest tensorShape t0 with [] in

-- We can access and mutate elements in a tensor using
utest tensorSetExn t0 [] 'b' with () in
utest tensorGetExn t0 [] with 'b' in

-- We can construct a rank 1 tensor (i.e. vector) as
let t1 = tensorCreateDense [9] (lam i. addi (get i 0) 1) in
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
tensorMapSelf (lam. 0) r2;
utest tensorToSeqExn t1 with [2, 2, 3, 0, 0, 0, 7, 8, 9] in
-- where we use `tensorFill` from `tensor.mc`

-- We can get a subset of the rows of t2 by restricting its 0th dimension.
let s1 = tensorSubExn t2 1 2 in
utest tensorShape s1 with [2, 3] in
utest tensorToSeqExn (tensorReshapeExn s1 [6]) with [0, 0, 0, 7, 8, 9] in

-- We can also copy the content of one tensor to another
let s2 = tensorSubExn t2 0 2 in
utest tensorBlitExn s1 s2 with () in

-- As before, none of these operations (except copy) does any copying
-- and the data is shared.
utest tensorToSeqExn t1 with [0, 0, 0, 7, 8, 9, 7, 8, 9] in

()
