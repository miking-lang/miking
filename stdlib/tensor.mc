-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the tensor intrinsics.

include "option.mc"
include "seq.mc"
include "string.mc"

let _prod = foldl muli 1

type TCreate a = [Int] -> (([Int] -> a) -> Tensor[a])

----------------------------
-- TENSOR INDEX FUNCTIONS --
----------------------------

-- Converts linear index `k` to Cartesian index in row-major order.
let linearToCartesianIndex = lam shape. lam k.
  let f = lam d. lam kidx.
    match kidx with (k, idx) then
      (divi k d, cons (modi k d) idx)
    else never
  in
  let r : (Int, [Int]) = foldr f (k, []) shape in
  r.1

utest linearToCartesianIndex [2] 0 with [0]
utest linearToCartesianIndex [2] 1 with [1]
utest linearToCartesianIndex [2, 3] 2 with [0, 2]
utest linearToCartesianIndex [2, 3] 3 with [1, 0]


-- Converts Cartesian index `idx` to linear index assuming row-major order.
let cartesianToLinearIndex = lam shape. lam idx.
  let acc =
    foldl
      (lam acc : ([Int], Int). lam i.
        match acc with (shape, ofs) in
        let ofs = addi ofs (muli (_prod shape) i) in
        match shape with [] then ([], ofs)
        else (tail shape, ofs))
      (tail shape, 0)
      idx
   in
   match acc with (_, i) in i

utest cartesianToLinearIndex [2] [0] with 0
utest cartesianToLinearIndex [2] [1] with 1
utest cartesianToLinearIndex [2, 3] [0, 2] with 2
utest cartesianToLinearIndex [2, 3] [1, 0] with 3


-- Folds `f` over the range `start` `stop` using accumulator `acc`
let indexFoldu : all a. (a -> Int -> a) -> a -> Int -> Int -> a =
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
let indexFoldRM : all a. (a -> [Int] -> a) -> a -> [Int] -> a =
lam f. lam acc. lam shape.
  let size = _prod shape in
  recursive let work = lam acc. lam k.
    if lti k size then
      let idx = linearToCartesianIndex shape k in
      work (f acc idx) (addi k 1)
    else acc
  in
  work acc 0

utest indexFoldRM (lam seq. lam idx. snoc seq idx) [] []
with [[]] using eqSeq (eqSeq eqi)

utest indexFoldRM (lam seq. lam idx. snoc seq idx) [] [2, 2]
with [[0, 0], [0, 1], [1, 0], [1, 1]] using eqSeq (eqSeq eqi)


-- Folds `f` over the indexes of `shape` in row-major order with accumulator
-- `acc`. If `f acc idx` is `None ()` then the result is `None ()`.
let optionIndexFoldRMM : all a. (a -> [Int] -> Option a) -> a -> [Int] -> Option a =
lam f. lam acc. lam shape.
  let size = _prod shape in
  recursive let work = lam acc. lam k.
    if lti k size then
      let idx = linearToCartesianIndex shape k in
      let res =  f acc idx in
      match res with Some acc then
        work acc (addi k 1)
      else match res with None _ then
        None ()
      else never
    else Some acc
  in
  work acc 0

utest optionIndexFoldRMM
  (lam seq. lam idx.
     if lti (length seq) 5 then Some (snoc seq idx) else None ())
  []
  []
with Some [[]] using optionEq (eqSeq (eqSeq eqi))

utest optionIndexFoldRMM
  (lam seq. lam idx.
     if lti (length seq) 5 then Some (snoc seq idx) else None ())
  []
  [2, 2]
with Some [[0, 0], [0, 1], [1, 0], [1, 1]] using optionEq (eqSeq (eqSeq eqi))

utest optionIndexFoldRMM
  (lam seq. lam idx.
     if lti (length seq) 3 then Some (snoc seq idx) else None ())
  []
  [2, 2]
with None () using optionEq (eqSeq (eqSeq eqi))


---------------------------
-- SHAPE AND RANK CHECKS --
---------------------------

let tensorHasRank : all a. Tensor[a] -> Int -> Bool =
  lam t. lam rank. eqi (tensorRank t) rank

utest
  let t = tensorCreateDense [2, 2] (lam. 0) in
  tensorHasRank t 2
with true

utest
  let t = tensorCreateDense [2, 2] (lam. 0) in
  tensorHasRank t 1
with false

let tensorHasShape : all a. Tensor[a] -> [Int] -> Bool =
  lam t. lam shape. eqSeq eqi (tensorShape t) shape

utest
  let t = tensorCreateDense [4, 1] (lam. 0) in
  tensorHasShape t [4, 1]
with true

utest
  let t = tensorCreateDense [4, 1] (lam. 0) in
  tensorHasShape t [4, 2]
with false


let tensorHasSameShape : all a. all b.  Tensor[a] -> Tensor[b] -> Bool =
lam t1. lam t2. eqSeq eqi (tensorShape t1) (tensorShape t2)

utest
  let t1 = tensorCreateDense [4, 1] (lam. 0) in
  let t2 = tensorCreateDense [4, 1] (lam. 0) in
  tensorHasSameShape t1 t2
with true

utest
  let t1 = tensorCreateDense [4, 1] (lam. 0) in
  let t2 = tensorCreateDense [4, 2] (lam. 0) in
  tensorHasSameShape t1 t2
with false

------------------------------
-- GENERAL TENSOR FUNCTIONS --
------------------------------

-- Default to dense tensors
let tensorCreate = tensorCreateDense

-- Construct a tensor of shape `shape` from a sequence `seq`.
let tensorOfSeqOrElse : all a.
  (() -> Tensor[a]) ->
  ([Int] -> ([Int] -> a) -> Tensor[a]) ->
  [Int] ->
  [a] ->
  Tensor[a] =
lam f. lam tcreate. lam shape. lam seq.
  let n = length seq in
  if neqi n (_prod shape) then f ()
  else
    let t = tcreate [n] (lam idx. get seq (get idx 0)) in
    tensorReshapeExn t shape

let tensorOfSeqExn
  : all a. ([Int] -> ([Int] -> a) -> Tensor[a]) -> [Int] -> [a] -> Tensor[a] =
  lam x.
  tensorOfSeqOrElse (lam. error "Empty seq in tensorOfSeqExn") x

-- Construct a sequence from a rank 1 tensor `t`.
let tensorToSeqOrElse : all a. (() -> [a]) -> Tensor[a] -> [a] =
lam f. lam t.
  if neqi (tensorRank t) 1 then f ()
  else
    let n = get (tensorShape t) 0 in
    unfoldr (lam i. if lti i n
               then Some (tensorGetExn t [i], addi i 1) else None ())
            0

let tensorToSeqExn : all a. Tensor[a] -> [a] = lam x.
  tensorToSeqOrElse (lam. error "Not rank 1 tensor in tensorToSeqExn") x

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
let tensorDenseRepeat : all a. [Int] -> a -> Tensor[a] =
lam shape. lam v.
  tensorCreateDense shape (lam. v)

utest
  let t = tensorDenseRepeat [4] 0 in
  tensorToSeqExn t
with [0, 0, 0, 0] using eqSeq eqi


-- The number of elements in a tensor `t`.
let tensorSize : all a. Tensor[a] -> Int =
lam t. _prod (tensorShape t)

utest tensorSize (tensorCreateDense [1, 2, 3] (lam. 0)) with 6
utest tensorSize (tensorCreateDense [] (lam. 0)) with 1
utest tensorSize (tensorCreateDense [0] (lam. 0)) with 0


-- Map the elements of `t1` to the elements of `t2` via the function `f`,
-- where `t1` and `t2` has to have the same shape.
let tensorMapOrElse
  : all a. all b. (() -> ()) -> (a -> b -> b) -> Tensor[a] -> Tensor[b] -> () =
lam f. lam g. lam t1. lam t2.
  if tensorHasSameShape t1 t2 then
    let n = tensorSize t1 in
    let v1 = tensorReshapeExn t1 [n] in
    let v2 =  tensorReshapeExn t2 [n] in
    tensorIterSlice
      (lam i. lam e.
        tensorSetExn v2 [i] (g (tensorGetExn e []) (tensorGetExn v2 [i])))
      v1
  else f ()

let tensorMapExn = lam x.
  tensorMapOrElse (lam. error "Tensor shape mismatch in tensorMap") x

utest
  let t1 = tensorCreateDense [0] (lam. []) in
  let t2 = tensorCreateDense [0] (lam. []) in
  tensorMapExn (lam x. lam. [x]) t1 t2;
  match tensorToSeqExn t2 with [] then true else false
with true

utest
  let t1 = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  let t2 = tensorCreateDense [4] (lam. []) in
  tensorMapExn (lam x. lam. [x]) t1 t2;
  tensorToSeqExn t2
with [[1], [2], [3], [4]]

utest
  let t = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  tensorMapExn addi t t;
  tensorToSeqExn t
with [2, 4, 6, 8]

utest
  let t1 = tensorOfSeqExn tensorCreateDense [4] [5, 6, 7, 8] in
  let t2 = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  tensorMapExn subi t1 t2;
  tensorToSeqExn t2
with [4, 4, 4, 4]

utest
  let t = tensorDenseRepeat [] 1 in
  tensorMapExn addi t t;
  tensorGetExn t []
with 2


-- Applies function `f` to the elements of `t`.
let tensorMapInplace : all a. (a -> a) -> Tensor[a] -> () =
  lam f. lam t. tensorMapExn (lam. f) t t

utest
  let t = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  tensorMapInplace (addi 1) t;
  tensorToSeqExn t
with [2, 3, 4, 5]


-- Applies function `f` to the elements of a copy of `t`.
let tensorMapCopy : all a. (a -> a) -> Tensor[a] -> Tensor[a] =
  lam f. lam t.
    let r = tensorCopy t in
    tensorMapExn (lam. f) t r; r

utest
  let t = tensorOfSeqExn tensorCreateDense [4] [1, 2, 3, 4] in
  tensorToSeqExn (tensorMapCopy (addi 1) t)
with [2, 3, 4, 5]


-- Map the index and elements of `t1` to the elements of `t2` via the function
-- `f`, where `t1` and `t2` has to have the same shape.
let tensorMapiOrElse
  : all a. all b. (() -> ()) -> ([Int] -> a -> b -> b) -> Tensor[a] -> Tensor[b] -> () =
lam f. lam g. lam t1. lam t2.
  let shape = tensorShape t1 in
  if tensorHasShape t2 shape then
    let n = tensorSize t1 in
    let v1 = tensorReshapeExn t1 [n] in
    let v2 =  tensorReshapeExn t2 [n] in
    tensorIterSlice
      (lam i. lam e.
        let idx = linearToCartesianIndex shape i in
        tensorSetExn
          v2
          [i]
          (g idx (tensorGetExn e []) (tensorGetExn v2 [i])))
      v1
  else f ()

let tensorMapiExn = lam x.
  tensorMapiOrElse (lam. error "Tensor shape mismatch in tensorMap") x

utest
  let t1 = tensorOfSeqExn tensorCreateDense [2, 2]
    [1, 2
    ,3, 4]
  in
  let t2 = tensorCreateDense [2, 2] (lam. ([], [])) in
  tensorMapiExn (lam idx. lam x1. lam x2 : ([Int], [Int]). (idx, cons x1 x2.0)) t1 t2;
  tensorToSeqExn (tensorReshapeExn t2 [tensorSize t2])
with [([0, 0], [1]), ([0, 1], [2]), ([1, 0], [3]), ([1, 1], [4])]

let tensorMapiInplace : all a. ([Int] -> a -> a) -> Tensor[a] -> () =
  lam f. lam t. tensorMapiExn (lam idx. lam x. lam. f idx x) t t

let tensorMapiCopy : all a. ([Int] -> a -> a) -> Tensor[a] -> Tensor[a] =
  lam f. lam t.
    let r = tensorCopy t in
    tensorMapiExn (lam idx. lam x. lam. f idx x) t r; r


-- Copies the content of `t1` to `t2`. Gives an error if `t1` and `t2` does no
-- have the same shape.
let tensorBlitExn : all a. Tensor[a] -> Tensor[a] -> () =
lam t1. lam t2.
  if tensorHasSameShape t1 t2 then tensorMapExn (lam x. lam. x) t1 t2
  else error "Invalid Argument: tensor.tensorBlitExn"

let test =
  let t1 = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  let t2 = tensorCreateDense [3] (lam. 0) in
  utest
    tensorBlitExn t1 t2;
    t2
  with t1 using tensorEq eqi in
  ()


-- Left folds `f acc idx t` over the zero'th dimension of `t1`, where `acc` is
-- the accumulator, `idx` is the index of the slice, and `t` is the i'th slice
-- of `t1`.
let tensorFoldliSlice
  : all a. all b. (b -> Int -> Tensor[a] -> b) -> b -> Tensor[a] -> b =
  lam f. lam acc. lam t1.
  let s = head (tensorShape t1) in
  recursive let rec = lam acc. lam i.
    if eqi i s then acc else
      let acc = f acc i (tensorSliceExn t1 [i]) in
      rec acc (addi i 1)
  in rec acc 0

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorFoldliSlice
    (lam acc. lam i. lam t. addi (addi acc (tensorGetExn t [])) i) 0 t
with 9


-- Left folds `f acc t` over the zero'th dimension of `t1`, where `acc` is the
-- accumulator and `t` is the i'th slice of `t1`.
let tensorFoldlSlice : all a. all b. (b -> Tensor[a] -> b) -> b -> Tensor[a] -> b =
  lam f. tensorFoldliSlice (lam acc. lam. f acc)

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorFoldlSlice
    (lam acc. lam t. addi acc (tensorGetExn t [])) 0 t
with 6


-- Folds `f acc el` over all elements `el` of `t` in row-major order, where
-- `acc` is the accumulator.
let tensorFold : all a. all b. (b -> a -> b) -> b -> Tensor[a] -> b =
  lam f. lam acc. lam t.
  let t = tensorReshapeExn t [tensorSize t] in
  tensorFoldlSlice (lam acc. lam t. f acc (tensorGetExn t [])) acc t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorFold addi 0 t
with 6


-- Folds `f idx acc el` over all elements `el` of `t` in row-major order, where
-- `acc` is the accumulator and `idx` is the index of the element.
let tensorFoldi : all a. all b. (b -> [Int] -> a -> b) -> b -> Tensor[a] -> b =
  lam f. lam acc. lam t.
  let shape = tensorShape t in
  let t = tensorReshapeExn t [tensorSize t] in
  tensorFoldliSlice
    (lam acc. lam i. lam t.
      f acc (linearToCartesianIndex shape i) (tensorGetExn t []))
    acc t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorFoldi
    (lam acc : ([[Int]], Int). lam idx. lam x.
      (snoc acc.0 idx, addi acc.1 x))
    ([], 0) t
with ([[0], [1], [2]], 6)

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 2]
    [1, 2
    ,3, 4]
  in
  tensorFoldi (lam acc. lam idx. lam x. snoc acc (idx, x)) [] t
with [([0, 0], 1), ([0, 1], 2), ([1, 0], 3), ([1, 1], 4)]


-- Iterates through the elements of `t` in row-major order, applying the
-- function `f` on each index and element.
let tensorIteri : all a. ([Int] -> a -> ()) -> Tensor[a] -> () =
  lam f. lam t.
  let shape = tensorShape t in
  let t = tensorReshapeExn t [tensorSize t] in
  tensorIterSlice
    (lam i. lam t. f (linearToCartesianIndex shape i) (tensorGetExn t [])) t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorIteri (lam i. lam x. tensorSetExn t i (addi x x)) t;
  tensorToSeqExn t
with [2, 4, 6]


-- Iterates through the elements of `t` in row-major order, applying the
-- function `f` on each element.
let tensorIter : all a. (a -> ()) -> Tensor[a] -> () =
  lam f. tensorIteri (lam. lam x. f x)


-- The maximum element in `t` as defined by `cmp`.
let tensorMax : all a. (a -> a -> Int) -> Tensor[a] -> Option a =
  lam cmp. lam t.
    if eqi (tensorRank t) 0 then Some (tensorGetExn t [])
    else if eqi (tensorSize t) 0 then None ()
    else
      let t = tensorReshapeExn t [tensorSize t] in
      let max =
        tensorFoldlSlice
          (lam max. lam t.
            let x = tensorGetExn t [] in
            if gti (cmp x max) 0 then x else max)
          (tensorGetExn t [0])
          t
      in
      Some max


utest
  let t = tensorOfSeqExn tensorCreateDense [] [1] in
  tensorMax subi t
with Some 1

utest
  let t = tensorOfSeqExn tensorCreateDense [0] [] in
  tensorMax subi t
with None ()

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorMax subi t
with Some 3

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorMax subi t
with Some 6


-- The minimum element in `t` as defined by `cmp`.
let tensorMin : all a. (a -> a -> Int) -> Tensor[a] -> Option a =
  lam cmp. lam t. tensorMax (lam x. lam y. cmp y x) t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorMin subi t
with Some 1

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorMin subi t
with Some 1


-- Finds element and index `Some (el, i)` in `t` satisfying predicate `p`. If
-- no such element is found then `None` is returned.
let tensorFindi : all a. (a -> Bool) -> Tensor[a] -> Option (a, [Int]) =
  lam p. lam t.
    let n = tensorSize t in
    let shape = tensorShape t in
    let t = tensorReshapeExn t [n] in
    recursive let work = lam i.
      if lti i n then
        let e = tensorGetExn t [i] in
        if p e then Some (e, linearToCartesianIndex shape i)
        else work (addi i 1)
      else None ()
    in
    work 0

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  match tensorFindi (eqi 1) t with Some x then x else (negi 1, [])
with (1, [0])

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  match tensorFindi (eqi 3) t with Some x then x else (negi 1, [])
with (3, [0, 2])


-- Finds element `Some el` in `t` satisfying predicate `p`. If
-- no such element is found then `None` is returned.
let tensorFind : all a. (a -> Bool) -> Tensor[a] -> Option a =
  lam p. lam t.
    let x = tensorFindi p t in
    -- NOTE(vsenderov, 2024-03-21) Workaround for a failing test in TreePPL
    -- see https://github.com/treeppl/treeppl/pull/67, https://github.com/treeppl/treeppl/issues/69
    match x with Some (y, _) then Some y
    else match x with None _ then None ()
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  match tensorFind (eqi 1) t with Some x then x else negi 1
with 1

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  match tensorFind (eqi 3) t with Some x then x else negi 1
with 3


-- Finds index `Some i` in `t` of element satisfying predicate `p`. If no such
-- element is found then `None` is returned.
let tensorIndex : all a. (a -> Bool) -> Tensor[a] -> Option [Int] =
  lam p. lam t.
    let x = tensorFindi p t in
    match x with Some (_, idx) then Some idx
    else match x with None _ then None ()
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  match tensorIndex (eqi 1) t with Some x then x
  else []
with [0]

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  match tensorIndex (eqi 3) t with Some x then x
  else []
with [0, 2]


-- `true` if `p x` for some `x` in `t`, else `false`.
let tensorAny : all a. (a -> Bool) -> Tensor[a] -> Bool =
  lam p. lam t.
    let x = tensorFindi p t in
    match x with Some _ then true
    else match x with None _ then false
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorAny (eqi 3) t
with true

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorAny (eqi 7) t
with false


-- `true` if `p x` for all `x` in `t`, else `false`.
let tensorAll : all a. (a -> Bool) -> Tensor[a] -> Bool =
  lam p. lam t.
    let x = tensorFindi (lam x. not (p x)) t in
    match x with Some _ then false
    else match x with None _ then true
    else never

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorAll (gti 7) t
with true

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorAll (gti 6) t
with false


-- All dimensions of tensor `t` are of the same size.
let tensorDimsEqual = lam t.
  let shape = tensorShape t in
  if null shape then true
  else forAll (eqi (head shape)) (tail shape)

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 2]
    [1, 2
    ,3, 4]
  in
  tensorDimsEqual t
with true

utest
  let t = tensorOfSeqExn tensorCreateDense [1, 4] [1, 2, 3, 4] in
  tensorDimsEqual t
with false


-- Filter elements of `t` given predicate `p`.
let tensorFilter : all a. (a -> Bool) -> Tensor[a] -> [a] =
  lam p. lam t.
    let t = tensorReshapeExn t [tensorSize t] in
    tensorFold
      (lam a. lam x. if p x then snoc a x else a)
      [] t

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorFilter (lti 3) t
with [4, 5, 6]


-- Filter index of elements of `t` given predicate `p`.
let tensorFilteri : all a. ([Int] -> a -> Bool) -> Tensor[a] -> [[Int]] =
  lam p. lam t.
    tensorFoldi
      (lam a. lam idx. lam x. if p idx x then snoc a idx else a)
      [] t

utest
  let t = tensorOfSeqExn tensorCreateDense [2, 3]
    [1, 2, 3
    ,4, 5, 6]
  in
  tensorFilteri (lam. lti 3) t
with [[1, 0], [1, 1], [1, 2]]

-- Given a tensor and sequence of index sequences, produce the corresponding
-- sub-tensor (that has the same rank). More general but not as efficient as
-- tensorSubExn (for Bigarrays) as it has to allocate a new tensor. See the
-- tests for example usages.
let tensorSubSeqExn : all a. TCreate a -> Tensor[a] -> [[Int]] -> Tensor[a] =
  lam tcreate. lam t. lam sub.
    let newShape = map length sub in
    tcreate newShape (lam is: [Int].
      let isPrev = mapi (lam i. lam x. get (get sub i) x) is in
      tensorGetExn t isPrev
    )

utest
  let t = tensorOfSeqExn tensorCreateDense [3, 3]
    [1, 2, 3
    ,4, 5, 6
    ,7, 8, 9]
  in
  tensorSubSeqExn tensorCreate t [[0,2],[1]]
with
  tensorOfSeqExn tensorCreateDense [2, 1]
    [2,
     8]
using tensorEq eqi
utest
  let t = tensorOfSeqExn tensorCreateDense [3, 3]
    [1, 2, 3
    ,4, 5, 6
    ,7, 8, 9]
  in
  tensorSubSeqExn tensorCreateDense t [[0],[0,2,1]]
with
  tensorOfSeqExn tensorCreateDense [1, 3]
    [1, 3, 2]
using tensorEq eqi


------------------------------
-- INTEGER TENSOR FUNCTIONS --
------------------------------

let tensorCumsumiExn : Tensor[Int] -> Tensor[Int] -> () =
  lam t. lam r.
    if tensorHasSameShape t r then
      tensorFoldi
        (lam acc. lam idx. lam x.
          let acc = addi acc x in
          tensorSetExn r idx acc; acc)
        0 t; ()
    else error "Invalid Argument: tensor.tensorCumsumiExn"

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  let r = tensorCreateDense [3] (lam. 0) in
  tensorCumsumiExn t r; tensorToSeqExn r
with [1, 3, 6]

let tensorCumsumiInplace : Tensor[Int] -> () =
  lam t. tensorCumsumiExn t t

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorCumsumiInplace t; tensorToSeqExn t
with [1, 3, 6]

let tensorCumsumiCopy : Tensor[Int] -> Tensor[Int] =
  lam t.
    let r = tensorCopy t in
    tensorCumsumiExn t r; r

utest
  let t = tensorOfSeqExn tensorCreateDense [3] [1, 2, 3] in
  tensorToSeqExn (tensorCumsumiCopy t)
with [1, 3, 6]


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
tensorMapInplace (lam. 0) r2;
utest tensorToSeqExn t1 with [2, 2, 3, 0, 0, 0, 7, 8, 9] in
-- where we use `tensorMapInplace` from `tensor.mc`

-- We can get a subset of the rows of t2 by restricting its 0th dimension.
let s1 = tensorSubExn t2 1 2 in
utest tensorShape s1 with [2, 3] in
utest tensorToSeqExn (tensorReshapeExn s1 [6]) with [0, 0, 0, 7, 8, 9] in

-- As before, none of these operations (except copy) does any copying
-- and the data is shared.
-- utest tensorToSeqExn t1 with [0, 0, 0, 7, 8, 9, 7, 8, 9] in

()
