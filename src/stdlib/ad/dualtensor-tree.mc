include "common.mc"
include "tensor.mc"
include "dual-tree.mc"
include "dualnum-tree.mc"

type DualTensor
-- Tensor with a 1. at exactly one index and 0. at all other indices.
con UnitTensor : {shape : [Int], lidx : Int} -> DualTensor
-- A primal tensor
con PrimalTensor : Tensor[Float] -> DualTensor
--- A dual tensor t + et', where t is the primal and t' the perturbation.
con DualTensor : {e : Eps, x : DualTensor, xp : DualTensor} -> DualTensor

----------------------------------------
-- LIFTING OF TENSOR SHAPE OPERATORS  --
----------------------------------------

let dualtensorShape : DualTensor -> [Int] =
recursive let recur = lam t.
  switch t
  case UnitTensor t then t.shape
  case PrimalTensor t then tensorShape t
  case DualTensor {x = t} then recur t
  end
in recur

let dualtensorRank : DualTensor -> Int =
recursive let recur = lam t.
  switch t
  case UnitTensor t then length t.shape
  case PrimalTensor t then tensorRank t
  case DualTensor {x = t} then recur t
  end
in recur

let _prod = foldl muli 1
let _eqShape = eqSeq eqi

let _idxInShape =
lam idx. lam shape.
  and
    (eqi (length idx) (length shape))
    (forAll (lti 0) (zipWith subi shape idx))

let dualtensorSize : DualTensor -> Int =
recursive let recur = lam t.
  switch t
  case UnitTensor t then _prod t.shape
  case PrimalTensor t then tensorSize t
  case DualTensor {x = t} then recur t
  end
in recur

-----------------------------------
-- DUAL NUMBERS API FOR TENSORS  --
-----------------------------------

let dualtensorIsDualNum : DualTensor -> Bool =
lam t.
  switch t
  case UnitTensor _ | PrimalTensor _ then false
  case DualTensor _ then true
  end

let dualtensorEpsilon : DualTensor -> Eps =
lam t.
  match t with DualTensor {e = e} then e
  else error "Operand not a dual tensor"

let dualtensorCreateUnit : [Int] -> [Int] -> DualTensor =
lam shape. lam idx.
  UnitTensor { shape = shape, lidx = cartesianToLinearIndex shape idx }

let dualtensorCreateDual : Eps -> DualTensor -> DualTensor -> DualTensor =
lam e. lam x. lam xp.
  if _eqShape (dualtensorShape x) (dualtensorShape xp) then
    DualTensor { e = e, x = x, xp = xp }
  else error "dualtensorCreateDual: Invalid Argument"

let dualtensorPrimal : Eps -> DualTensor -> DualTensor =
lam e. lam t.
  switch t
  case UnitTensor _ | PrimalTensor _ then t
  case DualTensor t then if dualLtE t.e e then DualTensor t else t.x
  end

let dualtensorPrimalDeep : DualTensor -> Tensor[Float] =
recursive let recur = lam t.
  switch t
  case UnitTensor _ then
    error "dualtensorPrimalDeep: Invalid Argument"
  case PrimalTensor t then t
  case DualTensor {x = x} then recur x
  end
in recur

let dualtensorPertubation : Eps -> DualTensor -> DualTensor =
lam e. lam t.
  switch t
  case UnitTensor _ then
    error "dualtensorPertubation: Invalid Argument"
  case PrimalTensor t then PrimalTensor (tensorMapCopy (lam. 0.) t)
  case DualTensor t then
  	if dualLtE t.e e then DualTensor t else t.xp
  end

let dualtensorGenEpsilon : () -> Eps = dualGenEpsilon

let dualtensorEq
  : (Float -> Float -> Bool) -> DualTensor -> DualTensor -> Bool =
lam eq. lam t1. lam t2.
  if _eqShape (dualtensorShape t1) (dualtensorShape t2) then
    recursive let recur = lam t1. lam t2.
      switch (t1, t2)
      case
        (UnitTensor {lidx = i1, shape = shape1},
         UnitTensor {lidx = i2, shape = shape2})
      then
        eqSeq eqi
          (linearToCartesianIndex shape1 i1)
          (linearToCartesianIndex shape2 i2)
      case
        (UnitTensor {shape = shape, lidx = i}, PrimalTensor t)
        | (PrimalTensor t, UnitTensor {shape = shape, lidx = i})
      then
        eq 1. (tensorGetExn t (linearToCartesianIndex shape i))
      case (PrimalTensor t1, PrimalTensor t2) then
        tensorEq eq t1 t2
      case
        (DualTensor {e = e1, x = x1, xp = xp1},
         DualTensor {e = e2, x = x2, xp = xp2})
      then
        if dualEqE e1 e2 then
          if recur x1 x2 then recur xp1 xp2 else false
        else false
      case (_, _) then false
      end
    in recur t1 t2
  else false

let dualtensorToString : DualTensor -> String =
lam t.
  let wrapInParen = lam t. lam str.
    if dualtensorIsDualNum t then join ["(", str, ")"] else str
  in
  let shape2str = lam shape.
    strJoin ", " (map int2string shape)
  in
  recursive let recur = lam t.
    switch t
    case UnitTensor {shape = shape, lidx = lidx} then
      let idx = linearToCartesianIndex shape lidx in
      let t = tensorCreateDense shape (lam. 0.) in
      (if _idxInShape idx shape then tensorSetExn t idx 1. else ());
      tensor2string float2string t
    case PrimalTensor t then tensor2string float2string t
    case DualTensor {e = e, x = x, xp = xp} then
      join [
        wrapInParen x (recur x),
        " + e",
        int2string e,
        " ",
        wrapInParen xp (recur xp)
      ]
    end
  in recur t

----------------------------------
-- LIFTING OF TENSOR OPERATORS  --
----------------------------------

let dualtensorGetExn : DualTensor -> [Int] -> DualNum =
lam t. lam idx.
  recursive let recur = lam t.
    switch t
    case UnitTensor t then
      if eqi (cartesianToLinearIndex t.shape idx) t.lidx then Primal 1.
      else Primal 0.
    case PrimalTensor t then Primal (tensorGetExn t idx)
    case DualTensor {e = e, x = x, xp = xp} then
      dualnumCreateDual e (recur x) (recur xp)
    end
  in recur t

let dualtensorSetExn : DualTensor -> [Int] -> DualNum -> () =
lam t. lam idx. lam v.
  recursive let recur = lam t. lam v.
    switch (t, v)
    case (UnitTensor _, _) then error "dualtensorSetExn: Invalid Argument"
    case (PrimalTensor t, Primal x2) then tensorSetExn t idx x2
    case (DualTensor {e = e1, x = x1, xp = xp1}, Primal _) then
      recur x1 v;
      recur xp1 (Primal 0.)
    -- case (PrimalTensor _, Dual {e = e2, x = x2, xp = Primal xp2}) then
    --   if eqf xp2 0. then recur t x2
    --   else error "dualtensorSetExn: Invalid Argument"
    case (PrimalTensor _, Dual {x = x2}) then recur t x2
    -- case (PrimalTensor _, Dual _) then
    --   error "dualtensorSetExn: Invalid Argument"
    case
      (DualTensor {e = e1, x = x1, xp = xp1}, Dual {e = e2, x = x2, xp = xp2})
    then
      if dualLtE e2 e1 then --error "dualtensorSetExn: Invalid Argument"
        recur x1 v
      else recur x1 x2; recur xp1 xp2
    end
  in recur t v

let dualtensorSliceExn : DualTensor -> [Int] -> DualTensor =
lam t. lam idx.
  let nidx = length idx in
  let rank = dualtensorRank t in
  let shape = dualtensorShape t in
  if
    and
      (leqi nidx rank)
      (and
        (forAll (leqi 0) idx)
        (forAll (lti 0) (zipWith subi shape idx)))
  then
    recursive let recur = lam t.
      switch t
      case UnitTensor t then
        UnitTensor { t with shape = subsequence shape nidx (subi rank nidx) }
      case PrimalTensor t then PrimalTensor (tensorSliceExn t idx)
      case DualTensor t then
        DualTensor {{ t with x = recur t.x } with xp = recur t.xp }
      end
    in recur t
  else error "dualtensorSliceExn: Invalid Argument"

let dualtensorReshapeExn : DualTensor -> [Int] -> DualTensor =
lam t. lam shape.
  if eqi (_prod shape) (dualtensorSize t) then
    recursive let recur = lam t.
      switch t
      case UnitTensor t then UnitTensor { t with shape = shape }
      case PrimalTensor t then PrimalTensor (tensorSliceExn t shape)
      case DualTensor t then
        DualTensor {{ t with x = recur t.x } with xp = recur t.xp }
      end
    in recur t
  else error "dualtensorReshapeExn: Invalid Argument"

let dualtensorSubExn : DualTensor -> Int -> Int -> DualTensor =
lam t. lam ofs. lam len.
  let shape = dualtensorShape t in
  if and
      -- rank > 1
      (gti (length shape) 0)
      (and
        -- ofs >= 0
        (geqi ofs 0)
          (and
            -- len >= 0
            (geqi len 0)
            -- ofs + len <= shape[0]
            (leqi (addi ofs len) (head shape))))
  then
    recursive let recur = lam t.
      switch t
      case UnitTensor t then
        UnitTensor
          {{ t with shape = set t.shape 0 len }
               with lidx = subi t.lidx ofs }
      case PrimalTensor t then PrimalTensor (tensorSubExn t ofs len)
      case DualTensor t then
        DualTensor {{ t with x = recur t.x } with xp = recur t.xp }
      end
    in recur t
  else error "dualtensorSubExn: Invalid Argument"

let dualtensorIterSlice : (Int -> DualTensor -> ()) -> DualTensor -> () =
lam f. lam t.
  if eqi (dualtensorRank t) 0 then f 0 t
  else
    let n = head (dualtensorShape t) in
    recursive let recur = lam i.
      if eqi i n then ()
      else f i (dualtensorSliceExn t [i]); recur (succ i)
    in recur 0

--------------------------------------------------------------------
-- DERIVATIVE OPERATORS OVER RANK 1 DUAL TENSORS VALUED FUNCTIONS --
--------------------------------------------------------------------

type DualVec = DualTensor

-- `dualtensorJacvecprod f x y r rp` computes the Jacobian-vector product of `f`
-- at `x` with `y`, storing f(x) in `r` and 𝛁f(x)y in `rp`.
let dualtensorJacfvecprod
  : (DualVec -> DualTensor -> ())
  -> DualVec
  -> DualVec
  -> DualTensor
  -> DualTensor
  -> () =
lam f. lam x. lam y. lam r. lam rp.
  let e = dualGenEpsilon () in
  let t1 = dualtensorCreateDual e x y in
  let t2 = dualtensorCreateDual e r rp in
  f t1 t2

-- `dualtensorJacfj f x j r rp` computes the j'th row in the Jacobian of `f` at
-- `x`, storing f(x) in `r` and 𝛁f(x)_j in `rp`.
let dualtensorJacfj
  : (DualVec -> DualTensor -> ())
  -> DualVec
  -> Int
  -> DualTensor
  -> DualTensor
  -> () =
lam f. lam x. lam j.
  dualtensorJacfvecprod f x (dualtensorCreateUnit (dualtensorShape x) [j])

-- `dualtensorJacvecprod f x y rp` computes the Jacobian-vector product of `f`
-- at `x` with `y`, storing 𝛁f(x)y in `rp`.
let dualtensorJacvecprod
  : (DualVec -> DualVec -> ()) -> DualVec -> DualVec -> DualTensor -> () =
lam f. lam x. lam y. lam rp.
  let r = tensorCreateDense (dualtensorShape rp) (lam. 0.) in
  dualtensorJacfvecprod f x y (PrimalTensor r) rp

-- `dualtensorJacj f x j rp` computes the j'th row in the Jacobian of `f` at
-- `x`, storing 𝛁f(x)_j in `rp`.
let dualtensorJacj
  : (DualVec -> DualTensor -> ())
  -> DualVec
  -> Int
  -> DualTensor
  -> () =
lam f. lam x. lam j.
  dualtensorJacvecprod f x (dualtensorCreateUnit (dualtensorShape x) [j])

-- Computes 𝛁f(x)^T and stores the result in `t`.
let dualtensorJacT
  : (DualVec -> DualTensor -> ()) ->  DualVec -> DualTensor -> () =
lam f. lam x. lam t.
  dualtensorIterSlice (lam j. lam r. dualtensorJacj f x j r) t

-- `dualtensorGradfvecprod f x y` computes the Gradient-vector product of `f` at
-- `x` with `y` returning the tuple (f(x), 𝛁f(x)y).
let dualtensorGradfvecprod
  : (DualVec -> DualNum) -> DualVec -> DualVec -> (DualNum, DualNum) =
lam f. lam x. lam y.
  let e = dualGenEpsilon () in
  let t1 = dualtensorCreateDual e x y in
  let r = f t1 in
  (dualnumPrimal e r, dualnumPertubation e r)

-- `dualtensorGradfj f x j` computes the j'th element in the gradient of `f` at
-- `x`, returning the tuple (f(x), 𝛁f(x)_j).
let dualtensorGradfj
  : (DualVec -> DualNum) -> DualVec -> Int -> (DualNum, DualNum) =
lam f. lam x. lam j.
  dualtensorGradfvecprod f x (dualtensorCreateUnit (dualtensorShape x) [j])

-- `dualtensorGradvecprod f x y` computes the Gradient-vector product of `f` at
-- `x` with `y` returning 𝛁f(x)y.
let dualtensorGradvecprod
  : (DualVec -> DualNum) -> DualVec -> DualVec -> DualNum =
lam f. lam x. lam y.
  let e = dualGenEpsilon () in
  let t1 = dualtensorCreateDual e x y in
  dualnumPertubation e (f t1)

-- `dualtensorGradj f x j` computes the j'th element in the gradient of `f` at
-- `x`, returning 𝛁f(x)_j.
let dualtensorGradj
  : (DualVec -> DualNum)-> DualVec -> Int -> DualNum =
lam f. lam x. lam j.
  dualtensorGradvecprod f x (dualtensorCreateUnit (dualtensorShape x) [j])

-- `dualtensorGrad f x r` computes the gradient 𝛁f(x) and stores the result in
-- `r`.
let dualtensorGrad : (DualVec -> DualNum) -> DualVec -> DualVec -> () =
lam f. lam x. lam r.
  dualtensorIterSlice
    (lam j. lam. dualtensorSetExn r [j] (dualtensorGradj f x j))
    x

-- `dualtensorHessij f x i j` computes the (i, j)'th component of the Hessian,
-- returning 𝛁^2f(x)_ij.
let dualtensorHessij
  : (DualVec -> DualNum) -> DualVec -> Int -> Int -> DualNum =
lam f. lam x. lam i. lam j. dualtensorGradj (lam x. dualtensorGradj f x i) x j

-- `dualtensorHessijs f x i j t` computes the (i, j)'th component of the
-- Hessian, 𝛁^2f(x)_ij, storing the result in `t`.
let dualtensorHessijs
  : (DualVec -> DualTensor -> ()) -> DualVec -> Int -> Int -> DualTensor -> () =
lam f. lam x. lam i. lam j. lam t.
  dualtensorJacj (lam x. dualtensorJacj f x i) x j t

mexpr

let _dnum = dualnumCreateDual in
let _deq = dualnumEq eqf in
let _primalDeep = dualnumPrimalDeep in
let _t = lam t. PrimalTensor t in
let _td = dualtensorCreateDual in
let _Eq = tensorEq eqf in
let _dEq = dualtensorEq eqf in

let t1 =
  _t (tensorOfSeqExn tensorCreateDense [2] [1., 2.])
in
let t2 =
  _t (tensorOfSeqExn tensorCreateDense [2] [3., 4.])
in
let t3 =
  _t (tensorOfSeqExn tensorCreateDense [2] [0., 0.])
in

----------------------
-- Test get and set --
----------------------

utest dualtensorGetExn t1 [0] with Primal 1. using _deq in
utest dualtensorGetExn t1 [1] with Primal 2. using _deq in

let e1 = dualGenEpsilon () in
let t5 = _td e1 t1 t2 in

utest dualtensorGetExn t5 [0] with _dnum e1 (Primal 1.) (Primal 3.)
using _deq in
utest dualtensorGetExn t5 [1] with _dnum e1 (Primal 2.) (Primal 4.)
using _deq in

dualtensorSetExn t1 [0] (Primal 2.);
utest dualtensorGetExn t1 [0] with Primal 2. using _deq in

dualtensorSetExn t5 [0] (_dnum e1 (Primal 3.) (Primal 2.));
utest dualtensorGetExn t5 [0] with _dnum e1 (Primal 3.) (Primal 2.)
using _deq in

let e2 = dualGenEpsilon () in
dualtensorSetExn t5 [0] (_dnum e2 (Primal 3.) (Primal 2.));
utest dualtensorGetExn t5 [0] with _dnum e1 (Primal 3.) (Primal 2.)
using _deq in

----------------
-- Test slice --
----------------

let t1 =
  _t (tensorOfSeqExn tensorCreateDense [2] [1., 2.])
in
let t2 =
  _t (tensorOfSeqExn tensorCreateDense [2, 2] [1., 2., 3., 4.])
in

utest dualtensorGetExn (dualtensorSliceExn t1 [0]) [] with Primal 1.
using _deq in
utest dualtensorGetExn (dualtensorSliceExn t1 [1]) [] with Primal 2.
using _deq in
utest dualtensorSliceExn t2 [0] with t1 using _dEq in

--------------
-- Test sub --
--------------

let t1 =
  _t (tensorOfSeqExn tensorCreateDense [2] [1., 2.])
in
let t2 =
  _t (tensorOfSeqExn tensorCreateDense [4] [1., 2., 3., 4.])
in
utest dualtensorSubExn t2 0 2 with t1 using _dEq in

let t1 = dualtensorCreateUnit [4] [2] in
utest dualtensorShape (dualtensorSubExn t1 2 2) with [2] in
utest dualtensorGetExn (dualtensorSubExn t1 2 2) [0] with Primal 1. in

--------------------
-- Test iterSlice --
--------------------

let t1 =
  _t (tensorOfSeqExn tensorCreateDense [2, 2] [0., 0., 0., 0.])
in

let t2 =
  _t (tensorOfSeqExn tensorCreateDense [2, 2] [1., 1., 2., 2.])
in

dualtensorIterSlice
  (lam i. lam t.
    dualtensorSetExn t [0] (Primal (int2float (succ i)));
    dualtensorSetExn t [1] (Primal (int2float (succ i))))
  t1;

utest t1 with t2 using _dEq in

----------------------
-- Test derivatives --
----------------------

let f1 = lam x.
  let x1 = dualtensorGetExn x [0] in
  let x2 = dualtensorGetExn x [1] in
  addn (muln x1 x1) (muln x2 x2)
in

let f2 = lam x.
  let x1 = dualtensorGetExn x [0] in
  let x2 = dualtensorGetExn x [1] in
  muln x1 x2
in

let f3 = lam x.
  let x1 = dualtensorGetExn x [0] in
  x1
in

let f = lam x. lam r.
  dualtensorSetExn r [0] (f1 x);
  dualtensorSetExn r [1] (f2 x);
  dualtensorSetExn r [2] (f3 x);
  ()
in

-- Analytical solution to f(x).
let primal_f = lam x. lam r.
  let x1 = tensorGetExn x [0] in
  let x2 = tensorGetExn x [1] in
  tensorSetExn r [0] (addf (mulf x1 x1) (mulf x2 x2));
  tensorSetExn r [1] (mulf x1 x2);
  tensorSetExn r [2] x1;
  ()
in

-- Analytical solution to 𝛁^2f(x)y.
let pertubation_f = lam x. lam y. lam r.
  let x1 = tensorGetExn x [0] in
  let x2 = tensorGetExn x [1] in
  let y1 = tensorGetExn y [0] in
  let y2 = tensorGetExn y [1] in
  tensorSetExn r [0] (mulf 2. (addf (mulf y1 x1) (mulf y2 x2)));
  tensorSetExn r [1] (addf (mulf x2 y1) (mulf x1 y2));
  tensorSetExn r [2] y1;
  ()
in

let r1 = tensorCreateDense [3] (lam. 0.) in
let rp1 = tensorCopy r1 in
let r2 = tensorCopy r1 in
let rp2 = tensorCopy r1 in
let rp3 = tensorCopy r1 in

let x = tensorOfSeqExn tensorCreateDense [2] [2., 3.] in
let y = tensorOfSeqExn tensorCreateDense [2] [4., 5.] in

-------------------------------
-- Test Jacobian calculation --
-------------------------------

dualtensorJacfvecprod f (_t x) (_t y) (_t r1) (_t rp1);
dualtensorJacvecprod f (_t x) (_t y) (_t rp3);
primal_f x r2;
pertubation_f x y rp2;

utest r1 with r2 using _Eq in
utest rp1 with rp2 using _Eq in
utest rp3 with rp2 using _Eq in

-- Test Gradient calculation.
(
  match dualtensorGradfvecprod f1 (_t x) (_t y) with (x, xp) in
  utest _primalDeep x with tensorGetExn r2 [0] using eqf in
  utest _primalDeep xp with tensorGetExn rp2 [0] using eqf in
  ()
);

(
  match dualtensorGradfvecprod f2 (_t x) (_t y) with (x, xp) in
  utest _primalDeep x with tensorGetExn r2 [1] using eqf in
  utest _primalDeep xp with tensorGetExn rp2 [1] using eqf in
  ()
);

(
  match dualtensorGradfvecprod f3 (_t x) (_t y) with (x, xp) in
  utest _primalDeep x with tensorGetExn r2 [2] using eqf in
  utest _primalDeep xp with tensorGetExn rp2 [2] using eqf in
  ()
);

utest dualtensorGradvecprod f1 (_t x) (_t y)
with Primal (tensorGetExn rp2 [0]) using _deq in
utest dualtensorGradvecprod f2 (_t x) (_t y)
with Primal (tensorGetExn rp2 [1]) using _deq in
utest dualtensorGradvecprod f3 (_t x) (_t y)
with Primal (tensorGetExn rp2 [2]) using _deq in

let f = lam x. lam r.
  let x1 = dualtensorGetExn x [0] in
  let x2 = dualtensorGetExn x [1] in
  let r1 =
    addn (muln (muln x1 x1) x2) (muln (Primal 2.) (muln x1 (muln x2 x2)))
  in
  let r2 = muln x1 x2 in
  let r3 = muln x1 x1 in
  dualtensorSetExn r [0] r1;
  dualtensorSetExn r [1] r2;
  dualtensorSetExn r [2] r3;
  ()
in


let jacT_f = lam x. lam m.
  let x1 = tensorGetExn x [0] in
  let x2 = tensorGetExn x [1] in
  let m11 = addf (mulf 2. (mulf x1 x2)) (mulf 2. (mulf x2 x2)) in
  let m12 = addf (mulf x1 x1) (mulf 4. (mulf x1 x2)) in
  let m21 = x2 in
  let m22 = x1 in
  let m31 = mulf 2. x1 in
  let m32 = 0. in
  tensorSetExn m [0, 0] m11;
  tensorSetExn m [1, 0] m12;
  tensorSetExn m [0, 1] m21;
  tensorSetExn m [1, 1] m22;
  tensorSetExn m [0, 2] m31;
  tensorSetExn m [1, 2] m32;
  ()
in

let m1 = tensorCreateDense [2, 3] (lam. 0.) in
let m2 = tensorCopy m1 in

dualtensorJacT f (_t x) (_t m1);
jacT_f x m2;

utest m1 with m2 using _Eq in

------------------------------
-- Test Hessian calculation --
------------------------------

let r1 = tensorCreateDense [2] (lam. 0.) in
let rp1 = tensorCopy r1 in
let r2 = tensorCopy r1 in
let rp2 = tensorCopy r1 in

let f = lam x.
  let x1 = dualtensorGetExn x [0] in
  let x2 = dualtensorGetExn x [1] in
  addn (muln (muln x1 x1) x2) (muln (Primal 2.) (muln x1 (muln x2 x2)))
in

-- Computes the Hessian vector product (𝛁^2f(x))y and stores the result in `rp`,
-- (𝛁f(x) is stored in `r`).
let hessvecprod_f =
  lam x. lam y. lam r. lam rp. dualtensorJacfvecprod (dualtensorGrad f) x y r rp
in

-- Analytical solution to 𝛁f(x)
let primal_h_f = lam x. lam r.
  let x1 = tensorGetExn x [0] in
  let x2 = tensorGetExn x [1] in
  let r1 = addf (mulf 2. (mulf x1 x2)) (mulf 2. (mulf x2 x2)) in
  let r2 =
    addf (mulf x1 x1) (mulf 4. (mulf x1 x2))
  in
  tensorSetExn r [0] r1;
  tensorSetExn r [1] r2;
  ()
in

-- Analytical solution to (𝛁^2f(x))y.
let pertubation_h_f = lam x. lam y. lam r.
  let x1 = tensorGetExn x [0] in
  let x2 = tensorGetExn x [1] in
  let y1 = tensorGetExn y [0] in
  let y2 = tensorGetExn y [1] in
  let r1 =
    addf (mulf 2. (mulf x2 y1)) (mulf y2 (addf (mulf 2. x1) (mulf 4. x2)))
  in
  let r2 =
    addf (mulf y1 (addf (mulf 2. x1) (mulf 4. x2))) (mulf 4. (mulf x1 y2))
  in
  tensorSetExn r [0] r1;
  tensorSetExn r [1] r2;
  ()
in

hessvecprod_f (_t x) (_t y) (_t r1) (_t rp1);
primal_h_f x r2;
pertubation_h_f x y rp2;

utest r1 with r2 using _Eq in
utest rp1 with rp2 using _Eq in

let f = lam x. lam r.
  let x1 = dualtensorGetExn x [0] in
  let x2 = dualtensorGetExn x [1] in
  let r1 =
    addn (muln (muln x1 x1) x2) (muln (Primal 2.) (muln x1 (muln x2 x2)))
  in
  let r2 = muln x1 x2 in
  let r3 = muln x1 x1 in
  dualtensorSetExn r [0] r1;
  dualtensorSetExn r [1] r2;
  dualtensorSetExn r [2] r3;
  ()
in

let hess_f = lam x. lam t.
  let x1 = tensorGetExn x [0] in
  let x2 = tensorGetExn x [1] in
  let t111 = mulf 2. x2 in
  let t112 = addf (mulf 2. x1) (mulf 4. x2) in
  let t121 = addf (mulf 2. x1) (mulf 4. x2) in
  let t122 = mulf 4. x1 in
  let t211 = 0. in
  let t212 = 1. in
  let t221 = 1. in
  let t222 = 0. in
  let t311 = 2. in
  let t312 = 0. in
  let t321 = 0. in
  let t322 = 0. in
  tensorSetExn t [0, 0, 0] t111;
  tensorSetExn t [0, 0, 1] t112;
  tensorSetExn t [0, 1, 0] t121;
  tensorSetExn t [0, 1, 1] t122;
  tensorSetExn t [1, 0, 0] t211;
  tensorSetExn t [1, 0, 1] t212;
  tensorSetExn t [1, 1, 0] t221;
  tensorSetExn t [1, 1, 1] t222;
  tensorSetExn t [2, 0, 0] t311;
  tensorSetExn t [2, 0, 1] t312;
  tensorSetExn t [2, 1, 0] t321;
  tensorSetExn t [2, 1, 1] t322;
  ()
in

let t = tensorCreateDense [3, 2, 2] (lam. 0.) in
hess_f x t;
let t = tensorTransposeExn t 0 2 in

let r = tensorCreateDense [3] (lam. 0.) in
dualtensorHessijs f (_t x) 0 0 (_t r);
utest r with tensorSliceExn t [0, 0] using _Eq in

let r = tensorCreateDense [3] (lam. 0.) in
dualtensorHessijs f (_t x) 0 1 (_t r);
utest r with tensorSliceExn t [0, 1] using _Eq in

let r = tensorCreateDense [3] (lam. 0.) in
dualtensorHessijs f (_t x) 1 0 (_t r);
utest r with tensorSliceExn t [1, 0] using _Eq in

let r = tensorCreateDense [3] (lam. 0.) in
dualtensorHessijs f (_t x) 1 1 (_t r);
utest r with tensorSliceExn t [1, 1] using _Eq in

let f = lam x.
  let x1 = dualtensorGetExn x [0] in
  let x2 = dualtensorGetExn x [1] in
  addn (muln (muln x1 x1) x2) (muln (Primal 2.) (muln x1 (muln x2 x2)))
in

let hess_f = lam x. lam m.
  let x1 = tensorGetExn x [0] in
  let x2 = tensorGetExn x [1] in
  let t11 = mulf 2. x2 in
  let t12 = addf (mulf 2. x1) (mulf 4. x2) in
  let t21 = addf (mulf 2. x1) (mulf 4. x2) in
  let t22 = mulf 4. x1 in
  tensorSetExn m [0, 0] t11;
  tensorSetExn m [0, 1] t12;
  tensorSetExn m [1, 0] t21;
  tensorSetExn m [1, 1] t22;
  ()
in

let m = tensorCreateDense [2, 2] (lam. 0.) in
hess_f x m;

utest _primalDeep (dualtensorHessij f (_t x) 0 0)
with tensorGetExn m [0, 0] using eqf in
utest _primalDeep (dualtensorHessij f (_t x) 0 1)
with tensorGetExn m [0, 1] using eqf in
utest _primalDeep (dualtensorHessij f (_t x) 1 0)
with tensorGetExn m [1, 0] using eqf in
utest _primalDeep (dualtensorHessij f (_t x) 1 1)
with tensorGetExn m [1, 1] using eqf in

()
