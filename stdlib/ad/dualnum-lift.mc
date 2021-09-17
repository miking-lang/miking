-- This is an implementation of functions lifting operators over reals to nested
-- dual-numbers described in the paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.



include "dualnum-tree.mc"
include "dualnum-helpers.mc"
include "bool.mc"
include "math.mc"
include "tensor.mc"
include "common.mc"

-------------
-- ALIASES --
-------------

let _num = dualnumNum
let _dnum = dualnumDNum

let _ltE = dualnumLtE
let _isDualNum = dualnumIsDualNum
let _epsilon = dualnumEpsilon
let _primal = dualnumPrimal
let _pertubation = dualnumPertubation
let _unpack = dualnumUnpackNum
let _float2num2 = dualnumFloat2num2
let _float2num1 = dualnumFloat2num1


----------------------------------
-- LIFTING OF BINARY OPERATORS  --
----------------------------------

type DualNumFun2 = DualNum -> DualNum -> DualNum

recursive
  -- lifts binary real operator to nested dual-numbers
  -- f : real operator
  -- dfdx1 : lifted first partial derivative of f
  -- dfdx2 : lifted second partial derivative of f
  let dualnumLift2
  : DualNumFun2 -> DualNumFun2 -> DualNumFun2 -> DualNumFun2 =
  lam f. lam dfdx1. lam dfdx2.
    recursive let self = lam p1. lam p2.
      if or (_isDualNum p1)
            (_isDualNum p2)
      then
        let e = if not (_isDualNum p1) then _epsilon p2
                else if not (_isDualNum p2) then _epsilon p1
                else if _ltE (_epsilon p1) (_epsilon p2) then _epsilon p2
                else _epsilon p1
        in

        _dnum e
             (self (_primal e p1) (_primal e p2))
             (addn (muln (dfdx1 (_primal e p1) (_primal e p2))
                         (_pertubation e p1))
                   (muln (dfdx2 (_primal e p1) (_primal e p2))
                         (_pertubation e p2)))
      else
        f p1 p2
    in self

    -- lifted addition
    let addn = lam p1. lam p2.
      dualnumLift2
        (_float2num2 addf)
        (lam x1. lam x2. (_num 1.))
        (lam x1. lam x2. (_num 1.))
        p1 p2

    -- lifted multiplication
    let muln = lam p1. lam p2.
      dualnumLift2
        (_float2num2 mulf)
        (lam x1. lam x2. x2)
        (lam x1. lam x2. x1)
        p1 p2
end

let _lift2 = dualnumLift2

-- addn
utest addn num1 num2 with num3 using dualnumEq eqf
utest addn dnum010 num2 with dnum0 num3 num0 using dualnumEq eqf
utest addn dnum011 num2 with dnum031 using dualnumEq eqf
utest addn dnum011 dnum011 with dnum022 using dualnumEq eqf
utest addn dnum011 dnum111 with dnum1 dnum021 num1 using dualnumEq eqf

-- muln
utest muln num1 num2 with num2 using dualnumEq eqf
utest muln dnum010 num2 with dnum0 num2 num0 using dualnumEq eqf
utest muln dnum011 num2 with dnum022 using dualnumEq eqf
utest muln dnum012 dnum034 with dnum0 num3 num10 using dualnumEq eqf
utest muln dnum012 dnum134 with dnum1 dnum036 dnum048 using dualnumEq eqf



----------------------------
-- DEEP PRIMAL OPERATOR  --
----------------------------

-- Real part of arbitrary nested dual number p.
recursive
let dualnumPrimalDeep : DualNum -> DualNum =
lam p.
   if not (_isDualNum p) then p
   else dualnumPrimalDeep (_primal (_epsilon p) p)
end

utest dualnumPrimalDeep num0 with num0 using dualnumEq eqf
utest dualnumPrimalDeep dnum134 with num3 using dualnumEq eqf
utest dualnumPrimalDeep (dnum1 dnum036 dnum048) with num3 using dualnumEq eqf


----------------------------------
-- LIFTING OF BINARY OPERATORS  --
----------------------------------

type Cmp2 = Float -> Float -> Bool

-- lifts compare function to nested dual-numbers. The compare functions is
-- applied to x in x+(en)x', where x and x' are reals, e.g. x+(en)x' is the
-- deepest element in the nested dual-number y+(e1)y'.
-- cmp : real compare function
let dualnumLiftBoolFun2 : Cmp2 -> (DualNum -> DualNum -> Bool) =
lam cmp.
  let self = lam p1. lam p2.
    cmp (_unpack (dualnumPrimalDeep p1)) (_unpack (dualnumPrimalDeep p2))
  in self

let _liftBool = dualnumLiftBoolFun2


-- Real part of arbitrary nested dual number p as string.
let dualnum2string : DualNum -> String =
lam p. float2string (_unpack (dualnumPrimalDeep p))

utest dualnum2string num0 with "0."
utest dualnum2string dnum134 with "3."
utest dualnum2string (dnum1 dnum036 dnum048) with "3."


---------------------------------
-- LIFTING OF UNARY OPERATORS  --
---------------------------------

type DualNumFun1 = DualNum -> DualNum

-- lifts unary real operator to nested dual-numbers
-- f : real operator
-- dfdx : lifted derivative of f
let dualnumLift1 : DualNumFun1 -> DualNumFun1 -> DualNumFun1 =
lam f. lam dfdx.
  recursive let self = lam p.
    if _isDualNum p then
      let e = _epsilon p in
      _dnum e
           (self (_primal e p))
                 (muln (dfdx (_primal e p))
                       (_pertubation e p))
    else
      f p
  in self

let _lift1 = dualnumLift1


---------------------------
-- DERIVATIVE OPERATORS  --
---------------------------

-- We define the scalar derivative operator over dual numbers
let der : (DualNum -> DualNum) -> DualNum -> DualNum =
  lam f. lam x.
  let e = genEpsilon () in
  _pertubation e (f (_dnum e x (_num 1.)))

utest der (lam. num2) num2 with num0
utest der (lam x. muln x x) (num2) with num4

-- As well as scalar higher order derivatives
recursive
let nder : Int -> (DualNum -> DualNum) -> DualNum -> DualNum =
  lam n. lam f. lam x.
    if lti n 0 then error "Negative derivative order"
    else if eqi n 0 then f x
    else nder (subi n 1) (der f) x
end

utest nder 0 (lam x. muln x x) (num2) with num4
utest nder 1 (lam x. muln x x) (num4) with num8
utest nder 2 (lam x. muln x x) (num4) with num2

-- Inplace computation of the i'th component of the Jacobian df_j/dx_i.
let jaci
  : (Tensor[DualNum] -> Tensor[DualNum] -> ())
  -> Int
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam i. lam x. lam r.
  let e = genEpsilon () in
  tensorSetExn x [i] (_dnum e (tensorGetExn x [i]) (_num 1.));
  f x r;
  tensorMapInplace (_pertubation e) r;
  tensorSetExn x [i] (_primal e (tensorGetExn x [i]))

-- Inplace computation of Jacobian df_j/dx_i, where j index columns and i index
-- rows, of `f` at `x` stored in `m`.
let jacT
  : (Tensor[DualNum] -> Tensor[DualNum] -> ())
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam j. tensorIterSlice (lam i. lam r. jaci f i x r) j

utest
  let f = lam t. lam r.
    let x1 = tensorGetExn t [0] in
    let x2 = tensorGetExn t [1] in
    tensorSetExn r [0] (addn x1 (muln (_num 2.) x2));
    tensorSetExn r [1] (muln (muln (_num 3.) x1) (muln (_num 4.) x2));
    ()
  in
  let x = tensorOfSeqExn tensorCreateDense [2] [_num 1., _num 2.] in
  let m = tensorCreateDense [2, 2] (lam. _num 0.) in
  jacT f x m;
  map _unpack (tensorToSeqExn (tensorReshapeExn m [4]))
with
[
  1., 24.,
  2., 12.
]

utest
  let f = lam x. lam r.
    let x0 = tensorGetExn x [0] in
    let x1 = tensorGetExn x [1] in
    let x2 = tensorGetExn x [2] in
    let x3 = tensorGetExn x [3] in
    tensorSetExn r [0] (muln x0 (muln x1 (muln x2 x3)));
    tensorSetExn r [1] (addn (muln x0 x0) (addn (muln x1 x1)
                                          (addn (muln x2 x2) (muln x3 x3))));
    ()
  in
  let x =
    tensorOfSeqExn tensorCreateDense [4] [_num 1., _num 5., num 5., num 1.]
  in
  let m = tensorCreateDense [4, 2] (lam. _num 0.) in
  jacT f x m;
  map _unpack (tensorToSeqExn (tensorReshapeExn m [8]))
with
[
  25., 2.,
  5., 10.,
  5., 10.,
  25., 2.
]

-- Inplace computation of gradient df/dx_i of `f` at `x` stored in `g`.
let grad
  : (Tensor[DualNum] -> DualNum)
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam g.
  if and (tensorHasRank x 1) (tensorHasRank g 1) then
    tensorIteri
      (lam idx. lam xi.
        let e = genEpsilon () in
        tensorSetExn x idx (_dnum e xi (_num 1.));
        tensorSetExn g idx (_pertubation e (f x));
        tensorSetExn x idx xi)
      x
   else error "Invalid Input: grad"

utest
  let f = lam x.
    let x1 = tensorGetExn x [0] in
    let x2 = tensorGetExn x [1] in
    muln x1 x2
  in
  let x = tensorOfSeqExn tensorCreateDense [2] [_num 2., _num 3.] in
  let g = tensorCreateDense [2] (lam. _num 0.) in
  grad f x g;
  map _unpack (tensorToSeqExn g)
with [3., 2.]

-- Computes the ij'th component of the Hessian d2f/(dx_i)(dx_j) of `f` at `x`.
let hessij
  : (Tensor[DualNum] -> DualNum)
  -> Int
  -> Int
  -> Tensor[DualNum]
  -> DualNum =
lam f. lam i. lam j. lam x.
  let ei = genEpsilon () in
  let ej = genEpsilon () in
  let xi = tensorGetExn x [i] in
  tensorSetExn x [i] (_dnum ei xi (_num 1.));
  let xj = tensorGetExn x [j] in
  tensorSetExn x [j] (_dnum ej xj (_num 1.));
  let hij = _pertubation ei (_pertubation ej (f x)) in
  tensorSetExn x [j] xj;
  tensorSetExn x [i] xi;
  hij

-- Inplace computation of Hessian d2f/(dx_i)(dx_j) of `f` at `x` stored in `h`.
let hess
  : (Tensor[DualNum] -> DualNum)
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam h.
  if and (tensorHasRank x 1) (tensorHasRank h 2) then
    tensorIterSlice
      (lam i. lam hi. tensorMapiInplace (lam idxj. lam. hessij f i (head idxj) x) hi) h
  else error "Invalid Input: hess"

utest
  let f = lam x.
    let x1 = tensorGetExn x [0] in
    let x2 = tensorGetExn x [1] in
    muln (muln x1 x1) (muln x2 x2)
  in
  let x = tensorOfSeqExn tensorCreateDense [2] [_num 2., _num 3.] in
  let h = tensorCreateDense [2, 2] (lam. _num 0.) in
  hess f x h;
  map _unpack (tensorToSeqExn (tensorReshapeExn h [4]))
with
[
  18., 24.,
  24., 8.
]

-- Computes the ij'th component of the Hessian d2f_k/(dx_i)(dx_j) simultaneously
-- for each component k of vector valued function `f` at `x`, storing the result
-- in `hij`.
let hessijs
  : (Tensor[DualNum] -> Tensor[DualNum] -> ())
  -> Int
  -> Int
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam i. lam j. lam x. lam hij.
  let ei = genEpsilon () in
  let ej = genEpsilon () in
  let xi = tensorGetExn x [i] in
  tensorSetExn x [i] (_dnum ei xi (_num 1.));
  let xj = tensorGetExn x [j] in
  tensorSetExn x [j] (_dnum ej xj (_num 1.));
  f x hij;
  tensorMapInplace (lam h. _pertubation ei (_pertubation ej h)) hij;
  tensorSetExn x [j] xj;
  tensorSetExn x [i] xi;
  ()

utest
  let f = lam x. lam r.
    let x1 = tensorGetExn x [0] in
    let x2 = tensorGetExn x [1] in
    tensorSetExn r [0] (muln (muln x1 x1) (muln x2 x2));
    tensorSetExn r [1] (addn (muln x1 x2) (muln x1 x2));
    ()
  in
  let x = tensorOfSeqExn tensorCreateDense [2] [_num 2., _num 3.] in
  let hij = tensorCreateDense [2] (lam. _num 0.) in
  hessijs f 0 1 x hij;
  map _unpack (tensorToSeqExn (hij))
with [24., 2.]


----------------
-- CONSTANTS  --
----------------

let epsn = _num 1.e-15


-----------------------
-- BOOLEAN OPERATORS  --
-----------------------

let eqn = _liftBool eqf -- lifted ==

utest eqn num1 num1 with true
utest eqn num1 num2 with false
utest eqn (_dnum e2 dnum112 num3) num1 with true
utest eqn (_dnum e2 dnum112 num3) num2 with false


let neqn = _liftBool neqf -- lifted !=

utest neqn num1 num1 with false
utest neqn num1 num2 with true
utest neqn (_dnum e2 dnum112 num3) num1 with false
utest neqn (_dnum e2 dnum112 num3) num2 with true


let ltn = _liftBool ltf -- lifted <

utest ltn num1 num1 with false
utest ltn num1 num2 with true
utest ltn num2 num1 with false
utest ltn (_dnum e2 dnum112 num3) num1 with false
utest ltn (_dnum e2 dnum112 num3) num2 with true
utest ltn num2 (_dnum e2 dnum112 num3) with false


let leqn = _liftBool leqf -- lifted <=

utest leqn num1 num1 with true
utest leqn num1 num2 with true
utest leqn num2 num1 with false
utest leqn (_dnum e2 dnum112 num3) num1 with true
utest leqn (_dnum e2 dnum112 num3) num2 with true
utest leqn num2 (_dnum e2 dnum112 num3) with false


let gtn = _liftBool gtf -- lifted >

utest gtn num1 num1 with false
utest gtn num1 num2 with false
utest gtn num2 num1 with true
utest gtn (_dnum e2 dnum112 num3) num1 with false
utest gtn (_dnum e2 dnum112 num3) num2 with false
utest gtn num2 (_dnum e2 dnum112 num3) with true


let geqn = _liftBool geqf -- lifted >=

utest geqn num1 num1 with true
utest geqn num1 num2 with false
utest geqn num2 num1 with true
utest geqn (_dnum e2 dnum112 num3) num1 with true
utest geqn (_dnum e2 dnum112 num3) num2 with false
utest geqn num2 (_dnum e2 dnum112 num3) with true


---------------------------
-- ARITHMETIC OPERATORS  --
---------------------------

-- lifted negation
let negn = lam p. _lift1 (_float2num1 negf) (lam x. _num (negf 1.)) p

utest negn num1 with _num (negf 1.) using dualnumEq eqf
utest negn dnum010 with dnum0 (_num (negf 1.)) num0 using dualnumEq eqf
utest negn dnum012 with dnum0 (_num (negf 1.)) (_num (negf 2.))
using dualnumEq eqf

utest der negn num1 with negn num1 using dualnumEq eqf

-- lifted subtraction
let subn = lam p1. lam p2.
  _lift2
    (_float2num2 subf)
    (lam x1. lam x2. (_num 1.))
    (lam x1. lam x2. negn (_num 1.))
    p1 p2

utest subn num2 num1 with num1 using dualnumEq eqf
utest subn dnum020 num1 with dnum0 num1 num0 using dualnumEq eqf
utest subn dnum021 num1 with dnum011 using dualnumEq eqf
utest subn dnum022 dnum011 with dnum011 using dualnumEq eqf

utest
  let r = subn dnum122 dnum011 in
  dualnumPrimal e1 r
with dnum0 num1 (_num (negf 1.)) using dualnumEq eqf


-- lifted abs
let absn = lam p. if ltn p num0 then negn p else p


-- lifted approximate compare function
let eqnEps = lam l. lam r.
  ltn (absn (subn l r)) epsn


recursive
  -- lifted division
  let divn = lam p1. lam p2.
    _lift2
      (_float2num2 divf)
      (lam x1. lam x2. divn (_num 1.) x2)
      (lam x1. lam x2. divn (negn x1) (muln x2 x2))
      p1 p2
end

utest divn num4 num2 with num2 using dualnumEq eqf
utest divn dnum040 num2 with dnum0 num2 num0 using dualnumEq eqf
utest divn dnum044 num2 with dnum022 using dualnumEq eqf

utest divn dnum012 dnum034
with dnum0 (_num (divf 1. 3.)) (_num (divf 2. 9.)) using dualnumEq eqf

utest divn dnum012 dnum134
with dnum1 (dnum0 (_num (divf 1. 3.))
                  (_num (divf 2. 3.)))
           (dnum0 (_num (divf (negf 4.) 9.))
                  (_num (divf (negf 8.) 9.)))
using dualnumEq eqf
