-- This is an implementation of functions lifting operators over reals to nested
-- dual-bers described in the paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.



include "dualnum-tree.mc"
-- include "dualnum-alist.mc"
include "bool.mc"
include "math.mc"
include "tensor.mc"
include "common.mc"

-------------
-- ALIASES --
-------------

let _dnum = dualnumCreateDual
let _ltE = dualLtE
let _isDualNum = dualnumIsDualNum
let _epsilon = dualnumEpsilon
let _primal = dualnumPrimal
let _primalDeep = dualnumPrimalDeep
let _pertubation = dualnumPertubation
let _lift2 = dualnumLift2
let _lift1 = dualnumLift1
let _genEpsilon = dualGenEpsilon

let _num0 = Primal 0.
let _num1 = Primal 1.
let _num2 = Primal 2.
let _num3 = Primal 3.
let _num4 = Primal 4.
let _num6 = Primal 6.
let _num8 = Primal 8.
let _num10 = Primal 10.

let _e0 = _genEpsilon ()
let _e1 = _genEpsilon ()
let _e2 = _genEpsilon ()
let _e3 = _genEpsilon ()

let _dnum0 = _dnum _e0
let _dnum1 = _dnum _e1
let _dnum010 = _dnum0 _num1 _num0
let _dnum011 = _dnum0 _num1 _num1
let _dnum012 = _dnum0 _num1 _num2
let _dnum020 = _dnum0 _num2 _num0
let _dnum021 = _dnum0 _num2 _num1
let _dnum022 = _dnum0 _num2 _num2
let _dnum031 = _dnum0 _num3 _num1
let _dnum034 = _dnum0 _num3 _num4
let _dnum036 = _dnum0 _num3 _num6
let _dnum040 = _dnum0 _num4 _num0
let _dnum044 = _dnum0 _num4 _num4
let _dnum048 = _dnum0 _num4 _num8
let _dnum111 = _dnum1 _num1 _num1
let _dnum112 = _dnum1 _num1 _num2
let _dnum122 = _dnum1 _num2 _num2
let _dnum134 = _dnum1 _num3 _num4


----------------------------------
-- LIFTING OF BINARY OPERATORS  --
----------------------------------

type Cmp2 = Float -> Float -> Bool

-- lifts compare function to nested dual-numbers. The compare functions is
-- applied to x in x+(en)x', where x and x' are reals, e.g. x+(en)x' is the
-- deepest element in the nested dual-number y+(e1)y'.
-- cmp : real compare function
let dualnumLiftBoolFun2 : Cmp2 -> (DualNum -> DualNum -> Bool) =
lam cmp. lam p1. lam p2. cmp (_primalDeep p1) (_primalDeep p2)

let _liftBool = dualnumLiftBoolFun2

---------------------------
-- DERIVATIVE OPERATORS  --
---------------------------

-- We define the scalar derivative operator over dual numbers
let der : (DualNum -> DualNum) -> DualNum -> DualNum =
  lam f. lam x.
  let e = _genEpsilon () in
  _pertubation e (f (_dnum e x (Primal 1.)))

utest der (lam. _num2) _num2 with _num0 using dualnumEq eqf
utest der (lam x. muln x x) (_num2) with _num4 using dualnumEq eqf

-- As well as scalar higher order derivatives
recursive
let nder
  : Int -> (DualNum -> DualNum) -> DualNum -> DualNum =
  lam n. lam f.
    if lti n 0 then error "Negative derivative order"
    else if eqi n 0 then f
    else nder (subi n 1) (der f)
end

utest nder 0 (lam x. muln x x) (_num2) with _num4 using dualnumEq eqf
utest nder 1 (lam x. muln x x) (_num4) with _num8 using dualnumEq eqf
utest nder 2 (lam x. muln x x) (_num4) with _num2 using dualnumEq eqf

-- Inplace computation of the i'th component of the Jacobian df_j/dx_i.
let dualnumJacj
  : (Tensor[DualNum] -> Tensor[DualNum] -> ())
  -> Tensor[DualNum]
  -> Int
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam i. lam r.
  let e = _genEpsilon () in
  tensorSetExn x [i] (_dnum e (tensorGetExn x [i]) (Primal 1.));
  f x r;
  tensorMapInplace (_pertubation e) r;
  tensorSetExn x [i] (_primal e (tensorGetExn x [i]))

-- Inplace computation of Jacobian df_j/dx_i, where j index columns and i index
-- rows, of `f` at `x` stored in `m`.
let dualnumJacT
  : (Tensor[DualNum] -> Tensor[DualNum] -> ())
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam t. tensorIterSlice (lam j. lam r. dualnumJacj f x j r) t

utest
  let f = lam t. lam r.
    let x1 = tensorGetExn t [0] in
    let x2 = tensorGetExn t [1] in
    tensorSetExn r [0] (addn x1 (muln (Primal 2.) x2));
    tensorSetExn r [1] (muln (muln (Primal 3.) x1) (muln (Primal 4.) x2));
    ()
  in
  let x = tensorOfSeqExn tensorCreateDense [2] [Primal 1., Primal 2.] in
  let m = tensorCreateDense [2, 2] (lam. Primal 0.) in
  dualnumJacT f x m;
  map _primalDeep (tensorToSeqExn (tensorReshapeExn m [4]))
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
    tensorOfSeqExn
      tensorCreateDense
      [4]
      [Primal 1., Primal 5., Primal 5., Primal 1.]
  in
  let m = tensorCreateDense [4, 2] (lam. Primal 0.) in
  dualnumJacT f x m;
  map _primalDeep (tensorToSeqExn (tensorReshapeExn m [8]))
with
[
  25., 2.,
  5., 10.,
  5., 10.,
  25., 2.
]

-- Inplace computation of gradient df/dx_i of `f` at `x` stored in `g`.
let dualnumGrad
  : (Tensor[DualNum] -> DualNum)
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam g.
  if and (tensorHasRank x 1) (tensorHasRank g 1) then
    let e = _genEpsilon () in
    tensorIteri
      (lam idx. lam xi.
        tensorSetExn x idx (_dnum e xi (Primal 1.));
        tensorSetExn g idx (_pertubation e (f x));
        tensorSetExn x idx xi)
      x
   else error "Invalid Input: dualnumGrad"

utest
  let f = lam x.
    let x1 = tensorGetExn x [0] in
    let x2 = tensorGetExn x [1] in
    muln x1 x2
  in
  let x = tensorOfSeqExn tensorCreateDense [2] [Primal 2., Primal 3.] in
  let g = tensorCreateDense [2] (lam. Primal 0.) in
  dualnumGrad f x g;
  map _primalDeep (tensorToSeqExn g)
with [3., 2.]

-- Computes the ij'th component of the Hessian d2f/(dx_i)(dx_j) of `f` at `x`.
let dualnumHessij
  : (Tensor[DualNum] -> DualNum)
  -> Tensor[DualNum]
  -> Int
  -> Int
  -> DualNum =
lam f. lam x. lam i. lam j.
  let ei = _genEpsilon () in
  let ej = _genEpsilon () in
  let xi = tensorGetExn x [i] in
  tensorSetExn x [i] (_dnum ei xi (Primal 1.));
  let xj = tensorGetExn x [j] in
  tensorSetExn x [j] (_dnum ej xj (Primal 1.));
  let hij = _pertubation ei (_pertubation ej (f x)) in
  tensorSetExn x [j] xj;
  tensorSetExn x [i] xi;
  hij

-- Inplace computation of Hessian d2f/(dx_i)(dx_j) of `f` at `x` stored in `h`.
let dualnumHess
  : (Tensor[DualNum] -> DualNum)
  -> Tensor[DualNum]
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam h.
  if and (tensorHasRank x 1) (tensorHasRank h 2) then
    tensorIterSlice
      (lam i. lam hi.
        tensorMapiInplace (lam idxj. lam. dualnumHessij f x i (head idxj)) hi) h
  else error "Invalid Input: dualnumHess"

utest
  let f = lam x.
    let x1 = tensorGetExn x [0] in
    let x2 = tensorGetExn x [1] in
    muln (muln x1 x1) (muln x2 x2)
  in
  let x = tensorOfSeqExn tensorCreateDense [2] [Primal 2., Primal 3.] in
  let h = tensorCreateDense [2, 2] (lam. Primal 0.) in
  dualnumHess f x h;
  map _primalDeep (tensorToSeqExn (tensorReshapeExn h [4]))
with
[
  18., 24.,
  24., 8.
]

-- Computes the ij'th component of the Hessian d2f_k/(dx_i)(dx_j) simultaneously
-- for each component k of vector valued function `f` at `x`, storing the
-- result in `hij`.
let dualnumHessijs
  : (Tensor[DualNum] -> Tensor[DualNum] -> ())
  -> Tensor[DualNum]
  -> Int
  -> Int
  -> Tensor[DualNum]
  -> () =
lam f. lam x. lam i. lam j. lam hij.
  let ei = _genEpsilon () in
  let ej = _genEpsilon () in
  let xi = tensorGetExn x [i] in
  tensorSetExn x [i] (_dnum ei xi (Primal 1.));
  let xj = tensorGetExn x [j] in
  tensorSetExn x [j] (_dnum ej xj (Primal 1.));
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
  let x = tensorOfSeqExn tensorCreateDense [2] [Primal 2., Primal 3.] in
  let hij = tensorCreateDense [2] (lam. Primal 0.) in
  dualnumHessijs f x 0 1 hij;
  map _primalDeep (tensorToSeqExn (hij))
with [24., 2.]


----------------
-- CONSTANTS  --
----------------

let epsn = Primal 1.e-15


-----------------------
-- BOOLEAN OPERATORS  --
-----------------------

let eqn = _liftBool eqf -- lifted ==

utest eqn _num1 _num1 with true
utest eqn _num1 _num2 with false
utest eqn (_dnum _e2 _dnum112 _num3) _num1 with true
utest eqn (_dnum _e2 _dnum112 _num3) _num2 with false


let neqn = _liftBool neqf -- lifted !=

utest neqn _num1 _num1 with false
utest neqn _num1 _num2 with true
utest neqn (_dnum _e2 _dnum112 _num3) _num1 with false
utest neqn (_dnum _e2 _dnum112 _num3) _num2 with true


let ltn = _liftBool ltf -- lifted <

utest ltn _num1 _num1 with false
utest ltn _num1 _num2 with true
utest ltn _num2 _num1 with false
utest ltn (_dnum _e2 _dnum112 _num3) _num1 with false
utest ltn (_dnum _e2 _dnum112 _num3) _num2 with true
utest ltn _num2 (_dnum _e2 _dnum112 _num3) with false


let leqn = _liftBool leqf -- lifted <=

utest leqn _num1 _num1 with true
utest leqn _num1 _num2 with true
utest leqn _num2 _num1 with false
utest leqn (_dnum _e2 _dnum112 _num3) _num1 with true
utest leqn (_dnum _e2 _dnum112 _num3) _num2 with true
utest leqn _num2 (_dnum _e2 _dnum112 _num3) with false


let gtn = _liftBool gtf -- lifted >

utest gtn _num1 _num1 with false
utest gtn _num1 _num2 with false
utest gtn _num2 _num1 with true
utest gtn (_dnum _e2 _dnum112 _num3) _num1 with false
utest gtn (_dnum _e2 _dnum112 _num3) _num2 with false
utest gtn _num2 (_dnum _e2 _dnum112 _num3) with true


let geqn = _liftBool geqf -- lifted >=

utest geqn _num1 _num1 with true
utest geqn _num1 _num2 with false
utest geqn _num2 _num1 with true
utest geqn (_dnum _e2 _dnum112 _num3) _num1 with true
utest geqn (_dnum _e2 _dnum112 _num3) _num2 with false
utest geqn _num2 (_dnum _e2 _dnum112 _num3) with true


---------------------------
-- ARITHMETIC OPERATORS  --
---------------------------

-- lifted addition
utest addn _num1 _num2 with _num3 using dualnumEq eqf
utest addn _dnum010 _num2 with _dnum0 _num3 _num0 using dualnumEq eqf
utest addn _dnum011 _num2 with _dnum031 using dualnumEq eqf
utest addn _dnum011 _dnum011 with _dnum022 using dualnumEq eqf
utest addn _dnum011 _dnum111 with _dnum1 _dnum021 _num1 using dualnumEq eqf

-- lifted multiplication
utest muln _num1 _num2 with _num2 using dualnumEq eqf
utest muln _dnum010 _num2 with _dnum0 _num2 _num0 using dualnumEq eqf
utest muln _dnum011 _num2 with _dnum022 using dualnumEq eqf
utest muln _dnum012 _dnum034 with _dnum0 _num3 _num10 using dualnumEq eqf
utest muln _dnum012 _dnum134 with _dnum1 _dnum036 _dnum048 using dualnumEq eqf

-- lifted negation
let negn = lam p. _lift1 negf (lam. Primal (negf 1.)) p

utest negn _num1 with Primal (negf 1.) using dualnumEq eqf
utest negn _num0 with Primal (negf 0.) using dualnumEq eqf
utest negn _dnum010 with _dnum0 (Primal (negf 1.)) _num0 using dualnumEq eqf
utest negn _dnum012 with _dnum0 (Primal (negf 1.)) (Primal (negf 2.))
using dualnumEq eqf

utest der negn _num1 with negn _num1 using dualnumEq eqf

-- lifted subtraction
let subn = lam p1. lam p2.
  _lift2
    subf
    (lam. lam. (Primal 1.))
    (lam. lam. negn (Primal 1.))
    p1 p2

utest subn _num2 _num1 with _num1 using dualnumEq eqf
utest subn _dnum020 _num1 with _dnum0 _num1 _num0 using dualnumEq eqf
utest subn _dnum021 _num1 with _dnum011 using dualnumEq eqf
utest subn _dnum022 _dnum011 with _dnum011 using dualnumEq eqf

utest
  let r = subn _dnum122 _dnum011 in
  dualnumPrimal _e1 r
with _dnum0 _num1 (Primal (negf 1.)) using dualnumEq eqf


-- lifted abs
let absn = lam p. if ltn p _num0 then negn p else p


-- lifted approximate compare function
let eqnEps = lam l. lam r.
  ltn (absn (subn l r)) epsn


recursive
  -- lifted division
  let divn = lam p1. lam p2.
    _lift2
      divf
      (lam. lam x2. divn (Primal 1.) x2)
      (lam x1. lam x2. divn (negn x1) (muln x2 x2))
      p1 p2
end

utest divn _num4 _num2 with _num2 using dualnumEq eqf
utest divn _dnum040 _num2 with _dnum0 _num2 _num0 using dualnumEq eqf
utest divn _dnum044 _num2 with _dnum022 using dualnumEq eqf

utest divn _dnum012 _dnum034
with _dnum0 (Primal (divf 1. 3.)) (Primal (divf 2. 9.)) using dualnumEq eqf

utest divn _dnum012 _dnum134
with _dnum1 (_dnum0 (Primal (divf 1. 3.))
                    (Primal (divf 2. 3.)))
            (_dnum0 (Primal (divf (negf 4.) 9.))
                    (Primal (divf (negf 8.) 9.)))
using dualnumEq eqf
