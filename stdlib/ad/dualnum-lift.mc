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

type FloatFun2 = Float -> Float -> Float
type DualNumFun2 = DualNum -> DualNum -> DualNum

recursive
  -- lifts binary real operator to nested dual-numbers
  -- f : real operator
  -- dfdx1 : lifted first partial derivative of f
  -- dfdx2 : lifted second partial derivative of f
  let dualnumLift2 : DualNumFun2 -> DualNumFun2 -> DualNumFun2 -> DualNumFun2 =
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
-- DEEP PRIAMAL OPERATOR  --
----------------------------

-- Real part of arbritrary nested dual number p.
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

type FloatCmp2 = Float -> Float -> Bool

-- lifts compare function to nested dual-numbers. The compare functions is
-- applied to x in x+(en)x', where x and x' are reals, e.g. x+(en)x' is the
-- deepest element in the nested dual-number y+(e1)y'.
-- cmp : real compare function
let dualnumLiftBoolFun2 : FloatCmp2 -> (DualNum -> DualNum -> Bool) =
lam cmp.
  let self = lam p1. lam p2.
    cmp (_unpack (dualnumPrimalDeep p1)) (_unpack (dualnumPrimalDeep p2))
  in self

let _liftBool = dualnumLiftBoolFun2


-- Real part of arbritrary nested dual number p as string.
let dualnum2string : DualNum -> String =
lam p. float2string (_unpack (dualnumPrimalDeep p))

utest dualnum2string num0 with "0."
utest dualnum2string dnum134 with "3."
utest dualnum2string (dnum1 dnum036 dnum048) with "3."


---------------------------------
-- LIFTING OF UNARY OPERATORS  --
---------------------------------

type FloatFun1 = Float -> Float
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

-- As well as scalar higher order derivatives
recursive
let nder : Int -> (DualNum -> DualNum) -> DualNum -> DualNum =
  lam n. lam f. lam x.
    if lti n 0 then error "Negative derivative order"
    else if eqi n 0 then f x
    else nder (subi n 1) (der f) x
end


----------------
-- CONSTANTS  --
----------------

let epsn = _num 1.e-15


-----------------------
-- BOLEAN OPERATORS  --
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

-- lifted substraction
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


-- lifted approximate comapre function
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
