-- This file elementary functions lifted to nested dual-numbers. See
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.


include "ad/dualnum-lift.mc"
include "ad/dualnum-helpers.mc"
include "math.mc"

-------------
-- ALIASES --
-------------

let _num = dualnumNum
let _dnum = dualnumDNum
let _lift1 = dualnumLift1
let _lift2 = dualnumLift2
let _float2num1 = dualnumFloat2num1
let _float2num2 = dualnumFloat2num2

----------------
-- CONSTANTS  --
----------------

let pin = num pi


---------------------------
-- ELEMENTARY FUNCTIONS  --
---------------------------

-- Trigonometric functions
recursive
  let sinn = lam p. _lift1 (_float2num1 sin) cosn p
  let cosn = lam p. _lift1 (_float2num1 cos) (lam x. negn (sinn x)) p
end

utest sinn (divn pin num2) with num1 using eqnEps
utest sinn num0 with num0 using eqnEps

utest cosn (divn pin num2) with num0 using eqnEps
utest cosn num0 with num1 using eqnEps

utest addn (muln (sinn num1) (sinn num1)) (muln (cosn num1) (cosn num1))
with num1 using eqnEps

utest der sinn num1 with cosn num1 using eqnEps
utest der cosn num1 with negn (sinn num1) using eqnEps

-- Exponential function
recursive
  let expn = lam p. _lift1 (_float2num1 exp) expn p
end

utest expn num0 with num1 using eqnEps
utest der expn num1 with expn num1 using eqnEps

-- Natural logarithm
let logn = lam p. _lift1 (_float2num1 log) (lam x. divn (num 1.) x) p

utest logn num1 with num0 using eqnEps
utest logn (expn num3) with num3 using eqnEps
utest expn (logn num3) with num3 using eqnEps
utest der logn num1 with num1 using eqnEps

-- Power function
recursive
  let pown = lam p1. lam p2.
    _lift2
      (_float2num2 pow)
      (lam x1. lam x2. muln x2 (pown x1 (subn x2 (_num 1.))))
      (lam x1. lam x2.
        if eqn x1 (_num 0.) then
          if gtn x2 (_num 0.) then _num 0.
          else _num nan
        else
          muln (pown x1 x2) (logn x1))
      p1 p2
end

utest pown num3 num2 with _num 9. using eqnEps
utest der (lam x. pown x num2) num3 with num6 using eqnEps
utest der (pown (expn num1)) num2 with expn num2 using eqnEps
utest der (pow num0) num2 with num0 using eqnEps
utest der (pow num1) num0 with num0 using eqnEps
utest der (pow num1) num1 with num0 using eqnEps


-- Square root
recursive
  let sqrtn = lam p.
    _lift1
      (_float2num1 sqrt)
      (lam x. divn (num 1.) (muln (num 2.) (sqrtn x)))
      p
end

utest sqrtn (num 9.) with num3 using eqnEps
utest der sqrtn (num 9.) with divn num1 num6 using eqnEps
