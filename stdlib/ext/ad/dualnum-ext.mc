-- This file elementary functions lifted to nested dual-numbers. See
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.


include "ad/dualnum-lift.mc"
include "math.mc"

-------------
-- ALIASES --
-------------

let _lift1 = dualnumLift1
let _lift2 = dualnumLift2
let _num0 = Primal 0.
let _num1 = Primal 1.
let _num2 = Primal 2.
let _num3 = Primal 3.
let _num4 = Primal 4.
let _num6 = Primal 6.
let _num8 = Primal 8.
let _num10 = Primal 10.

----------------
-- CONSTANTS  --
----------------

let pin = Primal pi

---------------------------
-- ELEMENTARY FUNCTIONS  --
---------------------------

-- Trigonometric functions
recursive
  let sinn = lam p. _lift1 sin cosn p
  let cosn = lam p. _lift1 cos (lam x. negn (sinn x)) p
end

utest sinn (divn pin _num2) with _num1 using eqnEps
utest sinn _num0 with _num0 using eqnEps

utest cosn (divn pin _num2) with _num0 using eqnEps
utest cosn _num0 with _num1 using eqnEps

utest addn (muln (sinn _num1) (sinn _num1)) (muln (cosn _num1) (cosn _num1))
with _num1 using eqnEps

utest der sinn _num1 with cosn _num1 using eqnEps
utest der cosn _num1 with negn (sinn _num1) using eqnEps

-- Exponential function
recursive
  let expn = lam p. _lift1 exp expn p
end

utest expn _num0 with _num1 using eqnEps
utest der expn _num1 with expn _num1 using eqnEps

-- Natural logarithm
let logn = lam p. _lift1 log (lam x. divn (Primal 1.) x) p

utest logn _num1 with _num0 using eqnEps
utest logn (expn _num3) with _num3 using eqnEps
utest expn (logn _num3) with _num3 using eqnEps
utest der logn _num1 with _num1 using eqnEps

-- Power function
recursive
  let pown = lam p1. lam p2.
    _lift2
      pow
      (lam x1. lam x2. muln x2 (pown x1 (subn x2 (Primal 1.))))
      (lam x1. lam x2.
        if eqn x1 (Primal 0.) then
          if gtn x2 (Primal 0.) then Primal 0.
          else Primal nan
        else
          muln (pown x1 x2) (logn x1))
      p1 p2
end

utest pown _num3 _num2 with Primal 9. using eqnEps
utest der (lam x. pown x _num2) _num3 with _num6 using eqnEps
utest der (pown (expn _num1)) _num2 with expn _num2 using eqnEps
utest der (pown _num0) _num2 with _num0 using eqnEps
utest der (pown _num1) _num0 with _num0 using eqnEps
utest der (pown _num1) _num1 with _num0 using eqnEps

-- Square root
recursive
  let sqrtn = lam p.
    _lift1
      sqrt
      (lam x. divn (Primal 1.) (muln (Primal 2.) (sqrtn x)))
      p
end

utest sqrtn (Primal 9.) with _num3 using eqnEps
utest der sqrtn (Primal 9.) with divn _num1 _num6 using eqnEps
