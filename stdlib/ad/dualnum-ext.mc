-- This file elementary functions lifted to nested dual-numbers. See
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.

include "dualnum-arith.mc"
include "dualnum-bool.mc"
include "dualnum-helpers.mc"
include "ext/math.mc"

let num = dualnumNum
let dnum = dualnumDNum
let lift1 = dualnumLift1
let float2num1 = dualnumFloat2num1
let primal = dualnumPrimal
let pertubation = dualnumPertubation

let epsn = num eps
let pin = num pi

-- Elementary functions
let absn = lam p. if ltn p num0 then negn p else p

let eqnEps = lam l. lam r.
  ltn (absn (subn l r)) epsn

-- Trigonometric functions
recursive
  let sinn = lam p. lift1 (float2num1 sin) cosn p
  let cosn = lam p. lift1 (float2num1 cos) (lam x. negn (sinn x)) p
end

utest sinn (divn pin num2) with num1 using eqnEps
utest sinn num0 with num0 using eqnEps

utest cosn (divn pin num2) with num0 using eqnEps
utest cosn num0 with num1 using eqnEps

utest addn (muln (sinn num1) (sinn num1)) (muln (cosn num1) (cosn num1))
with num1 using eqnEps

utest pertubation e0 (sinn dnum011) with cosn num1 using eqnEps
utest pertubation e0 (cosn dnum011) with negn (sinn num1) using eqnEps

-- Exponential function
recursive
  let expn = lam p. lift1 (float2num1 exp) expn p
end

utest expn num0 with num1 using eqnEps
utest pertubation e0 (expn dnum011) with expn num1 using eqnEps
