-- This file contains arithmetic operators lifted to nested dual-numbers. See
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.



include "dualnum.mc"
include "dualnum-helpers.mc"

let num = dualnumNum
let dnum = dualnumDNum
let lift1 = dualnumLift1
let lift2 = dualnumLift2
let float2num1 = dualnumFloat2num1
let float2num2 = dualnumFloat2num2
let genEpsilon = dualnumGenEpsilon

recursive
  -- lifted negation
  let negn = lam p. lift1 (float2num1 negf) (lam x. num (negf 1.)) p
end

recursive
  -- lifted substraction
  let subn = lam p1. lam p2.
    lift2 (float2num2 subf)
                  (lam x1. lam x2. (num 1.))
                  (lam x1. lam x2. negn (num 1.))
                  p1 p2
end

recursive
  -- lifted division
  let divn = lam p1. lam p2.
    lift2 (float2num2 divf)
                  (lam x1. lam x2. divn (num 1.) x2)
                  (lam x1. lam x2. divn (negn x1) (muln x2 x2))
                  p1 p2
end

mexpr

-- negn
utest negn num1 with num (negf 1.) in
utest negn dnum010 with dnum0 (num (negf 1.)) num0 in
utest negn dnum012 with dnum0 (num (negf 1.)) (num (negf 2.)) in

-- subn
utest subn num2 num1 with num1 in
utest subn dnum020 num1 with dnum0 num1 num0 in
utest subn dnum021 num1 with dnum011 in
utest subn dnum022 dnum011 with dnum011 in

let r = subn dnum122 dnum011 in

utest dualnumPrimal e1 r
with dnum0 num1 (num (negf 1.)) in

-- divn
utest divn num4 num2 with num2 in
utest divn dnum040 num2 with dnum0 num2 num0 in
utest divn dnum044 num2 with dnum022 in

utest divn dnum012 dnum034
with dnum0 (num (divf 1. 3.)) (num (divf 2. 9.)) in

utest divn dnum012 dnum134
with dnum1 (dnum0 (num (divf 1. 3.))
                  (num (divf 2. 3.)))
           (dnum0 (num (divf (negf 4.) 9.))
                  (num (divf (negf 8.) 9.))) in

()
