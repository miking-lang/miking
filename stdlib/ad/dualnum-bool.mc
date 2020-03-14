-- This is an implementation of functions lifting compares over reals to nested
-- dual-numbers described in the paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.



include "dualnum.mc"

let num = dualnumMkNum
let dnum = dualnumMkDualNum

let epsilon = dualnumEpsilon
let primal = dualnumPrimal
let primalDeep = dualnumPrimalDeep
let unpack = dualnumUnpackNum
let genEpsilon = dualnumGenEpsilon

type FloatCmp2 = Float -> Float -> Bool

-- lifts compare function to nested dual-numbers. The compare functions is
-- applied to x in x+(en)x', where x and x' are reals, e.g. x+(en)x' is the
-- deepest element in the nested dual-number y+(e1)y'.
-- cmp : real compare function
let dualnumLiftBoolFun2 : FloatCmp2 -> (DualNum -> DualNum -> Bool) =
lam cmp.
  let self = lam p1. lam p2.
    cmp (unpack (primalDeep p1)) (unpack (primalDeep p2))
  in self

let eqn = dualnumLiftBoolFun2 eqf -- lifted ==
let neqn = dualnumLiftBoolFun2 neqf -- lifted !=
let ltn = dualnumLiftBoolFun2 ltf -- lifted <
let leqn = dualnumLiftBoolFun2 leqf -- lifted <=
let gtn = dualnumLiftBoolFun2 gtf -- lifted >
let geqn = dualnumLiftBoolFun2 geqf -- lifted >=

mexpr

let e1 = genEpsilon () in
let e2 = genEpsilon () in

let num1 = num 1. in
let num2 = num 2. in
let num3 = num 3. in
let dnum112 = dnum e1 num1 num2 in

utest eqn num1 num1 with true in
utest eqn num1 num2 with false in
utest eqn (dnum e2 dnum112 num3) num1 with true in
utest eqn (dnum e2 dnum112 num3) num2 with false in

utest neqn num1 num1 with false in
utest neqn num1 num2 with true in
utest neqn (dnum e2 dnum112 num3) num1 with false in
utest neqn (dnum e2 dnum112 num3) num2 with true in

utest ltn num1 num1 with false in
utest ltn num1 num2 with true in
utest ltn num2 num1 with false in
utest ltn (dnum e2 dnum112 num3) num1 with false in
utest ltn (dnum e2 dnum112 num3) num2 with true in
utest ltn num2 (dnum e2 dnum112 num3) with false in

utest leqn num1 num1 with true in
utest leqn num1 num2 with true in
utest leqn num2 num1 with false in
utest leqn (dnum e2 dnum112 num3) num1 with true in
utest leqn (dnum e2 dnum112 num3) num2 with true in
utest leqn num2 (dnum e2 dnum112 num3) with false in

utest gtn num1 num1 with false in
utest gtn num1 num2 with false in
utest gtn num2 num1 with true in
utest gtn (dnum e2 dnum112 num3) num1 with false in
utest gtn (dnum e2 dnum112 num3) num2 with false in
utest gtn num2 (dnum e2 dnum112 num3) with true in

utest geqn num1 num1 with true in
utest geqn num1 num2 with false in
utest geqn num2 num1 with true in
utest geqn (dnum e2 dnum112 num3) num1 with true in
utest geqn (dnum e2 dnum112 num3) num2 with false in
utest geqn num2 (dnum e2 dnum112 num3) with true in

()
