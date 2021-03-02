-- This is an implementation of functions lifting operators over reals to nested
-- dual-numbers described in the paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Public functions are prefixed with dualnum. Other functions are internal.



include "dualnum-tree.mc"
include "dualnum-helpers.mc"
include "string.mc"

let num = dualnumNum
let dnum = dualnumDNum

let ltE = dualnumLtE
let isDualNum = dualnumIsDualNum
let epsilon = dualnumEpsilon
let primal = dualnumPrimal
let pertubation = dualnumPertubation
let unpack = dualnumUnpackNum
let float2num2 = dualnumFloat2num2

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
      if or (isDualNum p1)
            (isDualNum p2)
      then
        let e = if not (isDualNum p1) then epsilon p2
                else if not (isDualNum p2) then epsilon p1
                else if ltE (epsilon p1) (epsilon p2) then epsilon p2
                else epsilon p1
        in

        dnum e
             (self (primal e p1) (primal e p2))
             (addn (muln (dfdx1 (primal e p1) (primal e p2))
                         (pertubation e p1))
                   (muln (dfdx2 (primal e p1) (primal e p2))
                         (pertubation e p2)))
      else
        f p1 p2
    in self

    -- lifted addition
    let addn = lam p1. lam p2.
      dualnumLift2 (float2num2 addf)
                       (lam x1. lam x2. (num 1.))
                       (lam x1. lam x2. (num 1.))
                       p1 p2

    -- lifted multiplication
    let muln = lam p1. lam p2.
      dualnumLift2 (float2num2 mulf)
                       (lam x1. lam x2. x2)
                       (lam x1. lam x2. x1)
                       p1 p2
end

type FloatFun1 = Float -> Float
type DualNumFun1 = DualNum -> DualNum

-- lifts unary real operator to nested dual-numbers
-- f : real operator
-- dfdx : lifted derivative of f
let dualnumLift1 : DualNumFun1 -> DualNumFun1 -> DualNumFun1 =
lam f. lam dfdx.
  recursive let self = lam p.
    if isDualNum p then
      let e = epsilon p in
      dnum e
           (self (primal e p))
                 (muln (dfdx (primal e p))
                       (pertubation e p))
    else
      f p
  in self

-- Real part of arbritrary nested dual number p.
recursive
let dualnumPrimalDeep : DualNum -> DualNum =
lam p.
   if not (isDualNum p) then p
   else dualnumPrimalDeep (primal (epsilon p) p)
end

-- Real part of arbritrary nested dual number p as string.
let dualnum2string : DualNum -> String =
lam p. float2string (unpack (dualnumPrimalDeep p))

mexpr

-- addn
utest addn num1 num2 with num3 in
utest addn dnum010 num2 with dnum0 num3 num0 in
utest addn dnum011 num2 with dnum031 in
utest addn dnum011 dnum011 with dnum022 in
utest addn dnum011 dnum111 with dnum1 dnum021 num1 in

-- muln
utest muln num1 num2 with num2 in
utest muln dnum010 num2 with dnum0 num2 num0 in
utest muln dnum011 num2 with dnum022 in
utest muln dnum012 dnum034 with dnum0 num3 num10 in
utest muln dnum012 dnum134 with dnum1 dnum036 dnum048 in

-- primalDeep
utest dualnumPrimalDeep num0 with num0 in
utest dualnumPrimalDeep dnum134 with num3 in
utest dualnumPrimalDeep (dnum1 dnum036 dnum048) with num3 in

-- dualnum2string
utest dualnum2string num0 with "0.0" in
utest dualnum2string dnum134 with "3.0e+0" in
utest dualnum2string (dnum1 dnum036 dnum048) with "3.0e+0" in

()
