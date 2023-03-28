include "dual-tree.mc"

type DualNum = Dual Float

let dualnumIsDualNum : DualNum -> Bool = dualIsDual
let dualnumEpsilon : DualNum -> Eps = dualEpsilon
let dualnumCreateDual
  : Eps -> DualNum -> DualNum -> DualNum = dualCreateDual (eqf 0.)
let dualnumPrimal : Eps -> DualNum -> DualNum = dualPrimal
let dualnumPrimalDeep : DualNum -> Float = dualPrimalDeep
let dualnumPertubation : Eps -> DualNum -> DualNum = dualPertubation 0.
let dualGenEpsilon : () -> Eps = dualGenEpsilon
let dualnumEq = dualEq
let dualnumToString : DualNum -> String = dualToString float2string

-----------------
-- FOR BREVITY --
-----------------

let _dnum = dualnumCreateDual
let _ltE = dualLtE

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
  let dualnumLift2
  : FloatFun2 -> DualNumFun2 -> DualNumFun2 -> DualNumFun2 =
  lam f. lam dfdx1. lam dfdx2.
    recursive let self = lam x1. lam x2.
      switch (x1, x2)
      case (Primal x1, Primal x2) then
        Primal (f x1 x2)
      case (Dual {e = e, x = x11, xp = xp11}, Primal _) then
        _dnum e (self x11 x2) (muln (dfdx1 x11 x2) xp11)
      case (Primal _, Dual {e = e, x = x22, xp = xp22}) then
        _dnum e (self x1 x22) (muln (dfdx2 x1 x22) xp22)
      case
        (Dual {e = e1, x = x11, xp = xp11},
         Dual {e = e2, x = x22, xp = xp22})
      then
        if _ltE e1 e2 then
          _dnum e2 (self x1 x22) (muln (dfdx2 x1 x22) xp22)
        else if _ltE e2 e1 then
          _dnum e1 (self x11 x2) (muln (dfdx1 x11 x2) xp11)
        else
          _dnum
            e1
            (self x11 x22)
            (addn (muln (dfdx1 x11 x22) xp11) (muln (dfdx2 x11 x22) xp22))
      end
    in self

  -- lifted addition
  let addn = lam p1. lam p2.
    dualnumLift2
      addf
      (lam. lam. (Primal 1.))
      (lam. lam. (Primal 1.))
      p1 p2

  -- lifted multiplication
  let muln = lam p1. lam p2.
    dualnumLift2
      mulf
      (lam. lam x2. x2)
      (lam x1. lam. x1)
      p1 p2
end

---------------------------------
-- LIFTING OF UNARY OPERATORS  --
---------------------------------

type DualNumFun1 = DualNum -> DualNum
type FloatFun = Float -> Float

-- lifts unary real operator to nested dual-numbers
-- f : real operator
-- dfdx : lifted derivative of f
let dualnumLift1 : FloatFun -> DualNumFun1 -> DualNumFun1 =
lam f. lam dfdx.
  recursive let self = lam x.
    switch x
    case Primal x then Primal (f x)
    case Dual {e = e, x = x, xp = xp} then
      _dnum e (self x) (muln (dfdx x) xp)
    end
  in self

mexpr

let eq = dualnumEq eqf in

let e0 = 0 in
let e1 = 1 in
let e2 = 2 in
let e3 = 3 in

let num0 = Primal 0. in
let num1 = Primal 1. in
let num2 = Primal 2. in
let num3 = Primal 3. in
let num4 = Primal 4. in
let num6 = Primal 6. in
let num8 = Primal 8. in
let dnum112 = _dnum e1 num1 num2 in
let dnum212 = _dnum e2 num3 num4 in
let dnum0 = _dnum e0 in
let dnum1 = _dnum e1 in
let dnum134 = dnum1 num3 num4 in
let dnum036 = dnum0 num3 num6 in
let dnum048 = dnum0 num4 num8 in

utest dualPrimalDeep num0 with 0. using eqf in
utest dualPrimalDeep dnum134 with 3. using eqf in
utest dualPrimalDeep (dnum1 dnum036 dnum048) with 3. using eqf in
utest dualIsDual num1 with false in
utest dualIsDual dnum112 with true in
utest dualEpsilon dnum112 with e1 in
utest dualEpsilon (_dnum e3 dnum112 dnum212) with e3 in
utest dualPrimal e1 dnum112 with num1 using eq in
utest dualnumPertubation e1 dnum112 with num2 using eq in
utest dualPrimal e2 dnum112 with dnum112 using eq in
utest dualnumPertubation e2 dnum112 with num0 using eq in

()
