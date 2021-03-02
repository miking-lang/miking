-- This is an implementation of the tree-based dual-number API described in the
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearlmutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Functions part of the API are prefixed with dualnum. Other functions are
-- internal.



type Eps = Int

-- Dual-numbers can be nested and are implemented as explicit trees.
type DualNum
con DualNum : {e : Int, x : DualNum, xp : DualNum} -> DualNum
con Num : Float -> DualNum -- we separate out real numbers

-- epsilons are ordered
let dualnumLtE : Eps -> Eps -> Bool = lti

-- make a Real number
let dualnumNum : Float -> DualNum =
lam f. Num f

-- unpack float representation of a real number
let dualnumUnpackNum : DualNum -> Float =
lam n. match n with Num f then f
       else error "Can only unpack numbers"

-- lift unary real operator to number operator
let dualnumFloat2num1 : (Float -> Float) -> (DualNum -> DualNum) =
lam op. (lam x. dualnumNum (op (dualnumUnpackNum x)))

-- lift unary real operator to number operator
let dualnumFloat2num2 : (Float -> Float -> Float) -> (DualNum -> DualNum -> DualNum) =
lam op. (lam x1. lam x2. dualnumNum (op (dualnumUnpackNum x1)
                                    (dualnumUnpackNum x2)))

-- false if x' = 0 in x+ex'
let dualnumIsDualNum : DualNum -> Bool =
lam n. match n with Num _ then false else
       match n with DualNum _ then true else
       never

-- x if x' = 0 otherwise x+ex'
let dualnumDNum : Eps -> DualNum -> DualNum -> DualNum =
lam e. lam x. lam xp.
  match xp with Num f then
    if eqf f 0. then x else DualNum {e = e, x = x, xp = xp}
  else DualNum {e = e, x = x, xp = xp}

-- e in x+ex'
let dualnumEpsilon : DualNum -> Eps =
lam n. match n with DualNum dn then dn.e
       else error "Operand not a dual number"

-- x in x+ex'
let dualnumPrimal : Eps -> DualNum -> DualNum =
lam e. lam n.
  match n with Num _ then n else
  match n with DualNum dn then
    if dualnumLtE dn.e e then n else dn.x
  else never

-- x' in x+ex'
let dualnumPertubation : Eps -> DualNum -> DualNum =
lam e. lam n.
  match n with Num _ then Num 0. else
  match n with DualNum dn then
    if dualnumLtE dn.e e then Num 0. else dn.xp
  else never

-- generate unique epsilon e1 that fulfills the invariant e1 > e for all
-- previously generated epsilons e.
let e = ref 0
let dualnumGenEpsilon : Unit -> Eps =
lam. modref e (addi (deref e) 1); deref e

mexpr

let e1 = 1 in
let e2 = 2 in
let e3 = 3 in

let num0 = dualnumNum 0. in
let num1 = dualnumNum 1. in
let num2 = dualnumNum 2. in
let num3 = dualnumNum 3. in
let num4 = dualnumNum 4. in
let dnum112 = dualnumDNum e1 num1 num2 in
let dnum212 = dualnumDNum e2 num3 num4 in

utest dualnumIsDualNum num1 with false in
utest dualnumIsDualNum dnum112 with true in
utest dualnumEpsilon dnum112 with e1 in
utest dualnumEpsilon (dualnumDNum e3 dnum112 dnum212) with e3 in
utest dualnumPrimal e1 dnum112 with num1 in
utest dualnumPertubation e1 dnum112 with num2 in
utest dualnumPrimal e2 dnum112 with dnum112 in
utest dualnumPertubation e2 dnum112 with num0 in

()
