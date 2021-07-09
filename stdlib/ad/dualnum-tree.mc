-- This is an implementation of the tree-based dual-number API described in the
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearlmutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Functions part of the API are prefixed with dualnum. Other functions are
-- internal.

include "string.mc"

type Eps = Int

-- Dual-numbers can be nested and are implemented as explicit trees.
type DualNum
con DualNum : {e : Int, x : DualNum, xp : DualNum} -> DualNum
con Num : Float -> DualNum -- we separate out generic real numbers

-- epsilons are ordered
let dualnumLtE : Eps -> Eps -> Bool = lti

-- make a generic real number
let dualnumNum : a -> DualNum =
lam f. Num f

-- unpack real number
let dualnumUnpackNum : DualNum -> Float =
lam n. match n with Num f then f
       else error "Can only unpack numbers"

-- lift unary real operator to number operator
let dualnumFloat2num1 : (Float -> Float) -> (DualNum -> DualNum) =
lam op. (lam x. dualnumNum (op (dualnumUnpackNum x)))

-- lift unary generic real operator to number operator
let dualnumFloat2num2
  : (Float -> Float -> Float) -> (DualNum -> DualNum -> DualNum) =
lam op. (lam x1. lam x2. dualnumNum (op
                                      (dualnumUnpackNum x1)
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

-- Equality function for epsilon
let dualnumEqEpsilon : Eps -> Eps -> Bool = eqi

-- Structural equality function for dual numbers
let dualnumEq : (a -> a -> Bool) -> DualNum -> DualNum -> Bool =
  lam eq.
  recursive let recur = lam n1. lam n2.
    let nn = (n1, n2) in
    match nn with (Num r1, Num r2) then eq r1 r2
    else match nn with (DualNum _, DualNum _) then
      let e1 = dualnumEpsilon n1 in
      let e2 = dualnumEpsilon n2 in
      if dualnumEqEpsilon e1 e2 then
        if recur (dualnumPrimal e1 n1) (dualnumPrimal e2 n2) then
          recur (dualnumPertubation e1 n1) (dualnumPertubation e2 n2)
        else false
      else false
    else false
  in recur

-- String representation of dual number
let dualnumToString : DualNum -> String =
lam n.
  let wrapInParen = lam n. lam str.
    if dualnumIsDualNum n then join ["(", str, ")"] else str
  in
  recursive let recur = lam n.
    match n with Num r then float2string r
    else match n with DualNum {e = e, x = x, xp = xp} then
      join [
        wrapInParen x (recur x),
        " + e",
        int2string e,
        " ",
        wrapInParen xp (recur xp)
      ]
    else never
  in recur n

mexpr

let eq = dualnumEq eqf in

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
utest dualnumPrimal e1 dnum112 with num1 using eq in
utest dualnumPertubation e1 dnum112 with num2 using eq in
utest dualnumPrimal e2 dnum112 with dnum112 using eq in
utest dualnumPertubation e2 dnum112 with num0 using eq in

()
