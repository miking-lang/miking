-- This is an implementation of the tree-based dual-number API described in the
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearlmutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Functions part of the API are prefixed with dualnum. Other functions are
-- internal.

include "set.mc"
include "string.mc"

type Eps = Symb

-- Dual-numbers can be nested and are implemented as association lists. Each key
-- is the set if epsilons for a particular term in the dual number and the
-- value is the value of the term.
type DualNumTerm = (Set Symb, Float)
type DualNum = [DualNumTerm]

let _cmpEpsilon = lam e1 : Eps. lam e2 : Eps. subi (sym2hash e1) (sym2hash e2)
let _termEpsilons = lam t : DualNumTerm. t.0
let _termValue = lam t : DualNumTerm. t.1
let _termAddEpsilon = lam e : Eps. lam t : DualNumTerm.
  (setInsert e (_termEpsilons t), _termValue t)
let _termRemoveEpsilon = lam e : Eps. lam t : DualNumTerm.
  (setRemove e (_termEpsilons t), _termValue t)
let _termHasAnyEpsilon = lam t : DualNumTerm. not (setIsEmpty (_termEpsilons t))
let _termHasEpsilon = lam e. lam t. setMem e (_termEpsilons t)

-- epsilons are un-ordered
let dualnumLtE : Eps -> Eps -> Bool = lam. lam. true

-- packs a floating point number in a DualNumber
let dualnumNum : Float -> DualNum =
lam x. [(setEmpty _cmpEpsilon, x)]

-- false if x' = 0 in x+ex'
let dualnumIsDualNum : DualNum -> Bool = any _termHasAnyEpsilon

-- x if x' = 0 otherwise x+ex'
let dualnumDNum : Eps -> DualNum -> DualNum -> DualNum =
lam e. lam x. lam xp. concat x (map (_termAddEpsilon e) xp)

-- e in x+ex'
let dualnumEpsilon : DualNum -> Eps =
lam n.
  match find _termHasAnyEpsilon n with Some t then
    setChooseWithExn (_termEpsilons t)
  else error "Operand not a dual number"

-- x in x+ex'
let dualnumPrimal : Eps -> DualNum -> DualNum =
lam e. filter (lam t. not (_termHasEpsilon e t))

-- x in x+e1(x+e2(x+e3(...)))
let dualnumPrimalDeep : DualNum -> Float =
lam n.
  -- NOTE(oerikss, 2021-10-11): Exactly one element in the association list
  -- fulfills this predicate by construction.
  let p = lam t. not (_termHasAnyEpsilon t) in
  match find p n with Some (_, x) then x else error "Impossible"

-- x' in x+ex'
let dualnumPertubation : Eps -> DualNum -> DualNum =
lam e. lam n.
  let ts = map (_termRemoveEpsilon e) (filter (_termHasEpsilon e) n) in
  match ts with [] then dualnumNum 0. else ts

-- generate a unique epsilon
let dualnumGenEpsilon : Unit -> Eps = gensym

-- Equality function for epsilon
let dualnumEqEpsilon : Eps -> Eps -> Bool = eqsym

-- Structural equality function for dual numbers
let dualnumEq : (a -> a -> Bool) -> DualNum -> DualNum -> Bool =
  lam eq.
  recursive let recur = lam n1. lam n2.
    if and (dualnumIsDualNum n1) (dualnumIsDualNum n2) then
      let e1 = dualnumEpsilon n1 in
      let e2 = dualnumEpsilon n2 in
      if dualnumEqEpsilon e1 e2 then
        if recur (dualnumPrimal e1 n1) (dualnumPrimal e2 n2) then
          recur (dualnumPertubation e1 n1) (dualnumPertubation e2 n2)
        else false
      else false
    else if (and (not (dualnumIsDualNum n1)) (not (dualnumIsDualNum n2))) then
      eqf (dualnumPrimalDeep n1) (dualnumPrimalDeep n2)
    else false
  in recur

-- String representation of dual number
let dualnumToString : DualNum -> String =
lam n.
  strJoin "+"
    (map
      (lam t : DualNumTerm.
        match t with (es, x) then
          join
            (snoc
              (map (lam e. join ["(", int2string (sym2hash e), ")"]) es)
              (float2string x))
        else never)
      n)

mexpr

let num = dualnumNum in
let dnum = dualnumDNum in

let eq = dualnumEq eqf in

let e0 = dualnumGenEpsilon () in
let e1 = dualnumGenEpsilon () in
let e2 = dualnumGenEpsilon () in
let e3 = dualnumGenEpsilon () in

let num0 = num 0. in
let num1 = num 1. in
let num2 = num 2. in
let num3 = num 3. in
let num4 = num 4. in
let num6 = num 6. in
let num8 = num 8. in
let dnum112 = dnum e1 num1 num2 in
let dnum212 = dnum e2 num3 num4 in
let dnum0 = dnum e0 in
let dnum1 = dnum e1 in
let dnum134 = dnum1 num3 num4 in
let dnum036 = dnum0 num3 num6 in
let dnum048 = dnum0 num4 num8 in

utest dualnumPrimalDeep num0 with 0. using eqf in
utest dualnumPrimalDeep dnum134 with 3. using eqf in
utest dualnumPrimalDeep (dnum1 dnum036 dnum048) with 3. using eqf in
utest dualnumIsDualNum num1 with false in
utest dualnumIsDualNum dnum112 with true in
utest dualnumEpsilon dnum112 with e1 in
utest dualnumPrimal e1 dnum112 with num1 using eq in
utest dualnumPertubation e1 dnum112 with num2 using eq in
utest dualnumPrimal e2 dnum112 with dnum112 using eq in
utest dualnumPertubation e2 dnum112 with num0 using eq in

()
