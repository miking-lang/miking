-- This is an implementation of the tree-based dual-number API described in the
-- paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearlmutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Functions part of the API are prefixed with dualnum. Other functions are
-- internal.

include "set.mc"
include "string.mc"

type Eps = Symbol

-- Dual-numbers can be nested and are implemented as association lists. Each key
-- is the set if epsilons for a particular term in the dual number and the
-- value is the value of the term.
type DualNumTerm = (Set Symbol, Float)
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

-- generate a unique epsilon
let dualGenEpsilon : () -> Eps = gensym

-- epsilons are un-ordered
let dualLtE : Eps -> Eps -> Bool = lam. lam. true
let dualEqE : Eps -> Eps -> Bool = eqsym

-- packs a floating point number in a DualNumber
let dualnumCreatePrimal : Float -> DualNum =
lam x. [(setEmpty _cmpEpsilon, x)]

-- false if x' = 0 in x+ex'
let dualnumIsDualNum : DualNum -> Bool = any _termHasAnyEpsilon

-- x if x' = 0 otherwise x+ex'
let dualnumCreateDual : Eps -> DualNum -> DualNum -> DualNum =
lam e. lam x. lam xp. concat x (map (_termAddEpsilon e) xp)

-- e in x+ex'
let dualnumEpsilon : DualNum -> Eps =
lam n.
  match find _termHasAnyEpsilon n with Some t then
    setChooseExn (_termEpsilons t)
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
  match ts with [] then dualnumCreatePrimal 0. else ts

-- Structural equality function for dual numbers
let dualnumEq : (Float -> Float -> Bool) -> DualNum -> DualNum -> Bool =
  lam eq.
  recursive let recur = lam n1. lam n2.
    if and (dualnumIsDualNum n1) (dualnumIsDualNum n2) then
      let e1 = dualnumEpsilon n1 in
      let e2 = dualnumEpsilon n2 in
      if dualEqE e1 e2 then
        if recur (dualnumPrimal e1 n1) (dualnumPrimal e2 n2) then
          recur (dualnumPertubation e1 n1) (dualnumPertubation e2 n2)
        else false
      else false
    else if (and (not (dualnumIsDualNum n1)) (not (dualnumIsDualNum n2))) then
      eqf (dualnumPrimalDeep n1) (dualnumPrimalDeep n2)
    else false
  in recur

-- String representation of dual number
let dualnumToString : (Float -> String) -> DualNum -> String =
lam pri2str. lam n.
  strJoin "+"
    (map
      (lam t : DualNumTerm.
        match t with (es, x) then
          concat
            (setFold (lam s. lam e. join ["(", int2string (sym2hash e), ")", s]) "" es)
            (pri2str x)
        else never)
      n)

-------------
-- ALIASES --
-------------

let _num = dualnumCreatePrimal
let _dnum = dualnumCreateDual
let _ltE = dualLtE
let _isDualNum = dualnumIsDualNum
let _epsilon = dualnumEpsilon
let _primal = dualnumPrimal
let _primalDeep = dualnumPrimalDeep
let _pertubation = dualnumPertubation

----------------------------------
-- LIFTING OF BINARY OPERATORS  --
----------------------------------

type DualNumFun2 = DualNum -> DualNum -> DualNum
type FloatFun2 = Float -> Float -> Float

recursive
  -- lifts binary real operator to nested dual-numbers
  -- f : real operator
  -- dfdx1 : lifted first partial derivative of f
  -- dfdx2 : lifted second partial derivative of f
  let dualnumLift2
  : FloatFun2 -> DualNumFun2 -> DualNumFun2 -> DualNumFun2 =
  lam f. lam dfdx1. lam dfdx2.
    recursive let self = lam p1. lam p2.
      if or (_isDualNum p1)
            (_isDualNum p2)
      then
        let e = if not (_isDualNum p1) then _epsilon p2
                else if not (_isDualNum p2) then _epsilon p1
                else if _ltE (_epsilon p1) (_epsilon p2) then _epsilon p2
                else _epsilon p1
        in

        _dnum e
             (self (_primal e p1) (_primal e p2))
             (addn (muln (dfdx1 (_primal e p1) (_primal e p2))
                         (_pertubation e p1))
                   (muln (dfdx2 (_primal e p1) (_primal e p2))
                         (_pertubation e p2)))
      else
        _num (f (_primalDeep p1) (_primalDeep p2))
    in self

    -- lifted addition
    let addn = lam p1. lam p2.
      dualnumLift2
        addf
        (lam. lam. (_num 1.))
        (lam. lam. (_num 1.))
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
  recursive let self = lam p.
    if _isDualNum p then
      let e = _epsilon p in
      _dnum
        e
        (self
          (_primal e p))
          (muln
            (dfdx (_primal e p))
            (_pertubation e p))
    else
      _num (f (_primalDeep p))
  in self

mexpr

let num = dualnumCreatePrimal in
let dnum = dualnumCreateDual in

let eq = dualnumEq eqf in

let e0 = dualGenEpsilon () in
let e1 = dualGenEpsilon () in
let e2 = dualGenEpsilon () in
let e3 = dualGenEpsilon () in

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
utest dualnumEpsilon dnum112 with e1 using eqsym in
utest dualnumPrimal e1 dnum112 with num1 using eq in
utest dualnumPertubation e1 dnum112 with num2 using eq in
utest dualnumPrimal e2 dnum112 with dnum112 using eq in
utest dualnumPertubation e2 dnum112 with num0 using eq in

()
