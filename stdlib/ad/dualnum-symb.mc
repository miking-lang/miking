-- This is an implementation of the symbol-based dual-number API described in
-- the paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearlmutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.

-- Functions part of the API are prefixed with dualnum. Other functions are
-- internal.



include "seq.mc"

type Eps = Sym

-- Dual-numbers can be nested and are implemented as association lists indexed
-- by the coefficients (consisting of products of epsilons) resulting from
-- multiplying out all factors.
type DualNum
type Term = ([Eps], Float)
con DualNum : [Term] -> DualNum
con Num : Float -> DualNum -- we separate out real numbers

let memq = lam s. any (lam x. eqs x s)
let some = any

let findIf = lam p. lam seq.
  match find p seq with Some x then x
  else error "no such element"

let removeIf = lam p. filter (lam x. not (p x))

let removeq : Eps -> [Eps] =
lam s. lam ss. filter (lam x. not (eqs x s)) ss

let terms : DualNum -> [Term] =
lam p. match p with Num f then [([], f)] else
       match p with DualNum ts then ts else
       never

let terms2dualNum : [Term] -> DualNum =
lam ts. if null ts then Num 0.
        else if and (null (tail ts))
                    (null (head ts).0)
        then Num ((head ts).1)
        else DualNum ts

-- epsilons are unordered
let dualnumLtE : Eps -> Eps -> Bool = lam l. lam r. true

-- make a real number
let dualnumNum : Float -> DualNum =
lam f. Num f

-- unpack float representation of a real number
let dualnumUnpackNum : DualNum -> Float =
lam p. match p with Num f then f
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
lam p. some (lam t. not (null t.0)) (terms p)

-- x if x' = 0 otherwise x+ex'
let dualnumDNum : Eps -> DualNum -> DualNum -> DualNum =
lam e. lam x. lam xp.
  terms2dualNum (concat (terms x)
                           (map (lam t. (cons e t.0, t.1)) (terms xp)))

-- e in x+ex'
let dualnumEpsilon : DualNum -> Eps =
lam p. head (findIf (lam t. not (null t.0)) (terms p)).0

-- x in x+ex'
let dualnumPrimal : Eps -> DualNum -> DualNum =
lam e. lam p. terms2dualNum (removeIf (lam t. memq e t.0) (terms p))

-- x' in x+ex'
let dualnumPertubation : Eps -> DualNum -> DualNum =
lam e. lam p.
  terms2dualNum
  (map (lam t. (removeq e t.0, t.1))
       (removeIf (lam t. not (memq e t.0)) (terms p)))

-- generate unique epsilon
let dualnumGenEpsilon : Unit -> Eps = lam _. gensym ()

mexpr

let e1 = dualnumGenEpsilon () in
let e2 = dualnumGenEpsilon () in
let e3 = dualnumGenEpsilon () in

let num0 = dualnumNum 0. in
let num1 = dualnumNum 1. in
let num2 = dualnumNum 2. in
let num3 = dualnumNum 3. in
let num4 = dualnumNum 4. in
let dnum111 = dualnumDNum e1 num1 num1 in
let dnum112 = dualnumDNum e1 num1 num2 in
let dnum212 = dualnumDNum e2 num3 num4 in

utest dualnumIsDualNum num1 with false in
utest dualnumIsDualNum dnum112 with true in
utest dualnumEpsilon dnum112 with e1 in
utest dualnumEpsilon (dualnumDNum e3 dnum112 dnum212) with e1 in
utest dualnumPrimal e1 dnum112 with num1 in
utest dualnumPertubation e1 dnum112 with num2 in
utest dualnumPrimal e2 dnum112 with dnum112 in
utest dualnumPertubation e2 dnum112 with num0 in

()
