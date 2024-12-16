include "bool.mc"

/-
        This file contains utility functions that operate on tuples.
 -/

-- `tupleCmp2 cmpa cmpb` defines the product order for pairs (a, b), where:
-- (a₁, b₁) = (a₂, b₂) iff a₁ = a₂ ∧ b₁ = b₂,
-- (a₁, b₁) < (a₂, b₂) iff a₁ < a₂ ∧ b₁ ≤ b₂,
-- and where a is ordered by `cmpa` and b is ordered by `cmpb`.
let tupleCmp2
  : all a. all b. (a -> a -> Int) -> (b -> b -> Int) -> (a, b) -> (a, b) -> Int
  = lam cmpa. lam cmpb. lam x. lam y.
    match (x, y) with ((a1, b1), (a2, b2)) in
    let cmpa = cmpa a1 a2 in
    if eqi cmpa 0 then cmpb b1 b2 else cmpa

utest
  let testCmp2 = lam cmp. lam a. lam b. cmp (tupleCmp2 subi subi a b) 0 in
  utest testCmp2 eqi (0, 0) (0, 0) with true in
  utest testCmp2 lti (0, 0) (0, 1) with true in
  utest testCmp2 lti (0, 0) (1, 1) with true in
  utest testCmp2 lti (0, 1) (1, 1) with true in
  utest testCmp2 eqi (0, 1) (0, 1) with true in
  utest testCmp2 eqi (1, 0) (1, 0) with true in
  utest testCmp2 gti (1, 1) (1, 0) with true in
  utest testCmp2 gti (1, 1) (0, 1) with true in
  utest testCmp2 gti (1, 1) (0, 0) with true in
  utest testCmp2 gti (0, 1) (0, 0) with true in
  utest testCmp2 gti (1, 0) (0, 0) with true in
  utest testCmp2 eqi (1, 1) (1, 1) with true in
  ()
  with ()


-- `tupleCmp3 cmpa cmpb cmpc` defines the product order for triples
-- (a, b, c), see `tupleCmp2`.
let tupleCmp3
  : all a. all b. all c.
    (a -> a -> Int)
     -> (b -> b -> Int)
        -> (c -> c -> Int)
           -> (a, b, c) -> (a, b, c) -> Int
  = lam cmpa. lam cmpb. lam cmpc. lam x. lam y.
    match (x, y) with ((a1, b1, c1), (a2, b2, c2)) in
    let cmpa = cmpa a1 a2 in
    if eqi cmpa 0 then
      let cmpb = cmpb b1 b2 in
      if eqi cmpb 0 then cmpc c1 c2 else cmpb
    else cmpa

utest
  let testCmp3 = lam cmp. lam a. lam b. cmp (tupleCmp3 subi subi subi a b) 0 in
  utest testCmp3 eqi (0, 0, 0) (0, 0, 0) with true in
  utest testCmp3 lti (0, 0, 0) (0, 0, 1) with true in
  utest testCmp3 lti (0, 0, 0) (0, 1, 1) with true in
  utest testCmp3 lti (0, 0, 0) (1, 1, 1) with true in
  utest testCmp3 lti (0, 0, 1) (1, 1, 1) with true in
  utest testCmp3 lti (0, 1, 1) (1, 1, 1) with true in
  utest testCmp3 eqi (0, 1, 1) (0, 1, 1) with true in
  utest testCmp3 eqi (1, 0, 1) (1, 0, 1) with true in
  utest testCmp3 eqi (1, 1, 0) (1, 1, 0) with true in
  utest testCmp3 eqi (1, 0, 0) (1, 0, 0) with true in
  utest testCmp3 gti (1, 1, 1) (1, 1, 0) with true in
  utest testCmp3 gti (0, 1, 1) (0, 1, 0) with true in
  utest testCmp3 gti (1, 0, 1) (0, 1, 0) with true in
  utest testCmp3 eqi (1, 1, 1) (1, 1, 1) with true in
  ()
  with ()

let fst : all a. all b. (a, b) -> a = lam p. p.0
utest fst (1, 2) with 1
utest fst ("whatever", 2) with "whatever"

let snd : all a. all b. (a, b) -> b = lam p. p.1
utest snd (1, 2) with 2
utest snd ([1, 2, 3], "whatever") with "whatever"

-- Elementwise equality over pairs
let tupleEq2 : all a. all b. (a -> a -> Bool) -> (b -> b -> Bool) -> (a, b) -> (a, b) -> Bool
  = lam eqFst. lam eqSnd. lam lhs. lam rhs.
    and (eqFst lhs.0 rhs.0) (eqSnd lhs.1 rhs.1)

utest (tupleEq2 eqf eqi) (1.0, 1) (1.0, 1) with true
utest (tupleEq2 eqf eqi) (1.0, 1) (1.0, 12) with false
utest (tupleEq2 eqf eqi) (1.2, 1) (1.0, 12) with false

-- Elementwise equality over triples
let tupleEq3 : all a. all b. all c.
  (a -> a -> Bool) -> (b -> b -> Bool) -> (c -> c -> Bool) -> (a, b, c) -> (a, b, c) -> Bool
  = lam eqA. lam eqB. lam eqC. lam lhs. lam rhs.
    and (and (eqA lhs.0 rhs.0) (eqB lhs.1 rhs.1)) (eqC lhs.2 rhs.2)

utest
  let tupleEq3_ = tupleEq3 eqf eqi eqc in
  utest tupleEq3_ (1., 1, '1') (1., 1, '1') with true in
  utest tupleEq3_ (0., 1, '1') (1., 1, '1') with false in
  utest tupleEq3_ (1., 1, '1') (0., 1, '1') with false in
  utest tupleEq3_ (1., 0, '1') (1., 1, '1') with false in
  utest tupleEq3_ (1., 1, '1') (1., 0, '1') with false in
  utest tupleEq3_ (1., 1, '0') (1., 1, '1') with false in
  utest tupleEq3_ (1., 1, '1') (1., 1, '0') with false in
  () with ()
