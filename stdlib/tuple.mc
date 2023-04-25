/-
        This file constains utility functions that operate on tuples.
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

mexpr

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
