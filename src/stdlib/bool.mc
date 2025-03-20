-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines intrinsic bool operations. See the utests below each function for
-- its truth table.



-- ┌────────────────────┐
-- │ Pure Boolean Logic │
-- └────────────────────┘

-- Logical NOT
let not: Bool -> Bool =
  lam a. if a then false else true

utest not true with false
utest not false with true

-- Logical AND
let and: Bool -> Bool -> Bool =
  lam a. lam b. if a then b else false

utest and true true with true
utest and true false with false
utest and false true with false
utest and false false with false

-- Logical AND of sequence
let allb : [Bool] -> Bool = foldl and true

utest allb [true, true, true] with true
utest allb [false, true, true] with false
utest allb [true] with true
utest allb [false] with false
utest allb [] with true

-- Logical OR
let or: Bool -> Bool -> Bool =
  lam a. lam b. if a then true else b

utest or true true with true
utest or true false with true
utest or false true with true
utest or false false with false

-- Logical OR of sequence
let someb : [Bool] -> Bool = foldl or false

utest someb [false, false, false] with false
utest someb [false, true, true] with true
utest someb [true] with true
utest someb [false] with false
utest someb [] with false

-- Logical XOR
let xor: Bool -> Bool -> Bool =
  lam a. lam b. if a then not b else b

utest xor true true with false
utest xor true false with true
utest xor false true with true
utest xor false false with false


-- Logical XNOR (a.k.a. equivalence between boolean variables)
let xnor: Bool -> Bool -> Bool =
  lam a. lam b. not (xor a b)

utest xnor true true with true
utest xnor true false with false
utest xnor false true with false
utest xnor false false with true


-- ┌─────────────────────────────┐
-- │ Short-circuit Boolean Logic │
-- └─────────────────────────────┘

-- Short-circuited Logical AND
let scand: (() -> Bool) -> (() -> Bool) -> Bool =
  lam a. lam b. if a () then b () else false

utest scand (lam. true) (lam. true) with true
utest scand (lam. true) (lam. false) with false
utest scand (lam. false) (lam. true) with false
utest scand (lam. false) (lam. false) with false

utest
  let r = ref 0 in
  scand (lam. true) (lam. modref r 1; true);
  deref r
with 1

utest
  let r = ref 0 in
  scand (lam. false) (lam. modref r 1; true);
  deref r
with 0

-- Short-circuited Logical AND of sequence
let scallb : [() -> Bool] -> Bool =
  foldl (lam acc. lam p. scand (lam. acc) p) true

utest scallb [lam. true, lam. true, lam. true] with true
utest scallb [lam. false, lam. true, lam. true] with false
utest scallb [lam. true] with true
utest scallb [lam. false] with false
utest scallb [] with true

-- Short-circuited Logical OR
let scor: (() -> Bool) -> (() -> Bool) -> Bool =
  lam a. lam b. if a () then true else b ()

utest scor (lam. true) (lam. true) with true
utest scor (lam. true) (lam. false) with true
utest scor (lam. false) (lam. true) with true
utest scor (lam. false) (lam. false) with false

utest
  let r = ref 0 in
  scor (lam. true) (lam. modref r 1; true);
  deref r
with 0

utest
  let r = ref 0 in
  scor (lam. false) (lam. modref r 1; true);
  deref r
with 1

-- Short-circuited Logical OR of sequence
let scsomeb : [(() -> Bool)] -> Bool =
  foldl (lam acc. lam p. scor (lam. acc) p) false

utest scsomeb [lam. false, lam. false, lam. false] with false
utest scsomeb [lam. false, lam. true, lam. true] with true
utest scsomeb [lam. true] with true
utest scsomeb [lam. false] with false
utest scsomeb [] with false


-- ┌───────────────────────────┐
-- │ Boolean Utility Functions │
-- └───────────────────────────┘

-- Boolean equality
let eqBool: Bool -> Bool -> Bool = xnor

utest eqBool false false with true
utest eqBool false true  with false
utest eqBool true  false with false
utest eqBool true  true  with true


-- Boolean comparison
let cmpBool: Bool -> Bool -> Int =
  lam b1: Bool. lam b2: Bool.
  if b1 then if b2 then 0 else 1
  else if b2 then negi 1 else 0

utest cmpBool false false with 0
utest cmpBool false true  with negi 1
utest cmpBool true  false with 1
utest cmpBool true  true  with 0


-- Boolean to string
let bool2string: Bool -> String = lam b.
  if b then "true" else "false"

utest bool2string true with "true"
utest bool2string false with "false"

-- String to Boolean
let string2bool: String -> Bool = lam s.
  match s with "true" then true
  else match s with "false" then false
  else error (concat "Cannot convert string " (concat s " to Bool."))

utest string2bool "true" with true
utest string2bool "false" with false
