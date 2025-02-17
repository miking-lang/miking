-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines intrinsic bool operations. See the utests below each function for
-- its truth table.


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


-- Boolean equality
let eqBool: Bool -> Bool -> Bool =
  lam b1: Bool. lam b2: Bool.
  if b1 then b2 else (if b2 then false else true)

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
