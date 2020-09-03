-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines intrinsic bool operations. See the utests below each function for
-- its truth table.


-- Logical NOT
let not: Bool -> Bool -> Bool =
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


-- Logical OR
let or: Bool -> Bool -> Bool =
  lam a. lam b. if a then true else b

utest or true true with true
utest or true false with true
utest or false true with true
utest or false false with false


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
