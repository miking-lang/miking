-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test intrinsics for random numbers

include "seq.mc"
include "eqset.mc"

mexpr

-- 'randIntU l u : Int -> Int'
-- Generates a random number from a uniform distribution in the interval ['l','u').
-- Self-initializes the random generator if not already set by randSetSeed.

-- 'randSetSeed s : Int -> ()'
-- Seeds the random generator. The same seeds generates the same sequence of numbers.

-- Generate a sequence of random numbers
let randSeq = lam lower. lam upper. lam length.
  map (lam. randIntU lower upper) (create length (lam. 0)) in

-- With high probability all possible elements are present in the random sequence
utest [2,3,4,5,6] with distinct eqi (randSeq 2 7 1000) using eqsetEqual eqi in

-- The same seed should give the same sequence of numbers
randSetSeed 42;
let randSeq1 = randSeq 123 89018 100 in
randSetSeed 42;
let randSeq2 = randSeq 123 89018 100 in
utest randSeq1 with randSeq2 using eqsetEqual eqi in

-- With high probability, subsequent sequence should be different
let randSeq3 = randSeq 123 89018 100 in
let neg = lam f. lam x. lam y. not (f x y) in
utest randSeq1 with randSeq3 using neg (eqsetEqual eqi) in

()
