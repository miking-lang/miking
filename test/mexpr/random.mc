-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test intrinsics for random numbers

include "seq.mc"
include "set.mc"

mexpr

-- 'randIntU l u : Int -> Int'
-- Generates a random number from a uniform distribution in the interval ['l','u').
-- Self-initializes the random generator if not already set by randSetSeed.

-- 'randSetSeed s : Int -> Unit'
-- Seeds the random generator. The same seeds generates the same sequence of numbers.

-- Generate a sequence of random numbers
let randSeq = lam lower. lam upper. lam length.
  map (lam _. randIntU lower upper) (create length (lam _. 0)) in

-- With high probability all possible elements are present in the random sequence
utest [2,3,4,5,6] with distinct eqi (randSeq 2 7 1000) using setEqual eqi in

-- The same seed should give the same sequence of numbers
let _ = randSetSeed 42 in
let randSeq1 = randSeq 123 89018 100 in
let _ = randSetSeed 42 in
let randSeq2 = randSeq 123 89018 100 in
utest randSeq1 with randSeq2 using setEqual eqi in

-- With high probability, subsequent sequence should be different
let randSeq3 = randSeq 123 89018 100 in
let neg = lam f. lam x. lam y. not (f x y) in
utest randSeq1 with randSeq3 using neg (setEqual eqi) in

()
