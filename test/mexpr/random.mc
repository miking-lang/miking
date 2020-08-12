-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test intrinsics for random numbers

include "seq.mc"
include "set.mc"

mexpr

-- randIntU l u : Int -> Int
-- Generates a random number from a uniform distribution in the interval [l,u).
-- Self-initializes the random generator if not already set by randSetSeed.

-- randSetSeed s : Int -> ()
-- Seeds the random generator. The same seeds generates the same sequence of numbers.

-- Generate a sequence of random numbers
let randSeq = lam lower. lam upper. lam length.
  map (lam _. randIntU lower upper) (makeSeq length 0) in

-- With high probability all possible elements are present in the random sequence
utest setEqual eqi [2,3,4,5,6] (distinct eqi (randSeq 2 7 1000)) with true in

-- The same seed should give the same sequence of numbers
let _ = randSetSeed 42 in
let randSeq1 = randSeq 123 89018 100 in
let _ = randSetSeed 42 in
let randSeq2 = randSeq 123 89018 100 in
utest setEqual eqi randSeq1 randSeq2 with true in

-- With high probability, subsequent sequence should be different
let randSeq3 = randSeq 123 89018 100 in
utest setEqual eqi randSeq1 randSeq3 with false in

()
