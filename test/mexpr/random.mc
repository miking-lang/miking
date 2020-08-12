-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test intrinsics for random numbers

include "seq.mc"
include "set.mc"

mexpr

-- 'randIntU bound' generates a random number from a uniform distribution in the
-- interval [0,bound)
-- type: Int -> Int
let randSeq = map (lam _. randIntU 5) (makeSeq 1000 0) in
-- With high probability all possible elements are present in the random sequence
utest setEqual eqi [0,1,2,3,4] (distinct eqi randSeq) with true in

()
