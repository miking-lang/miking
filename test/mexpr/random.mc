-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test intrinsics for random numbers

include "seq.mc"
include "set.mc"

mexpr

-- 'randIntU l u' generates a random number from a uniform distribution in the
-- interval [l,u)
-- type: Int -> Int
let randSeq = map (lam _. randIntU 2 7) (makeSeq 1000 0) in
-- With high probability all possible elements are present in the random sequence
utest setEqual eqi [2,3,4,5,6] (distinct eqi randSeq) with true in

()
