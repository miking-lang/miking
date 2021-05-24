-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the atomic intrinsics.

-- 'atomicSet r v' sets the value of the atomic reference 'r' to 'v'.
let atomicSet : ARef a -> a -> Unit = lam r. lam v.
  atomicExchange r v; ()

-- 'atomicIncr r' increments the value of the atomic reference 'r' by 1.
let atomicIncr : ARef -> Unit = lam r.
  atomicFetchAndAdd r 1; ()

-- 'atomicDecr r' decrements the value of the atomic reference 'r' by 1.
let atomicDecr : ARef -> Unit = lam r.
  atomicFetchAndAdd r (subi 0 1); ()

mexpr

let a = atomicMake [] in

utest atomicSet a [1,2,3] with () in
utest atomicGet a with [1,2,3] in

let a = atomicMake 0 in

utest atomicIncr a with () in
utest atomicGet a with 1 in

utest atomicDecr a with () in
utest atomicGet a with 0 in

()
