
-- Atomic references.

type ARef a

-- 'atomicMake v' creates a new atomic reference with initial value v
external externalAtomicMake ! : all a. a -> ARef a
let atomicMake = lam v.
  externalAtomicMake v

-- 'atomicGet r' returns the current value of the atomic reference 'r'.
external externalAtomicGet ! : all a. ARef a -> a
let atomicGet = lam v.
  externalAtomicGet v

-- 'atomicExchange r v' sets the value of the atomic reference 'r' to 'v' and
-- returns the current (old) value.
external externalAtomicExchange ! : all a. ARef a -> a -> a
let atomicExchange = lam r. lam v.
  externalAtomicExchange r v

-- 'atomicCAS r seen v' sets the value of the atomic reference 'r' to 'v' iff
-- the current value is physically equal to 'seen'. Returns 'true' if the update
-- was successful, otherwise 'false'.
external externalAtomicCAS ! : all a. ARef a -> a -> a -> Bool
let atomicCAS = lam r. lam v1. lam v2.
  externalAtomicCAS r v1 v2

-- 'atomicFetchAndAdd r v' adds 'v' to the current value of the atomic reference
-- 'r' and returns the current (old) value.
external externalAtomicFetchAndAdd ! : ARef Int -> Int -> Int
let atomicFetchAndAdd = lam a. lam v.
  externalAtomicFetchAndAdd a v


-- Auxiliary (non-external) functions follow below

-- 'atomicSet r v' sets the value of the atomic reference 'r' to 'v'.
let atomicSet : all a. ARef a -> a -> () = lam r. lam v.
  atomicExchange r v; ()

-- 'atomicIncr r' increments the value of the atomic reference 'r' by 1.
let atomicIncr : ARef Int -> () = lam r.
  atomicFetchAndAdd r 1; ()

-- 'atomicDecr r' decrements the value of the atomic reference 'r' by 1.
let atomicDecr : ARef Int -> () = lam r.
  atomicFetchAndAdd r (subi 0 1); ()

mexpr

utest
  let a = atomicMake 0 in
  utest atomicCAS a 0 1 with true in
  utest atomicCAS a 1 (subi 0 1) with true in
  utest atomicCAS a 42 0 with false in
  utest atomicExchange a 0 with subi 0 1 in
  utest atomicFetchAndAdd a 2 with 0 in
  utest atomicGet a with 2 in

  let a = atomicMake [] in
  utest atomicSet a [1,2,3] with () in
  utest atomicGet a with [1,2,3] in

  let a = atomicMake 0 in
  utest atomicIncr a with () in
  utest atomicGet a with 1 in
  utest atomicDecr a with () in
  utest atomicGet a with 0 in
  ()
with () in
()
