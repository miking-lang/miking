-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Mutual-exclusion locks.

include "thread.mc"

type Mutex

-- 'mutexCreate ()' returns a new mutex.
external externalMutexCreate ! : () -> Mutex
let mutexCreate = lam.
  externalMutexCreate ()

-- 'mutexLock m' locks the mutex 'm'.
external externalMutexLock ! : Mutex -> ()
let mutexLock = lam m.
  externalMutexLock m

-- 'mutexTryLock m' tries to lock the mutex 'm'.
external externalMutexTryLock ! : Mutex -> Bool
let mutexTryLock = lam m.
  externalMutexTryLock m

-- 'mutexRelease m' releases the mutex 'm'.
external externalMutexRelease ! : Mutex -> ()
let mutexRelease = lam m.
  externalMutexRelease m

mexpr

let debug = false in
let debugPrint = if debug then print else lam x. () in

-- Used for debug printing, included to avoid dependency on seq.mc
let int2string = lam n.
  recursive
  let int2string_rechelper = lam n.
    if lti n 10
    then [int2char (addi n (char2int '0'))]
    else
      let d = [int2char (addi (modi n 10) (char2int '0'))] in
      concat (int2string_rechelper (divi n 10)) d
  in
  if lti n 0
  then cons '-' (int2string_rechelper (negi n))
  else int2string_rechelper n
in

utest
  let m = mutexCreate () in

  utest mutexLock m with () in
  utest mutexRelease m with () in
  utest
    let b = mutexTryLock m in
    (if b then mutexRelease m else ());
    b
  with true in

  utest
    let ts = create 10 (lam. threadSpawn (lam.
      mutexLock m;
      debugPrint (join [int2string (threadSelf ()), " has the lock!\n"]);
      mutexRelease m
      ))
    in iter threadJoin ts
  with () in

  utest
    let ts = create 10 (lam. threadSpawn (lam.
      if mutexTryLock m then
        debugPrint (join [int2string (threadSelf ()), " got the lock!\n"]);
        mutexRelease m
      else
        debugPrint (join [int2string (threadSelf ()), " did not get the lock!\n"]);
        ()
  ))
  in iter threadJoin ts
  with () in ()
with () in
()
