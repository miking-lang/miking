-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Condition variables for thread synchronization.

include "thread.mc"
include "mutex.mc"

type Cond

-- 'condCreate ()' returns a new condition variable
external externalCondCreate ! : () -> Cond
let condCreate = lam.
  externalCondCreate ()

-- 'condWait c m' releases the mutex 'm' and suspends the current thread until
-- condition variable 'c' is set
external externalCondWait ! : Cond -> Mutex -> ()
let condWait = lam c. lam m.
  externalCondWait c m

-- 'condSignal c' signals the condition variable 'c', waking up ONE waiting
-- thread
external externalCondSignal ! : Cond -> ()
let condSignal = lam c.
  externalCondSignal c

-- 'condBroadcast c' signals the condition variable 'c', waking up ALL waiting
-- threads.
external externalCondBroadcast ! : Cond -> ()
let condBroadcast = lam c.
  externalCondBroadcast c

mexpr

utest
  let c = condCreate () in

  let m = mutexCreate () in

  -- Waiters register (under 'm') before 'condWait', and signallers only
  -- signal once enough waiters have registered. Since 'condWait' releases
  -- 'm' atomically, this guarantees the signal reaches threads that are
  -- actually waiting. 'ready' only guards against spurious wakeups.
  recursive let waitFor = lam c. lam m. lam ready.
    if deref ready then () else (condWait c m; waitFor c m ready)
  in
  let waiter = lam waiting. lam ready. lam.
    mutexLock m;
    modref waiting (addi (deref waiting) 1);
    waitFor c m ready;
    mutexRelease m
  in
  recursive let lockWhenWaiting = lam waiting. lam n.
    mutexLock m;
    if geqi (deref waiting) n then () else
      (mutexRelease m; threadCPURelax (); lockWhenWaiting waiting n)
  in

  -- 'condSignal' wakes a waiting thread
  let waiting = ref 0 in
  let ready = ref false in
  let t1 = threadSpawn (waiter waiting ready) in
  let t2 = threadSpawn (lam.
    lockWhenWaiting waiting 1; modref ready true; condSignal c; mutexRelease m) in
  threadJoin t1;
  threadJoin t2;

  -- 'condBroadcast' wakes *all* waiting threads
  let waiting = ref 0 in
  let ready = ref false in
  let t1 = threadSpawn (waiter waiting ready) in
  let t2 = threadSpawn (waiter waiting ready) in
  let t3 = threadSpawn (lam.
    lockWhenWaiting waiting 2; modref ready true; condBroadcast c; mutexRelease m) in
  threadJoin t1;
  threadJoin t2;
  threadJoin t3;

  ()
with () in ()
