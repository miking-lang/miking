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

  let t1 = threadSpawn (lam. mutexLock m; condWait c m; condSignal c; mutexRelease m) in
  let t2 = threadSpawn (lam. mutexLock m; condSignal c; mutexRelease m) in
  threadJoin t1;
  threadJoin t2;

  let t1 = threadSpawn (lam. mutexLock m; condWait c m; condSignal c; mutexRelease m) in
  let t2 = threadSpawn (lam. mutexLock m; condWait c m; condSignal c; mutexRelease m) in
  let t3 = threadSpawn (lam. mutexLock m; condBroadcast c; mutexRelease m) in
  threadJoin t1;
  threadJoin t2;
  threadJoin t3;

  ()
with () in ()
