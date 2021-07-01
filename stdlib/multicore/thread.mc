include "atomic.mc"
include "seq.mc"

-- Multicore threads.

-- 'threadSpawn f' spawns a new thread, which will execute 'f' in parallel with
-- the current thread.
external externalThreadSpawn ! : (Unit -> a) -> Thread
let threadSpawn = lam f.
  externalThreadSpawn f

-- 'threadJoin t' blocks until the thread 't' runs to completion. Returns the
-- value returned by running 't'.
-- [NOTE]: should be called exactly once per each spawned thread.
external externalThreadJoin ! : Thread -> a
let threadJoin = lam t.
  externalThreadJoin t

-- 'threadGetID t' returns the ID of the thread 't'
external externalThreadGetID ! : Thread -> Int
let threadGetID = lam t.
  externalThreadGetID t

-- 'threadSelf ()' returns the ID of the current thread
external externalThreadSelf ! : Unit -> Int
let threadSelf = lam u.
  externalThreadSelf u

-- 'threadCPURelax ()' may improve performance during busy waiting.
external externalThreadCPURelax ! : Unit -> Unit
let threadCPURelax = lam u.
  externalThreadCPURelax u

mexpr

-- Threads --

let ps = create 10 (lam. threadSpawn (lam. threadSelf ())) in

let tids = map threadJoin ps in

-- We expect the thread IDs to be unique.
utest length (distinct eqi tids) with length tids in


-- Threaded atomic operations --
-- increase/decrease an atomic in different threads
let incr = lam a. atomicFetchAndAdd a 1 in
let decr = lam a. atomicFetchAndAdd a (subi 0 1) in

let a = atomicMake 0 in
recursive let work : (ARef a -> Unit) -> Int -> Unit = lam op. lam n.
  match n with 0 then ()
  else
    op a;
    work op (subi n 1)
in

let nIncr = 10000 in
let nDecr = 1000 in
let nSpawns = 8 in

let threads = create nSpawns (lam. threadSpawn (lam. work incr nIncr)) in
work decr nDecr;

iter threadJoin threads;

utest atomicGet a with subi (muli nIncr nSpawns) nDecr in


-- Locksteps using CAS --

-- use integer tids to make physical comparison in CAS possible
let me = threadSelf () in
let tid = atomicMake me in

-- Wait for friend to take a step before each step.
recursive let loop : Int -> Tid -> Unit = lam n. lam friend.
  match n with 0 then ()
  else
    match atomicCAS tid friend (threadSelf ()) with true then
      loop (subi n 1) friend
    else
      threadCPURelax ();
      loop n friend
in
let n = 100 in
let t = threadSpawn (lam. loop n me) in
loop n (threadGetID t);
-- Does not loop forever = the test has passed!
threadJoin t;

()
