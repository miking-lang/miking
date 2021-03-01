
mexpr

-- Atomic operations --

-- 'atomicMake v' creates a new atomic reference with initial value v
-- : a -> ARef a
let a = atomicMake 0 in

-- 'atomicCAS r seen v' sets the value of the atomic reference 'r' to 'v' iff
-- the current value is physically equal to 'seen'. Returns 'true' if the update
-- was successful, otherwise 'false'.
-- : ARef a -> a -> a -> Bool
utest atomicCAS a 0 1 with true in
utest atomicCAS a 1 (subi 0 1) with true in
utest atomicCAS a 42 0 with false in

-- 'atomicExchange r v' sets the value of the atomic reference 'r' to 'v' and
-- returns the current (old) value.
-- : ARef a -> a -> a
utest atomicExchange a 0 with subi 0 1 in

-- 'atomicFetchAndAdd r v' adds 'v' to the current value of the atomic reference
-- 'r' and returns the current (old) value.
-- : ARef Int -> Int -> Int
utest atomicFetchAndAdd a 2 with 0 in

-- 'atomicGet r' returns the current value of the atomic reference 'r'.
-- : ARef a -> a
utest atomicGet a with 2 in

let v = 0.0 in
let a = atomicMake v in
utest atomicCAS a v 1.0 with true in


-- Threads --

let selfTID : Unit -> Int = lam _.
  -- 'threadID2int tid' converts the thread ID 'tid' to a unique integer.
  -- : Tid -> Int
  threadID2int (
    -- 'threadSelf ()' returns the ID of the current thread.
    -- : Unit -> Tid
    threadSelf ()
  )
in

-- 'threadSpawn f' spawns a new thread, which will execute 'f' in parallel with
-- the current thread.
-- : (Unit -> a) -> Thread a
let ps = create 10 (lam _. threadSpawn selfTID) in

-- 'threadJoin t' blocks until the thread 't' runs to completion. Returns the
-- value returned by running 't'.
-- [NOTE]: should be called exactly once per each spawned thread.
-- : Thread a -> a
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
    let _ = op a in
    work op (subi n 1)
in

let nIncr = 10000 in
let nDecr = 1000 in
let nSpawns = 8 in

let threads = create nSpawns (lam _. threadSpawn (lam _. work incr nIncr)) in
let _ = work decr nDecr in

let _ = iter threadJoin threads in

utest atomicGet a with subi (muli nIncr nSpawns) nDecr in


-- Locksteps using CAS --

-- use integer tids to make physical comparison in CAS possible
let me = threadID2int (threadSelf ()) in
let tid = atomicMake me in

-- Wait for friend to take a step before each step.
recursive let loop : Int -> Tid -> Unit = lam n. lam friend.
  match n with 0 then ()
  else
    match atomicCAS tid friend (threadID2int (threadSelf ())) with true then
      loop (subi n 1) friend
    else
      -- 'threadCPURelax ()' may improve performance during busy waiting.
      -- : Unit -> Unit
      let _ = threadCPURelax () in
      loop n friend
in
let n = 100 in
let t = threadSpawn (lam _. loop n me) in
let _ = loop n (threadID2int (threadGetID t)) in
-- Does not loop forever = the test has passed!
let _ = threadJoin t in


-- Wait, notify, and critical section --
let inCriticalSection = atomicMake false in
let afterWait = atomicMake false in

let t = threadSpawn (lam _.
  -- 'threadCriticalSection f' runs 'f' as a critical section in the current
  -- thread 't'. A critical section means that 'f' may include a call to
  -- 'threadWait' (see below), and that any call to 'threadNotify t' (see below)
  -- during the critical section blocks until the critical section runs to
  -- completion. A critical section is either notified, or not notified. It is
  -- initially not notified, and becomes notified after a call to 'threadNotify
  -- t'. Once it is notified, it stays notified.
  -- : (Unit -> a) -> a
  threadCriticalSection (
    lam _.
      let _ = atomicExchange inCriticalSection true in
      -- 'threadWait ()' must be called from within a critical section. Blocks
      -- until the critical section becomes notified.
      -- [NOTE] two calls to 'threadWait' within the same critical section is
      -- meaningless, as the second one will always immediately return.
      let _ = threadWait () in
      -- Sleep for a while, to make it clear that the other thread waits for the
      -- critical section to finish.
      let _ = sleepMs 1000 in
      atomicExchange afterWait true
  )
) in

recursive let waitForFlag : ARef a -> Unit = lam flag.
  match atomicGet flag with true then ()
  else waitForFlag flag
in
let _ = waitForFlag inCriticalSection in

-- When inCriticalSection is set, we know that t is in the critical section, so
-- threadNotify will unblock the threadWait.

-- 'threadNotify tid' notifies any in-progress critical section in the thread
-- with ID 'tid'. Blocks until any in-progress critical section in that thread
-- runs to completion.
let _ = threadNotify (threadGetID t) in

-- Since threadNotify blocks until the critical section exits, afterWait must be
-- set to true now.
utest atomicGet afterWait with true in

-- Don't forget to clean up!
let _ = threadJoin t in

()
