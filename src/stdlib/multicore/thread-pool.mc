-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines a thread pool for parallel execution of tasks.

include "thread.mc"
include "atomic.mc"
include "channel.mc"
include "map.mc"

type Async a = ARef (Option a)

type ThreadPoolTask a
con Task : all a. {task : () -> a, result : Async a} -> ThreadPoolTask a
con Quit : all a. () -> ThreadPoolTask a

type ThreadPool a = {threads : [Thread ()], queue : Channel (ThreadPoolTask a)}

-- Helper function for waiting for and executing tasks.
recursive let _wait = lam chan.
  let msg = channelRecv chan in
  match msg with Task {task = f, result = r} then
    atomicSet r (Some (f ()));
    _wait chan
  else match msg with Quit _ then ()
  else never
end

-- 'threadPoolCreate n' creates a new thread pool with 'n' worker threads.
let threadPoolCreate : all a. Int -> ThreadPool a = lam n.
  let chan = channelEmpty () in
  {threads = create n (lam. threadSpawn (lam. _wait chan)), queue = chan}

-- 'threadPoolTearDown p' joins the threads in the pool 'p'.
--
-- NOTE: Should be called as soon as a thread pool has finished all intended
-- tasks. After 'threadPoolTearDown', no more tasks can be sent to the pool.
let threadPoolTearDown : all a. ThreadPool a -> () = lam pool.
  channelSendMany pool.queue (map (lam. Quit ()) pool.threads);
  iter threadJoin pool.threads

-- 'threadPoolAsync p task' sends a 'task' to the pool 'p'.
let threadPoolAsync : all a. ThreadPool a -> (() -> a) -> Async a = lam pool. lam task.
  let r = atomicMake (None ()) in
  channelSend pool.queue (Task {task = task, result = r});
  r

-- 'threadPoolWait p r' waits for a result 'r' to be available.
recursive let threadPoolWait : all a. ThreadPool a -> Async a -> a = lam pool. lam r.
  match atomicGet r with Some v then v
  else match channelRecvOpt pool.queue
  with Some (Task {task = task, result = result})
  then
    -- Do some work while we're waiting
    atomicSet result (Some (task ()));
    threadPoolWait pool r
  else
    threadCPURelax (); threadPoolWait pool r
end

mexpr

utest
  let pool = threadPoolCreate 8 in
  threadPoolTearDown pool
with () in

utest
  let pool = threadPoolCreate 2 in
  let r1 = threadPoolAsync pool (lam. addi 0 1) in
  let r2 = threadPoolAsync pool (lam. addi 0 2) in
  let r3 = threadPoolAsync pool (lam. addi 0 3) in
  let r4 = threadPoolAsync pool (lam. addi 0 4) in
  let r5 = threadPoolAsync pool (lam. addi 0 5) in
  let r6 = threadPoolAsync pool (lam. addi 0 6) in
  let r =
  [ threadPoolWait pool r1
  , threadPoolWait pool r2
  , threadPoolWait pool r3
  , threadPoolWait pool r4
  , threadPoolWait pool r5
  , threadPoolWait pool r6
  ] in
  threadPoolTearDown pool; r
with [1,2,3,4,5,6] in

()
