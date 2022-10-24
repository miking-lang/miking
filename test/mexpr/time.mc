-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test time measurements intrinsics

mexpr

-- 'wallTimeMs () : () -> Float' gives the current time stamp (absolute value
-- is meaningless). The difference between subsequent calls to 'wallTimeMs'
-- gives the elapsed wall time in ms.

-- 'sleepMs ms : Int -> ()' pauses the execution for 'ms' number of ms.

let t1 = wallTimeMs () in
sleepMs 1;
let t2 = wallTimeMs () in

utest t2 with t1 using gtf in ()
