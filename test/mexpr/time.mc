-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test time measurements intrinsics

mexpr

-- 'wallTimeMs () : Unit -> Int' gives the current time stamp (absolute value is meaningless).
-- The difference between subsequent calls to 'wallTimeMs' gives the elapsed wall time in ms.

-- 'sleepMs ms : Int -> Unit' pauses the execution for 'ms' number of ms.

let t1 = wallTimeMs () in
let _ = sleepMs 1 in
let t2 = wallTimeMs () in

utest gti t2 t1 with true in ()
