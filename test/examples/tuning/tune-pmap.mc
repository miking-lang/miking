
-- mi tune test/examples/tuning/tune-pmap.mc -- --verbose --input 10000

include "string.mc"
include "multicore/hseq.mc"

mexpr

let n = string2int (get argv 1) in
let f = lam. sleepMs 1 in

hmap f (create n (lam i. i))
