
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "map_n.ml"
include "multicore/pseq.mc"

mexpr

let nThreads = 8 in
let pool = threadPoolCreate nThreads in

let workload = 20 in
recursive let fibonacci = lam n.
  if lti n 3 then 1
  else addi (fibonacci (subi n 1)) (fibonacci (subi n 2))
in

let mapf = lam n.
  let res = map (lam. fibonacci workload) (createList n (lam i. i)) in
  utest length res with n using eqi in
  res
in

let res = bc_repeat (lam. mapf n) in

threadPoolTearDown pool;

res
