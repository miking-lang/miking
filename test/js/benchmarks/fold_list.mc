include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"

mexpr

let foldf = lam n.
  foldl addi 0 (createList (addi n 1) (lam i. i))
in

let r = repeat (lam. foldf 100000) in
utest r with 5000050000 using eqi in
()
