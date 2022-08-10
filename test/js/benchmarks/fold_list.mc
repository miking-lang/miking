include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"

mexpr

let foldf = lam n.
  foldl addi 0 (createList n (lam i. i))
in

let r = repeat (lam. foldf 100000) in
utest r with 4999950000 using eqi in
()
