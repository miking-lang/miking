
include "benchmarkcommon.mc"

mexpr

recursive
let fact = lam n.
  if eqi n 0
    then 1
    else muli n (fact (subi n 1))
in

repeat (lam. fact 100)
