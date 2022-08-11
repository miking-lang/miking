include "benchmarkcommon.mc"

mexpr

recursive let fact = lam n.
  if eqi n 0 then 1 else muli n (fact (subi n 1))
in

let r = repeat (lam. fact 1000) in
utest r with 1000000 using gti in
()
