include "benchmarkcommon.mc"
include "common.mc"

mexpr

recursive let fact = lam n.
  if lti n 1 then 1 else muli n (fact (subi n 1))
in

let r = repeat (lam. fact 20) in
utest r with 2432902008176640000 using eqi in
()
