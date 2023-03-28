include "benchmarkcommon.mc"

mexpr

recursive let fact = lam n. lam acc.
  if lti n 1 then acc else fact (subi n 1) (muli n acc)
in

let r = repeat (lam. fact 20 1) in
utest r with 2432902008176640000 using eqi in
()
