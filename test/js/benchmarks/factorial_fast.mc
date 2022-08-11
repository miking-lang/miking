include "benchmarkcommon.mc"

mexpr

recursive let fact = lam n. lam acc.
  if eqi n 0 then acc else fact (subi n 1) (muli n acc)
in

let r = repeat (lam. fact 1000 1) in
utest r with 1000000 using gti in
()
