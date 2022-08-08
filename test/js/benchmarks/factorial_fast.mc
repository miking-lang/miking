include "benchmarkcommon.mc"

mexpr

recursive let fact = lam n. lam acc.
  if eqi n 0 then acc else fact (subi n 1) (muli n acc)
in

repeat (lam. fact 100 1)
