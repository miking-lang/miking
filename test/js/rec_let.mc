include "common.mc"
include "string.mc"

mexpr
  recursive let fact_rect = lam acc. lam n.
    if eqi n 0 then acc
    else fact_rect (muli n acc) (subi n 1)
  in
  let fact = lam n. lam acc. fact_rect acc n in
  printLn (int2string (fact 5 1));
  printLn (int2string (fact 10 1));
  printLn (int2string (fact 20 1));
  printLn (int2string (fact 40 1));
  ()
