include "common.mc"
include "string.mc"

mexpr
  recursive let fact_rect = lam acc. lam n.
    if eqi n 0 then acc
    else fact_rect (muli n acc) (subi n 1)
  in
  let fact = fact_rect 1 in
  printLn (int2string (fact 5));
  printLn (int2string (fact 10));
  printLn (int2string (fact 20));
  printLn (int2string (fact 40));
  ()
