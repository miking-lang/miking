include "common.mc"
include "string.mc"

mexpr
  recursive let fact = lam n. lam acc.
    if eqi n 0 then acc
    else fact (subi n 1) (muli n acc)
  in
  printLn (int2string (fact 5 1));
  printLn (int2string (fact 10 1));
  printLn (int2string (fact 20 1));
  printLn (int2string (fact 40 1));
  ()
