include "common.mc"
include "string.mc"

mexpr
  recursive let fact_rect = lam acc. lam n.
    if eqi n 0 then acc
    else fact_rect (muli n acc) (subi n 1)
  in
  let fact = lam n. fact_rect 1 n in
  printLn (int2string (fact 5));
  printLn (int2string (fact 10));
  printLn (int2string (fact 20));
  printLn (int2string (fact 40));
  recursive
      let isEven_rect = lam n.
        if eqi n 0 then "true"
        else isOdd_rect (subi n 1)
      let isOdd_rect = lam n.
        if eqi n 0 then "false"
        else isEven_rect (subi n 1)
  in
  printLn (isEven_rect 10);
  printLn (isOdd_rect 10);
  printLn (isEven_rect 15);
  printLn (isOdd_rect 15);
  ()
