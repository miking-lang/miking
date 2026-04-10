include "common.mc"
include "string.mc"

mexpr
  -- non-recursive let
  let add = lam x. lam y. addi x y in
  recursive let _fact = lam acc. lam n.
    if eqi n 0 then add acc 0
    else _fact (muli n acc) (subi n 1)
  in
  let fact = lam n. _fact 1 n in
  printLn (int2string (fact 5));
  printLn (int2string (fact 10));
  printLn (int2string (fact 20));
  -- dprintLn (fact 40);
  recursive
      let isEven = lam n.
        if eqi n 0 then true
        else isOdd (subi n 1)
      let isOdd = lam n.
        if eqi n 0 then false
        else isEven (subi n 1)
  in
  printLn (bool2string (isEven 10));
  printLn (bool2string (isOdd 10));
  printLn (bool2string (isEven 15));
  printLn (bool2string (isOdd 15));

  let wrapper = lam n.
    recursive let work = lam a. lam b.
      let m = subi a n in
      if lti m 1 then b
      else work m (muli b b)
    in
    work
  in
  printLn (int2string (wrapper 1 4 2));
  printLn (int2string (wrapper 2 3 4));
  printLn (int2string ((wrapper 10) 50 2));
  ()
