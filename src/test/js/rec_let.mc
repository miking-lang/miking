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
  dprintLn (fact 5);
  dprintLn (fact 10);
  dprintLn (fact 20);
  -- dprintLn (fact 40);
  recursive
      let isEven = lam n.
        if eqi n 0 then true
        else isOdd (subi n 1)
      let isOdd = lam n.
        if eqi n 0 then false
        else isEven (subi n 1)
  in
  dprintLn (isEven 10);
  dprintLn (isOdd 10);
  dprintLn (isEven 15);
  dprintLn (isOdd 15);

  let wrapper = lam n.
    recursive let work = lam a. lam b.
      let m = subi a n in
      if lti m 1 then b
      else work m (muli b b)
    in
    work
  in
  dprintLn (wrapper 1 4 2);
  dprintLn (wrapper 2 3 4);
  dprintLn ((wrapper 10) 50 2);
  ()
