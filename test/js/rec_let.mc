include "common.mc"
include "string.mc"

mexpr
  recursive let fact_rect = lam acc. lam n.
    if eqi n 0 then acc
    else fact_rect (muli n acc) (subi n 1)
  in
  let fact = lam n. fact_rect 1 n in
  dprintLn (fact 5);
  dprintLn (fact 10);
  dprintLn (fact 20);
  -- dprintLn (fact 40);
  recursive
      let isEven_rect = lam n.
        if eqi n 0 then true
        else isOdd_rect (subi n 1)
      let isOdd_rect = lam n.
        if eqi n 0 then false
        else isEven_rect (subi n 1)
  in
  dprintLn (isEven_rect 10);
  dprintLn (isOdd_rect 10);
  dprintLn (isEven_rect 15);
  dprintLn (isOdd_rect 15);

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
