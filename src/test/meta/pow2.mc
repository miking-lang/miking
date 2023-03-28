
mexpr

recursive
  let pow = lam n. lam x.
    if eqi n 0 then 1
    else muli (dive (pow (subi n 1)) x) x
in

let pow3 = dive (pow 3) in

dprint (pow3 4);
print "\n";
dprint (pow 3 4);
print "\n"

-- Manual example with "dive (pow 2)"

/--

lam x.  -- n = 2
  muli
    ((lam x.  -- n = 1
        muli
          ((lam x. -- n = 0
             1) x)
         x) x) x
--/

-- In the end, it will still substitute and result in

/--

lam x. muli (muli 1 x) x

--/

-- Without simplifications
