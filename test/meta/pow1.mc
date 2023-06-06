

mexpr

recursive
  let pow = lam n. lam x.
    if eqi n 0 then 1
    else muli (pow (subi n 1) x) x
in

let pow3 = dive (pow 3) in

dprint (pow3 4);
print "\n";
dprint (pow 3 4);
print "\n"
