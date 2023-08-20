
-- Instead of specializing for x^3, we try to
-- specialize for 3^x. This should yield no specialization,
-- but should still terminate.

mexpr

recursive
  let pow = lam n. lam x.
    if eqi n 0 then 1
    else muli (pow (subi n 1) x) x
in

let pow3 = lam x. prerun (pow x 3) in

dprint pow3; print "\n-----\n";
dprint (pow3 2); print "\n"
