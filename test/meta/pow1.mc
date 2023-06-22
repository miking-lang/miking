

mexpr

recursive
  let pow = lam n. lam x.
    if eqi n 0 then 1
    else muli (pow (subi n 1) x) x
in

let pow3 = lam x. prerun (pow 3 x) in
let pow6 = lam x. prerun (pow 6 x) in

--let f = lam x. prerun (addi x 1) in

dprint (pow 2 3); print "\n-----\n";
print "Hello\n"; ()

/--
dprint pow; print "\n-----\n";
dprint (pow3 5); print "\n";
dprint (pow 3 5); print "\n";
dprint (pow6 2); print "\n";
dprint (pow 6 2); print "\n"
--/
