

-- The example show two ways of specializing a function,
-- using only prerun, or a combination of prerun and dive

mexpr


recursive
  let pow = lam n. lam x.
    if eqi n 0 then 1
    else muli (pow (subi n 1) x) x
in

let pow3a = lam x. prerun (pow 3 x) in
let pow3b = prerun (dive (pow 3)) in

dprint (pow 3 5);
dprint (pow3a 5);
dprint (pow3b 5);

let pow6 = lam x. prerun (pow 6 x) in
let pow6d = prerun (dive (pow 6)) in

dprint pow; print "\n-----\n";
dprint pow3a; print "\n-----\n";
dprint pow6; print "\n-----\n";
dprint pow6d; print "\n-----\n";

dprint (pow 3 5); print "\n";
dprint (pow3a 5); print "\n";
dprint (pow 6 2); print "\n";
dprint (pow6 2); print "\n";
dprint (pow6d 2); print "\n"
