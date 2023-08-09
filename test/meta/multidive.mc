

mexpr

let foo = lam x. lam k1. lam k2.
  (addi (addi (addi x 10) k1) k2) in

let foo2 = prerun (dive (foo 2)) in

dprint foo2; print "------\n";
dprint (foo2 10 20); print "\n"
