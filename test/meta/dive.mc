

mexpr

-- Continuous to apply a lambda after diving into it
let foo = lam y. prerun ((dive (lam x. addi (addi 1 2) x)) y) in
dprint foo; print "\n------\n";

()
