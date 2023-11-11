


mexpr


let double = lam x. addi x x in

let foo = lam y. prerun (double, double) in

print "\n"; dprint foo; print "\n";

utest ((foo 5).0) 3 with 6 in

()
