
-- Test case which shows that you must do closure
-- removal during runtime, when partial evaluation has finished.
-- That is, we cannot leave symbols inside closures.

mexpr

let foo = lam y.
   prerun (let bar = lam x. addi x y in bar)
in

utest foo 2 3 with 5 in

dprint foo; print "\n-----\n";
dprint (foo 2 3); print "\n"
