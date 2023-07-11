

mexpr

-- Evaluate recursive let functions before proceeding
recursive
  let foo =
    let y = 2 in lam x. addi x y
in

dprint foo; print "\n------\n";
dprint (foo 2); print "\n";


()
