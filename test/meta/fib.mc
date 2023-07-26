

mexpr


recursive
  let fib = lam n.
    if leqi n 1 then n else
    addi (fib (subi n 1)) (fib (subi n 2))
in


dprint (fib 12); print "\n------\n"
