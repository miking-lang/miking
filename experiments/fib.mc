-- Naive Fibonacci.
--
-- Exercises: non-tail recursion, one-argument closure application, integer
-- comparison and addition.  The call tree is wide and shallow, so this is
-- dominated by raw function-call overhead.
--
-- Scales exponentially in `scale` (~1.6^scale calls).

mexpr

let scale = 32 in -- SCALE

recursive let fib = lam n.
  if lti n 2 then n
  else addi (fib (subi n 1)) (fib (subi n 2))
in

exit (modi (fib scale) 251)
