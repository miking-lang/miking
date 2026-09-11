-- The Ackermann function, ack(3, scale).
--
-- Exercises: very deep non-tail recursion combined with a huge number of small
-- calls, and nested application where an argument is itself a recursive call.
-- Stresses the interpreter's use of the host stack.
--
-- Scales exponentially in `scale` (ack(3,n) = 2^(n+3) - 3).

mexpr

let scale = 8 in -- SCALE

recursive let ack = lam m. lam n.
  if eqi m 0 then addi n 1
  else if eqi n 0 then ack (subi m 1) 1
  else ack (subi m 1) (ack m (subi n 1))
in

exit (modi (ack 3 scale) 251)
