-- A tight tail-recursive accumulator loop.
--
-- Exercises: tail calls, two-argument currying, and the per-iteration cost of
-- the interpreter's dispatch loop.  This is the cheapest possible body, so it
-- measures interpretation overhead almost in isolation.
--
-- Scales linearly in `scale` (number of iterations).

mexpr

let scale = 2000000 in -- SCALE

recursive let loop = lam i. lam acc.
  if geqi i scale then acc
  else loop (addi i 1) (addi acc i)
in

exit (modi (loop 0 0) 251)
