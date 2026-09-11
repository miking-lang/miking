-- Counting the primes below `scale` by trial division.
--
-- Exercises: a realistic mix of integer arithmetic -- multiplication for the
-- `d*d > n` bound, `modi` for the divisibility test -- inside two levels of
-- tail recursion with data-dependent exits.
--
-- Scales roughly as scale^1.5.

mexpr

let scale = 300000 in -- SCALE

recursive let isPrimeFrom = lam n. lam d.
  if gti (muli d d) n then true
  else if eqi (modi n d) 0 then false
  else isPrimeFrom n (addi d 2)
in

recursive let countFrom = lam n. lam acc.
  if gti n scale then acc
  else countFrom (addi n 2) (if isPrimeFrom n 3 then addi acc 1 else acc)
in

exit (modi (countFrom 3 1) 251)
