-- Summing the population count of 1..scale, computed with shifts.
--
-- Exercises: the shift constants (`slli`, `srli`), which are otherwise
-- untouched by the rest of the suite, together with a short inner loop whose
-- trip count varies with the input.
--
-- Scales linearly in `scale` (times ~log2(scale) inner iterations).

mexpr

let scale = 200000 in -- SCALE

recursive let popcount = lam n. lam acc.
  if eqi n 0 then acc
  else popcount (srli n 1) (addi acc (subi n (slli (srli n 1) 1)))
in

recursive let go = lam i. lam acc.
  if gti i scale then acc
  else go (addi i 1) (addi acc (popcount i 0))
in

exit (modi (go 1 0) 251)
