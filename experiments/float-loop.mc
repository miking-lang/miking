-- A tight loop of floating-point arithmetic.
--
-- Exercises: `addf`, `subf`, `mulf`, `divf` and `int2float` with nothing else
-- in the loop body.  This is the float counterpart of loop-sum.mc: it measures
-- what the evaluator charges per float operation, including boxing each
-- intermediate result.
--
-- Scales linearly in `scale` (number of iterations).

mexpr

let scale = 2000000 in -- SCALE

recursive let go = lam i. lam acc.
  if geqi i scale then acc
  else
    let x = divf (int2float (modi i 1000)) 1000.0 in
    go (addi i 1) (addf (mulf acc 0.75) (subf x 0.25))
in

exit (modi (roundfi (mulf (go 0 0.0) 1000.0)) 251)
