-- Persistent element update in a loop.
--
-- Exercises: `set`, the only three-argument sequence constant, so it is also
-- the benchmark that exercises the evaluator's three-argument constant path.
-- Each update produces a new sequence, so the cost is whatever the underlying
-- representation charges for a persistent write.
--
-- Scales linearly in `scale` (number of updates); the sequence stays at 256
-- elements.

mexpr

let scale = 1200000 in -- SCALE

let s = create 256 (lam i. i) in

recursive let go = lam i. lam cur.
  if geqi i scale then cur
  else go (addi i 1) (set cur (modi i 256) (modi (muli i 7) 1000003))
in

exit (modi (foldl addi 0 (go 0 s)) 251)
