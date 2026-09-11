-- Folding a sequence with a closure callback, in both directions.
--
-- Exercises: `create`, `foldl` and `foldr`.  These are the higher-order
-- sequence constants: the evaluator hands each element back through its own
-- application path, so this measures the cost of a callback per element rather
-- than the cost of the sequence itself.  `foldr` is not tail recursive, so it
-- also holds `scale` frames of host stack.
--
-- Scales linearly in `scale` (sequence length); the sequence is folded 4 times.

mexpr

let scale = 1000000 in -- SCALE

let s = create scale (lam i. modi (muli i 7) 1000003) in

let add = lam a. lam x. modi (addi a x) 1000003 in

recursive let passes = lam k. lam acc.
  if geqi k 3 then acc
  else passes (addi k 1) (add acc (foldl add 0 s))
in

let l = passes 0 0 in
let r = foldr (lam x. lam a. modi (addi x a) 1000003) 0 s in

exit (modi (addi l r) 251)
