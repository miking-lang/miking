-- Repeated `map` and `mapi` passes over a sequence.
--
-- Exercises: `map` and `mapi`, which allocate a fresh sequence per pass and
-- call back into the evaluator once per element.  Unlike seq-fold.mc the result
-- of every call is retained, so this leans on allocation as much as on
-- dispatch.  The final fold passes `addi` itself as the callback, so a constant
-- travels through the general application path as a value.
--
-- Scales linearly in `scale` (sequence length); 5 passes plus one `mapi`.

mexpr

let scale = 600000 in -- SCALE

let s = create scale (lam i. i) in

recursive let passes = lam k. lam cur.
  if geqi k 5 then cur
  else passes (addi k 1) (map (lam x. modi (addi (muli x 3) 1) 1000003) cur)
in

let r = mapi (lam i. lam x. modi (addi i x) 1000003) (passes 0 s) in

exit (modi (foldl addi 0 r) 251)
