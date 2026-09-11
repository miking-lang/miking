-- Indexed reads from a fixed sequence in a tight loop.
--
-- Exercises: `get` and `length`, the first-order sequence constants, with no
-- allocation at all in the loop body.  MCore sequences are ropes, so this is
-- where the cost of indexing into one shows up.
--
-- Scales linearly in `scale` (number of reads); the sequence itself stays at
-- 1024 elements.

mexpr

let scale = 2000000 in -- SCALE

let s = create 1024 (lam i. modi (muli i 37) 997) in

recursive let go = lam i. lam acc.
  if geqi i scale then acc
  else go (addi i 1) (modi (addi acc (get s (modi i (length s)))) 1000003)
in

exit (modi (go 0 0) 251)
