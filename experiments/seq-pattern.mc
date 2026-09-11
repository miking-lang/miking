-- Walking a sequence with sequence patterns instead of indices.
--
-- Exercises: `PatSeqEdge` in both its forms -- `[x] ++ rest`, which is how
-- functional code usually takes a sequence apart, and `[x] ++ mid ++ [y]`,
-- which has to split at both ends and bind the middle.  Every step allocates
-- the remaining subsequence, so this measures pattern matching against
-- sequences rather than sequence operations.
--
-- Scales linearly in `scale` (sequence length); walked twice.

mexpr

let scale = 1500000 in -- SCALE

let s = create scale (lam i. modi (muli i 13) 1000003) in

recursive let front = lam xs. lam acc.
  match xs with [x] ++ rest then front rest (modi (addi acc x) 1000003)
  else acc
in

recursive let ends = lam xs. lam acc.
  match xs with [x] ++ mid ++ [y] then
    ends mid (modi (addi acc (addi x y)) 1000003)
  else match xs with [x] then modi (addi acc x) 1000003
  else acc
in

exit (modi (addi (front s 0) (ends s 0)) 251)
