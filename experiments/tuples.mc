-- The same loop as records.mc, but with the state packed in a tuple that is
-- rebuilt from scratch each iteration instead of updated field by field.
--
-- Exercises: record (tuple) construction and tuple patterns, without
-- `TmRecordUpdate`.  Comparing against records.mc isolates the cost of
-- record update versus record construction.
--
-- Scales linearly in `scale` (number of iterations).

mexpr

let scale = 700000 in -- SCALE

recursive let step = lam s.
  match s with (i, a, b, c, d) in
  if geqi i scale then s
  else
    step
      ( addi i 1
      , modi (addi a b) 1000003
      , modi (addi b c) 1000003
      , modi (addi c d) 1000003
      , modi (addi d 1) 1000003 )
in

match step (0, 0, 1, 2, 3) with (_, a, _, c, _) in

exit (modi (addi a c) 251)
