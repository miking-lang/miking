-- Non-tail-recursive sum of 1..scale.
--
-- Exercises: recursion depth rather than recursion count.  Every call has a
-- pending `addi` continuation, so the interpreter must keep `scale` frames
-- alive at once.  Useful for finding where each backend runs out of stack.
--
-- Scales linearly in `scale`, both in time and in stack depth.

mexpr

let scale = 500000 in -- SCALE

recursive let sum = lam k.
  if eqi k 0 then 0
  else addi k (sum (subi k 1))
in

exit (modi (sum scale) 251)
