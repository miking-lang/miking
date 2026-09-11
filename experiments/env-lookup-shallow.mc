-- Variable lookup at depth 4.
--
-- Exercises: reading a variable that is only a few bindings away from its use.
-- This is the control for env-lookup-deep.mc.
--
-- The chain of `v` bindings is threaded (each one uses the previous) so that
-- dead-code elimination cannot remove it, and the hot loop reads `v0`, the
-- binding furthest from the point of use.  `v3` is read once at the end so
-- the whole chain stays live.
--
-- Scales linearly in `scale` (number of lookups); the lookup *depth* is fixed
-- at 4 by the shape of the program -- compare the two env-lookup benchmarks
-- against each other to see how lookup cost grows with scope size.

mexpr

let scale = 1500000 in -- SCALE

let v0 = 1 in
let v1 = addi v0 1 in
let v2 = addi v1 1 in
let v3 = addi v2 1 in

recursive let loop = lam i. lam acc.
  if geqi i scale then acc
  else loop (addi i 1) (addi acc v0)
in

exit (modi (addi (loop 0 0) v3) 251)
