-- A three-way mutually recursive cycle, expressed as one `recursive` group
-- with three bindings.
--
-- Exercises: dispatch between sibling bindings of a `recursive` group.  Every
-- other benchmark in this suite deliberately uses separate single-binding
-- groups, so this is the only one that measures how an evaluator ties the knot
-- across several bindings at once.  The loop body is the same counter as
-- loop-sum.mc, and it reads no variable from outside the group, so any
-- difference against loop-sum.mc is the cost of the group itself.
--
-- See mutual-rec-outer.mc for the same cycle with a free variable in the body;
-- the two are kept at the same scale so they can be compared directly.
--
-- Scales linearly in `scale` (number of steps around the cycle).

mexpr

let scale = 1200000 in -- SCALE

recursive
  let a = lam n. lam acc. if eqi n 0 then acc else b (subi n 1) (addi acc 1)
  let b = lam n. lam acc. if eqi n 0 then acc else c (subi n 1) (addi acc 2)
  let c = lam n. lam acc. if eqi n 0 then acc else a (subi n 1) (addi acc 3)
in

exit (modi (a scale 0) 251)
