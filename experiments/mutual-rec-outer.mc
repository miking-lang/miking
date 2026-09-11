-- The same three-way cycle as mutual-rec.mc, except that the loop counts *up*
-- to `scale`, so each body reads a variable bound outside the `recursive`
-- group instead of only its own parameters.
--
-- Exercises: variable lookup from inside a multi-binding `recursive` group.
--
-- This pair used to expose a bug in `eval-fast.mc`: `RecLetsEval` passed the
-- fold *accumulator* rather than the incoming environment to its recursive
-- `reclet` call, so calling the second or third binding prepended another copy
-- of the group to the environment.  The environment grew without bound as the
-- loop ran, and since `scale` lives below all of that growth, every lookup of
-- it walked further than the last.  mutual-rec.mc hid the lookup cost because
-- its bodies never look past their own parameters, but it still paid for the
-- allocation.  Both are fixed; keep the two at the same scale so the remaining
-- difference is just the free-variable read.
--
-- Scales linearly in `scale`.

mexpr

let scale = 1200000 in -- SCALE

recursive
  let a = lam n. lam acc. if geqi n scale then acc else b (addi n 1) (addi acc 1)
  let b = lam n. lam acc. if geqi n scale then acc else c (addi n 1) (addi acc 2)
  let c = lam n. lam acc. if geqi n scale then acc else a (addi n 1) (addi acc 3)
in

exit (modi (a 0 0) 251)
