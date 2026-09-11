-- Function composition chains.
--
-- Exercises: closure allocation and higher-order application.  `build`
-- allocates `scale` nested closures, and each application of the result walks
-- a chain of `scale` non-tail calls, so both closure creation and closure
-- invocation are on the hot path.  Unlike the other benchmarks the called
-- function is not statically known at any call site.
--
-- Scales quadratically in `scale`: a chain of `scale` closures, applied
-- `scale` times.

mexpr

let scale = 4000 in -- SCALE

let compose = lam f. lam g. lam x. f (g x) in

recursive let build = lam i. lam f.
  if geqi i scale then f
  else build (addi i 1) (compose f (lam x. addi x 3))
in

let chain = build 0 (lam x. x) in

recursive let applyN = lam i. lam acc.
  if geqi i scale then acc
  else applyN (addi i 1) (modi (chain acc) 1000003)
in

exit (modi (applyN 0 0) 251)
