-- The Takeuchi function, tak(3k, 2k, k).
--
-- Exercises: three-argument currying (three closures allocated per call),
-- non-tail recursion where every argument position is a recursive call, and a
-- branch condition that depends on two of the arguments.
--
-- Scales steeply in `scale`; tak(18,12,6) is the classic size (scale = 6).

mexpr

let scale = 9 in -- SCALE

recursive let tak = lam x. lam y. lam z.
  if geqi y x then z
  else tak (tak (subi x 1) y z) (tak (subi y 1) z x) (tak (subi z 1) x y)
in

exit (modi (tak (muli 3 scale) (muli 2 scale) scale) 251)
