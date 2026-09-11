-- Two nested tail-recursive loops.
--
-- Exercises: nested loops, three-argument currying, multiplication, and a
-- closure (`inner`) that is called from another function rather than only from
-- itself.
--
-- Scales quadratically in `scale` (scale * scale iterations of the inner body).

mexpr

let scale = 2000 in -- SCALE

recursive let inner = lam i. lam j. lam acc.
  if geqi j scale then acc
  else inner i (addi j 1) (modi (addi acc (muli i j)) 1000003)
in

recursive let outer = lam i. lam acc.
  if geqi i scale then acc
  else outer (addi i 1) (inner i 0 acc)
in

exit (modi (outer 0 0) 251)
