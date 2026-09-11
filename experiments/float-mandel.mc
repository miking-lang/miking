-- Escape-time Mandelbrot over a scale x scale grid.
--
-- Exercises: float arithmetic and comparison inside three levels of recursion,
-- with a five-argument curried inner function.  Unlike float-loop.mc the
-- branch depends on the float comparison, and the iteration count varies per
-- point, so this is the realistic-workload float benchmark.
--
-- Scales quadratically in `scale` (grid side), times up to 50 inner steps.

mexpr

let scale = 320 in -- SCALE

let limit = 50 in

recursive let escape = lam cr. lam ci. lam zr. lam zi. lam k.
  if geqi k limit then k
  else
    let zr2 = mulf zr zr in
    let zi2 = mulf zi zi in
    if gtf (addf zr2 zi2) 4.0 then k
    else
      escape cr ci
        (addf (subf zr2 zi2) cr)
        (addf (mulf 2.0 (mulf zr zi)) ci)
        (addi k 1)
in

let side = int2float scale in

recursive let row = lam y. lam x. lam acc.
  if geqi x scale then acc
  else
    let cr = subf (divf (mulf 3.0 (int2float x)) side) 2.0 in
    let ci = subf (divf (mulf 3.0 (int2float y)) side) 1.5 in
    row y (addi x 1) (addi acc (escape cr ci 0.0 0.0 0))
in

recursive let grid = lam y. lam acc.
  if geqi y scale then acc
  else grid (addi y 1) (addi acc (row y 0 0))
in

exit (modi (grid 0 0) 251)
