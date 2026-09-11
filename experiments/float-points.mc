-- A loop carrying a record of floats, updated field by field.
--
-- Exercises: floats stored in records rather than passed as arguments, so the
-- evaluator boxes each component twice -- once as a float value, once in the
-- record.  Comparing against records.mc, which carries the same shape of state
-- with integers, isolates the cost of float values from the cost of records.
--
-- Scales linearly in `scale` (number of steps).

mexpr

let scale = 800000 in -- SCALE

type P = {i : Int, x : Float, y : Float, vx : Float, vy : Float} in

recursive let step = lam p : P.
  match p with {i = i, x = x, y = y, vx = vx, vy = vy} in
  if geqi i scale then p
  else
    let ax = negf (mulf x 0.001) in
    let ay = negf (mulf y 0.001) in
    step
      { p with
        i = addi i 1,
        x = addf x (mulf vx 0.01),
        y = addf y (mulf vy 0.01),
        vx = addf vx ax,
        vy = addf vy ay }
in

match step {i = 0, x = 1.0, y = 0.5, vx = 0.0, vy = 0.25} with {x = x, y = y} in

exit (modi (roundfi (mulf (addf (mulf x x) (mulf y y)) 1000.0)) 251)
