-- A loop carrying a five-field record as its state.
--
-- Exercises: record construction, multi-field record update (`{s with ...}`),
-- and record patterns.  Every iteration allocates a fresh record and destructs
-- it again, so this measures record handling rather than call overhead.
--
-- Scales linearly in `scale` (number of iterations).

mexpr

let scale = 700000 in -- SCALE

type St = {i : Int, a : Int, b : Int, c : Int, d : Int} in

recursive let step = lam s : St.
  match s with {i = i, a = a, b = b, c = c, d = d} in
  if geqi i scale then s
  else
    step
      { s with
        i = addi i 1,
        a = modi (addi a b) 1000003,
        b = modi (addi b c) 1000003,
        c = modi (addi c d) 1000003,
        d = modi (addi d 1) 1000003 }
in

match step {i = 0, a = 0, b = 1, c = 2, d = 3} with {a = a, c = c} in

exit (modi (addi a c) 251)
