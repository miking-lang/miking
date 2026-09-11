-- Variable lookup at depth 64.
--
-- Exercises: reading a variable from far up the lexical environment.  An
-- evaluator that represents environments as an association list pays for the
-- distance on every read; one that resolves variables to indices or slots does
-- not.
--
-- The chain of `v` bindings is threaded (each one uses the previous) so that
-- dead-code elimination cannot remove it, and the hot loop reads `v0`, the
-- binding furthest from the point of use.  `v63` is read once at the end so
-- the whole chain stays live.
--
-- Scales linearly in `scale` (number of lookups); the lookup *depth* is fixed
-- at 64 by the shape of the program -- compare the two env-lookup benchmarks
-- against each other to see how lookup cost grows with scope size.

mexpr

let scale = 1500000 in -- SCALE

let v0 = 1 in
let v1 = addi v0 1 in
let v2 = addi v1 1 in
let v3 = addi v2 1 in
let v4 = addi v3 1 in
let v5 = addi v4 1 in
let v6 = addi v5 1 in
let v7 = addi v6 1 in
let v8 = addi v7 1 in
let v9 = addi v8 1 in
let v10 = addi v9 1 in
let v11 = addi v10 1 in
let v12 = addi v11 1 in
let v13 = addi v12 1 in
let v14 = addi v13 1 in
let v15 = addi v14 1 in
let v16 = addi v15 1 in
let v17 = addi v16 1 in
let v18 = addi v17 1 in
let v19 = addi v18 1 in
let v20 = addi v19 1 in
let v21 = addi v20 1 in
let v22 = addi v21 1 in
let v23 = addi v22 1 in
let v24 = addi v23 1 in
let v25 = addi v24 1 in
let v26 = addi v25 1 in
let v27 = addi v26 1 in
let v28 = addi v27 1 in
let v29 = addi v28 1 in
let v30 = addi v29 1 in
let v31 = addi v30 1 in
let v32 = addi v31 1 in
let v33 = addi v32 1 in
let v34 = addi v33 1 in
let v35 = addi v34 1 in
let v36 = addi v35 1 in
let v37 = addi v36 1 in
let v38 = addi v37 1 in
let v39 = addi v38 1 in
let v40 = addi v39 1 in
let v41 = addi v40 1 in
let v42 = addi v41 1 in
let v43 = addi v42 1 in
let v44 = addi v43 1 in
let v45 = addi v44 1 in
let v46 = addi v45 1 in
let v47 = addi v46 1 in
let v48 = addi v47 1 in
let v49 = addi v48 1 in
let v50 = addi v49 1 in
let v51 = addi v50 1 in
let v52 = addi v51 1 in
let v53 = addi v52 1 in
let v54 = addi v53 1 in
let v55 = addi v54 1 in
let v56 = addi v55 1 in
let v57 = addi v56 1 in
let v58 = addi v57 1 in
let v59 = addi v58 1 in
let v60 = addi v59 1 in
let v61 = addi v60 1 in
let v62 = addi v61 1 in
let v63 = addi v62 1 in

recursive let loop = lam i. lam acc.
  if geqi i scale then acc
  else loop (addi i 1) (addi acc v0)
in

exit (modi (addi (loop 0 0) v63) 251)
