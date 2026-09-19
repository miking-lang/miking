-- FizzBuzz classification done entirely with `PatAnd`/`PatOr`/`PatNot`
-- pattern combinators instead of `if`/`modi` guards.
--
-- Exercises: `PatOr` (each category is a disjunction of up to six `PatInt`
-- literals), `PatAnd` (the "div by 3 and 4" category matches the same value
-- against two `PatOr`s in sequence, threading env between them), and
-- `PatNot` (the residual "plain number" category is `!(divBy3 | divBy4)`
-- unfolded over literals). All three run on every iteration via a chain of
-- `match`/`else match`.
--
-- Scales linearly in `scale` (loop iterations).

mexpr

let scale = 1500000 in -- SCALE

let classify = lam r.
  match r with (0 | 3 | 6 | 9) & (0 | 4 | 8) then 3
  else match r with 0 | 3 | 6 | 9 then 1
  else match r with 0 | 4 | 8 then 2
  else match r with !(0 | 3 | 4 | 6 | 8 | 9) then 0
  else never
in

recursive let loop = lam i. lam acc.
  if geqi i scale then acc
  else
    let c = classify (modi i 12) in
    loop (addi i 1) (modi (addi acc c) 1000003)
in

exit (modi (loop 0 0) 251)
