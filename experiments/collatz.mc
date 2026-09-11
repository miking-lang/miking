-- Longest Collatz chain starting below `scale`.
--
-- Exercises: division and remainder, and branching that the interpreter cannot
-- predict (the parity test alternates irregularly).  The inner loop is short
-- and hot, the outer loop long.
--
-- Scales slightly super-linearly in `scale`.

mexpr

let scale = 60000 in -- SCALE

recursive let chain = lam n. lam len.
  if eqi n 1 then len
  else if eqi (modi n 2) 0 then chain (divi n 2) (addi len 1)
  else chain (addi (muli 3 n) 1) (addi len 1)
in

recursive let go = lam i. lam best.
  if gti i scale then best
  else
    let l = chain i 1 in
    go (addi i 1) (if gti l best then l else best)
in

exit (modi (go 1 0) 251)
