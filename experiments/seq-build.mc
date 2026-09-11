-- Building sequences by consing, snocing and concatenating.
--
-- Exercises: `cons`, `snoc`, `concat`, `length` and `subsequence`.  Growing a
-- rope from both ends is the case MCore's sequence representation is built
-- for, and none of it goes through a callback, so this is the counterpart to
-- seq-map.mc: allocation without dispatch.
--
-- Scales linearly in `scale` (elements added at each end).

mexpr

let scale = 1200000 in -- SCALE

recursive let front = lam i. lam acc.
  if geqi i scale then acc else front (addi i 1) (cons i acc)
in

recursive let back = lam i. lam acc.
  if geqi i scale then acc else back (addi i 1) (snoc acc i)
in

let both = concat (front 0 []) (back 0 []) in

exit (modi (addi (length both) (foldl addi 0 (subsequence both 0 1024))) 251)
