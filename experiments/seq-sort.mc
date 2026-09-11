-- Merge sort over a sequence.
--
-- Exercises: a realistic algorithm rather than one operation -- `splitAt`,
-- `length`, `cons` and sequence patterns together, with the tuple pattern that
-- takes `splitAt` apart.  `merge` is not tail recursive, so the host stack
-- carries the recursion as well.
--
-- Scales as scale*log(scale) in `scale` (number of elements sorted).

mexpr

let scale = 75000 in -- SCALE

let s = create scale (lam i. modi (muli i 48271) 100003) in

recursive let merge = lam a. lam b.
  match a with [] then b
  else match b with [] then a
  else match (a, b) with ([x] ++ ra, [y] ++ rb) in
    if leqi x y then cons x (merge ra b) else cons y (merge a rb)
in

recursive let msort = lam xs.
  let n = length xs in
  if leqi n 1 then xs
  else match splitAt xs (divi n 2) with (l, r) in merge (msort l) (msort r)
in

let sorted = msort s in

exit (modi (addi (get sorted 0) (get sorted (subi (length sorted) 1))) 251)
