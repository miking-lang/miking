-- Lists encoded as their own right fold (Boehm-Berarducci / Church encoding).
--
-- Exercises: data structures built entirely out of closures, which is the only
-- way to get recursive data past the subset of MExpr that the fast evaluator
-- supports (it has no constructor patterns).  Consing allocates a closure per
-- element; folding walks the chain with a non-tail call per element.
--
-- Scales linearly in `scale` (list length); the list is folded three times.

mexpr

let scale = 200000 in -- SCALE

type IntList = (Int -> Int -> Int) -> Int -> Int in

let nil : IntList = lam f. lam z. z in
let cons : Int -> IntList -> IntList =
  lam x. lam xs. lam f. lam z. f x (xs f z) in

recursive let build = lam i. lam acc.
  if geqi i scale then acc
  else build (addi i 1) (cons i acc)
in

let l = build 0 nil in

let sum = l (lam x. lam acc. modi (addi x acc) 1000003) 0 in
let cnt = l (lam. lam acc. addi acc 1) 0 in
let mx  = l (lam x. lam acc. if gti x acc then x else acc) 0 in

exit (modi (addi sum (addi cnt mx)) 251)
