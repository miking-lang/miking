mexpr
accelerate (
  let f = lam x. lam y. addi x y in
  foldl f 0 (create 10 (lam i. i)))
