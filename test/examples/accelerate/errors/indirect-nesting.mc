let f = lam x. accelerate (addi x 1)
let g = lam x. lam y. addi x (f y)
let h = lam x. g x 2
mexpr
accelerate (h 4)
