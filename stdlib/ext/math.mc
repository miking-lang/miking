let pi = mulf 4. (extAtan 1.)
let abs = lam x. if ltf x 0. then negf x else x

mexpr
let eps = 1.e-15 in

let eqfEps = lam l. lam r.
  ltf (abs (subf l r)) eps
in

utest eqfEps (extCos pi) (negf 1.) with true in
utest eqfEps (extSin pi) (extSin 0.) with true in

()
