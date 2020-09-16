-- constants
let eps = 1.e-15
let pi = mulf 4. (extAtan 1.)

-- Elementary functions
let abs = lam x. if ltf x 0. then negf x else x

let eqfEps = lam l. lam r.
  ltf (abs (subf l r)) eps

-- Trigonometic functions
let sin = extSin
utest sin (divf pi 2.) with 1. using eqfEps
utest sin 0. with 0. using eqfEps

let cos = extCos
utest cos (divf pi 2.) with 0. using eqfEps
utest cos 0. with 1. using eqfEps

utest addf (mulf (sin 1.) (sin 1.)) (mulf (cos 1.) (cos 1.)) with 1.
using eqfEps

let exp = extExp
utest exp 0. with 1. using eqfEps
