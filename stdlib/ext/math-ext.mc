let maxf = lam r. lam l. if gtf r l then r else l

let absf = lam f. maxf f (negf f)

let eqfApprox = lam epsilon. lam r. lam l.
  if leqf (absf (subf r l)) epsilon then true else false

utest 1. with 1.01 using eqfApprox 0.011
utest negf 1.0 with negf 1.009 using eqfApprox 0.01
utest 0.0 with 0.0  using (eqfApprox 0.)
utest eqfApprox 0.01 1.0 1.011 with false
utest 1. with 1.000009 using eqfApprox 0.00001
utest eqfApprox 0.00001 1.0 1.000011 with false

let _eqf = eqfApprox 1e-15

utest maxf 0. 0. with 0. using eqf
utest maxf 1. 0. with 1. using eqf
utest maxf 0. 1. with 1. using eqf

external externalExp : Float -> Float
let exp = lam x. externalExp x
utest exp 0. with 1. using eqf

external externalLog : Float -> Float
let log = lam x. externalLog x
utest log (exp 7.) with 7. using eqf
utest exp (log 7.) with 7. using _eqf

external externalAtan : Float -> Float
let atan = lam x. externalAtan x
utest atan 0. with 0. using eqf

let pi = mulf 4. (atan 1.)

external externalSin : Float -> Float
let sin = lam x. externalSin x
utest sin (divf pi 2.) with 1. using eqf
utest sin 0. with 0. using eqf

external externalCos : Float -> Float
let cos = lam x. externalCos x
utest cos (divf pi 2.) with 0. using _eqf
utest cos 0. with 1. using eqf

utest addf (mulf (sin 1.) (sin 1.)) (mulf (cos 1.) (cos 1.)) with 1.
using eqf

external externalAtan2 : Float -> Float -> Float
let atan2 = lam x. lam y. externalAtan2 x y
utest atan2 0. 1. with 0. using eqf

external externalPow : Float -> Float -> Float
let pow = lam x. lam y. externalPow x y
utest pow 3. 2. with 9. using eqf
