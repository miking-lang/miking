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

let _eqf = eqfApprox 1e-6

utest maxf 0. 0. with 0. using _eqf
utest maxf 1. 0. with 1. using _eqf
utest maxf 0. 1. with 1. using _eqf

external exp : Float -> Float
utest exp 0. with 1. using _eqf

external atan : Float -> Float
utest atan 0. with 0. using _eqf

let pi = mulf 4. (atan 1.)

external sin : Float -> Float
utest sin (divf pi 2.) with 1. using _eqf
utest sin 0. with 0. using _eqf

external cos : Float -> Float
utest cos (divf pi 2.) with 0. using _eqf
utest cos 0. with 1. using _eqf

utest addf (mulf (sin 1.) (sin 1.)) (mulf (cos 1.) (cos 1.)) with 1.
using _eqf
