include "math.mc"

-- TODO(oerikss, 2021-04-27) If we don't define this alias dead code elimination
-- will remove eqfApprox. This is a bug and the code elimination should be
-- updated to check if functions are used in tests.
let _eqf = eqfApprox 1e-6

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
