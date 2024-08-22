include "float.mc"

let _eqf = eqfApprox 1e-15

external externalExp : Float -> Float
let exp = lam x: Float. externalExp x
utest exp 0. with 1. using eqf

external externalLog : Float -> Float
let log = lam x: Float. externalLog x
utest log (exp 7.) with 7. using eqf
utest exp (log 7.) with 7. using _eqf

external externalAtan : Float -> Float
let atan = lam x : Float. externalAtan x
utest atan 0. with 0. using eqf

let pi = mulf 4. (atan 1.)

external externalSin : Float -> Float
let sin = lam x : Float. externalSin x
utest sin (divf pi 2.) with 1. using eqf
utest sin 0. with 0. using eqf

external externalCos : Float -> Float
let cos = lam x : Float. externalCos x
utest cos (divf pi 2.) with 0. using _eqf
utest cos 0. with 1. using eqf

utest addf (mulf (sin 1.) (sin 1.)) (mulf (cos 1.) (cos 1.)) with 1.
using eqf

external externalAtan2 : Float -> Float -> Float
let atan2 = lam x : Float. lam y : Float. externalAtan2 x y
utest atan2 0. 1. with 0. using eqf

external externalPow : Float -> Float -> Float
let pow = lam x: Float. lam y: Float. externalPow x y
utest pow 3. 2. with 9. using eqf

external externalSqrt : Float -> Float
let sqrt: Float -> Float = lam x. externalSqrt x
utest sqrt 9. with 3. using eqf

external externalLogGamma : Float -> Float
let logGamma: Float -> Float = lam x. externalLogGamma x
utest logGamma 3. with log 2. using eqf

external externalLogCombination : Int -> Int -> Float
let logCombination: Int -> Int -> Float = lam n. lam c. externalLogCombination n c
utest logCombination 4 2 with log 6. using _eqf
