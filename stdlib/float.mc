include "bool.mc"

-- Infinity
let inf: Float = divf 1.0 0.0


-- Not a number
let nan: Float = mulf 0. inf


-- `isNaN a` is `true` if `a` is `nan`
let isNaN: Float -> Bool = lam a. if eqf a a then false else true

utest isNaN nan with true
utest isNaN inf with false
