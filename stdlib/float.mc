include "bool.mc"

-- Infinity
let inf: Float = divf 1.0 0.0


-- Not a number
let nan: Float = mulf 0. inf


-- `isNaN a` is `true` if `a` is `nan`
let isNaN: Float -> Bool = lam a. if eqf a a then false else true

utest isNaN nan with true
utest isNaN inf with false


-- `maxf l r` returns the maximum of `l` and `r`. If either is `nan` it returns
-- `nan`.
let maxf: Float -> Float -> Float = lam l. lam r.
  if or (isNaN l) (isNaN r) then nan
  else
    if gtf l r then l else r

utest maxf 0. 0. with 0.
utest maxf 1. 0. with 1.
utest maxf 0. 1. with 1.
utest isNaN (maxf nan 0.) with true
utest isNaN (maxf 0. nan) with true
