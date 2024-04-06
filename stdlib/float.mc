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


-- `minf l r` returns the minimum of `l` and `r`. If either is `nan` it returns
-- `nan`. If `minf 0. -0.` and `minf -0. 0.` returns `-0.`.
let minf: Float -> Float -> Float = lam r. lam l.
  if or (isNaN l) (isNaN r) then nan
  else
    if ltf r l then r else l

utest minf 0. 0. with 0.
utest minf 1. 0. with 0.
utest minf 0. 1. with 0.
utest isNaN (minf nan 0.) with true
utest isNaN (minf 0. nan) with true


-- `absf a` returns the absolute value of `a` or `nan` if `a` is `nan`.
let absf: Float -> Float = lam f. maxf f (negf f)

utest absf 0. with 0. using eqf
utest absf 1. with 1. using eqf
utest absf -1. with 1. using eqf
utest absf -0. with 0. using eqf
utest isNaN (absf nan) with true


-- `cmpf l r` compares `l` and `r`. `cmpf l r = -1` if l < r, `cmpf l r = 1` if
-- l > r, and `cmpf l r = 0` if l = r. `nan` is considered smaller than negative
-- infinity and equal to itself.
let cmpf: Float -> Float -> Int = lam l. lam r.
  let lIsNaN = isNaN l in
  let rIsNaN = isNaN r in
  if and lIsNaN rIsNaN then 0
  else if lIsNaN then -1
  else if rIsNaN then 1
  else
    if ltf l r then -1 else if gtf l r then 1 else 0

utest cmpf 0. 0. with 0
utest cmpf 1. 0. with 1
utest cmpf 0. 1. with -1
utest cmpf inf inf with 0
utest cmpf (negf inf) (negf inf) with 0
utest cmpf inf inf with 0
utest cmpf (negf inf) 0. with -1
utest cmpf 0. (negf inf) with 1
utest cmpf nan nan with 0
utest cmpf nan (negf inf) with -1
utest cmpf (negf inf) nan with 1
