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
-- infinity and equal to itself. OPT(oerikss, 2024-04-18): For a faster `cmpf` you
-- should create an external to, e.g., OCamls `Float.compare which` uses an 
-- optimized C under the hood. 
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


-- `eqfApprox epsilon l r` has the same semantics as `eqf` but where `l` and `r`
-- are considered equal if l = r or |l - r| ≤ epsilon. Returns false if
-- `epsilon` is not a number greater than or equal to zero.
let eqfApprox = lam epsilon. lam l. lam r.
  if or (ltf epsilon 0.) (isNaN epsilon) then false
  else
    if (eqf l r) then
       -- handles the cases where `subf l r` is `nan`.
       true
    else leqf (absf (subf l r)) epsilon

utest 1. with 1.01 using eqfApprox 0.011
utest negf 1.0 with negf 1.009 using eqfApprox 0.01
utest 0.0 with 0.0  using (eqfApprox 0.)
utest eqfApprox 0.01 1.0 1.011 with false
utest 1. with 1.000009 using eqfApprox 0.00001
utest eqfApprox 0.00001 1.0 1.000011 with false
utest eqfApprox 0.01 inf inf with true
utest eqfApprox 0. inf inf with true
utest eqfApprox 0. (negf inf) (negf inf) with true
utest eqfApprox 0. nan 0. with false
utest eqfApprox 0. 0. nan with false
utest eqfApprox 0. nan nan with false
utest eqfApprox inf nan nan with false
utest eqfApprox inf inf 0. with true
utest eqfApprox inf 0. inf with true
utest eqfApprox inf inf (negf inf) with true


-- `cmpfApprox epsilon l r` has the same semantics as `cmpf` but where `l` and
-- `r` are considered equal if l = r or |l - r| ≤ epsilon. Gives an error if
-- `epsilon` is not a number greater than or equal to zero.
let cmpfApprox : Float -> Float -> Float -> Int =
  lam epsilon. lam l. lam r.
  if or (ltf epsilon 0.) (isNaN epsilon) then
    error "eqfApprox: Invalid input, epsilon must be a number greater than or equal to zero."
  else
    let lIsNaN = isNaN l in
    let rIsNaN = isNaN r in
    if and lIsNaN rIsNaN then 0
    else if lIsNaN then -1
    else if rIsNaN then 1
    else
      if eqfApprox epsilon l r then 0
      else if ltf l r then -1
      else 1

utest cmpfApprox 0.01 0. 0. with 0
utest cmpfApprox 0.01 1. 0. with 1
utest cmpfApprox 0.01 0. 1. with -1
utest cmpfApprox 0.01 inf inf with 0
utest cmpfApprox 0.01 (negf inf) (negf inf) with 0
utest cmpfApprox 0.01 inf inf with 0
utest cmpfApprox 0.01 (negf inf) 0. with -1
utest cmpfApprox 0.01 0. (negf inf) with 1
utest cmpfApprox 0.01 nan nan with 0
utest cmpfApprox 0.01 nan (negf inf) with -1
utest cmpfApprox 0.01 (negf inf) nan with 1
