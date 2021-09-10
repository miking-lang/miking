
include "math-ext.mc"

external externalBinomialLogPmf : Int -> Float -> Int -> Float
let binomialLogPmf = lam p:Float. lam n:Int. lam x:Int. externalBinomialLogPmf x p n
let bernoulliPmf = lam p:Float. lam x:Int. if eqi x 0 then subf 1. p else p
let bernoulliLogPmf = lam p:Float. lam x:Int. log (bernoulliPmf p x)

mexpr

let maxf = lam r. lam l. if gtf r l then r else l in

let absf = lam f. maxf f (negf f) in

let eqfApprox = lam epsilon. lam r. lam l.
  if leqf (absf (subf r l)) epsilon then true else false in

let _eqf = eqfApprox 1e-11 in

utest exp (binomialLogPmf 0.7 1 0) with 0.3 using _eqf in
utest bernoulliPmf 0.3 0 with 0.7 using _eqf in
utest exp (bernoulliLogPmf 0.6 1) with 0.6 using _eqf in
()
