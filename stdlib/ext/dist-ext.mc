


external externalBinomialLogPmf : Int -> Float -> Int -> Float
let binomialLogPmf = lam p:Float. lam n:Int. lam x:Int. externalBinomialLogPmf x p n
let bernoulliLogPmf = lam p:Float. lam x:Int. externalBinomialLogPmf x p 1

mexpr

let maxf = lam r. lam l. if gtf r l then r else l in

let absf = lam f. maxf f (negf f) in

let eqfApprox = lam epsilon. lam r. lam l.
  if leqf (absf (subf r l)) epsilon then true else false in

let _eqf = eqfApprox 1e-11 in

utest binomialLogPmf 0.7 1 0 with negf 1.20397280433 using _eqf in
utest bernoulliLogPmf 0.6 1 with negf 0.510825623766 using _eqf in
()
