
include "math-ext.mc"
include "bool.mc"

-- Binomial and Bernoulli
external externalBinomialLogPmf : Int -> Float -> Int -> Float
external externalBinomialSample ! : Float -> Int -> Int
let binomialPmf = lam p:Float. lam n:Int. lam x:Int. exp (externalBinomialLogPmf x p n)
let binomialLogPmf = lam p:Float. lam n:Int. lam x:Int. externalBinomialLogPmf x p n
let binomialSample = lam p:Float. lam n:Int. externalBinomialSample p n
let bernoulliPmf = lam p:Float. lam x:Int. if eqi x 0 then subf 1. p else p
let bernoulliLogPmf = lam p:Float. lam x:Int. log (bernoulliPmf p x)
let bernoulliSample = lam p:Float. externalBinomialSample p 1

-- Beta
external externalBetaLogPdf : Float -> Float -> Float -> Float
external externalBetaSample ! : Float -> Float -> Float
let betaPdf = lam a:Float. lam b:Float. lam x:Float. exp (externalBetaLogPdf x a b)
let betaLogPdf = lam a:Float. lam b:Float. lam x:Float. externalBetaLogPdf x a b
let betaSample = lam a:Float. lam b:Float. externalBetaSample a b


mexpr

-- Functions for testing floats. Should perhaps be in another library.
let maxf = lam r. lam l. if gtf r l then r else l in
let absf = lam f. maxf f (negf f) in
let eqfApprox = lam epsilon. lam r. lam l.
  if leqf (absf (subf r l)) epsilon then true else false in
let _eqf = eqfApprox 1e-11 in

-- Test functions for ranges
let intRange = lam lower. lam upper. lam r. lam l.
  and (and (leqi r upper) (geqi r lower)) (and (leqi l upper) (geqi l lower)) in
let floatRange = lam lower. lam upper. lam r. lam l.
  and (and (leqf r upper) (geqf r lower)) (and (leqf l upper) (geqf l lower)) in

-- Testing Binomial and Bernoulli
utest binomialPmf 0.7 20 15 with 0.17886305057 using _eqf in
utest exp (binomialLogPmf 0.5 40 20) with 0.12537068762 using _eqf in
utest binomialSample 0.7 20 with 0 using intRange 0 20 in
utest bernoulliPmf 0.3 0 with 0.7 using _eqf in
utest exp (bernoulliLogPmf 0.6 1) with 0.6 using _eqf in
utest bernoulliSample 0.6 with 0 using intRange 0 1 in

-- Testing Beta
utest betaPdf 2. 2. 0.5 with 1.5 using _eqf in
utest exp (betaLogPdf 2. 5. 0.2) with 2.4576 using _eqf in
utest betaSample 2. 2. with 0. using floatRange 0. 1. in


()
