
include "math-ext.mc"
include "bool.mc"

-- Binomial and Bernoulli
external externalBinomialLogPmf : Int -> Float -> Int -> Float
external externalBinomialSample ! : Float -> Int -> Int
let binomialPmf = lam p:Float. lam n:Int. lam x:Int.
  exp (externalBinomialLogPmf x p n)
let binomialLogPmf = lam p:Float. lam n:Int. lam x:Int.
  externalBinomialLogPmf x p n
let binomialSample = lam p:Float. lam n:Int.
  externalBinomialSample p n
let bernoulliPmf = lam p:Float. lam x:Int.
  if eqi x 0 then subf 1. p else p
let bernoulliLogPmf = lam p:Float. lam x:Int.
  log (bernoulliPmf p x)
let bernoulliSample = lam p:Float.
  externalBinomialSample p 1

-- Beta
external externalBetaLogPdf : Float -> Float -> Float -> Float
external externalBetaSample ! : Float -> Float -> Float
let betaPdf = lam a:Float. lam b:Float. lam x:Float.
  exp (externalBetaLogPdf x a b)
let betaLogPdf = lam a:Float. lam b:Float. lam x:Float.
  externalBetaLogPdf x a b
let betaSample = lam a:Float. lam b:Float.
  externalBetaSample a b

-- Gaussian
external externalGaussianLogPdf : Float -> Float -> Float -> Float
external externalGaussianSample ! : Float -> Float -> Float
let gaussianPdf = lam mu:Float. lam sigma:Float. lam x:Float.
  exp (externalGaussianLogPdf x mu sigma)
let gaussianLogPdf = lam mu:Float. lam sigma:Float. lam x:Float.
  externalGaussianLogPdf x mu sigma
let gaussianSample = lam mu:Float. lam sigma:Float.
  externalGaussianSample mu sigma

-- Multinomial and Categorical
external externalMultinomialLogPmf : [Int] -> [Float] -> Float
external externalMultinomialSample ! : Int -> [Float] -> [Int]
external externalCategoricalSample ! : [Float] -> Int
let multinomialLogPmf : [Float] -> [Int] -> Float =
  lam ps. lam ns. externalMultinomialLogPmf ns ps
let multinomialPmf : [Float] -> [Int] -> Float =
  lam ps. lam ns. exp (externalMultinomialLogPmf ns ps)
let categoricalLogPmf : [Float] -> Int -> Float =
  lam ps. lam x. log (get ps x)
let categoricalPmf : [Float] -> Int -> Float =
  lam ps. lam x. get ps x
let multinomialSample : [Float] -> Int -> [Int] =
  lam ps. lam n. externalMultinomialSample n ps
let categoricalSample : [Float] -> Int =
  lam ps. externalCategoricalSample ps


-- Uniform (continuous)
external uniformSample ! : Unit -> Float

-- Random (discrete)
external externalRandomSample ! : Int -> Int -> Int
let randomSample = lam a:Int. lam b:Int.
  externalRandomSample a b


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

-- Testing Gaussian
utest gaussianPdf 0. 0.4472 0. with 0.892089178 using _eqf in
utest exp (gaussianLogPdf 2. 1. 2.) with 0.398942280401 using _eqf in
utest gaussianSample 0. 0.2 with 0. using lam. lam. true in

-- Testing Multinomial and Categorical
utest multinomialLogPmf [0.1, 0.3, 0.6] [0,1,0] with log 0.3 using _eqf in
utest multinomialPmf [0.1, 0.3, 0.6] [0,0,1] with 0.6 using _eqf in
utest multinomialPmf [0.1, 0.3, 0.6] [0,2,3] with 0.1944 using _eqf in
utest categoricalLogPmf [0.3, 0.2, 0.5] 2 with log 0.5 using _eqf in
utest categoricalPmf [0.1, 0.3, 0.6] 2 with 0.6 using _eqf in
utest categoricalPmf [0.1, 0.3, 0.6] 1 with 0.3 using _eqf in
utest multinomialSample [0.2, 0.8] 3 with [] using
  lam r. lam l. match r with [v1,v2] then eqi (addi v1 v2) 3 else false in
utest categoricalSample [0.1, 0.4, 0.2, 0.3] with 0 using intRange 0 3 in

-- Testing Uniform
utest uniformSample () with 0. using floatRange 0. 1. in

-- Testing Random
utest randomSample 3 8 with 3 using intRange 3 8 in

()
