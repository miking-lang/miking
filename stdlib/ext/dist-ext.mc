include "math.mc"
include "bool.mc"

-- Gamma
external externalGammaLogPdf : Float -> Float -> Float -> Float
external externalGammaSample ! : Float -> Float -> Float
let gammaPdf = lam shape:Float. lam scale:Float. lam x:Float.
  exp (externalGammaLogPdf x shape scale)
let gammaLogPdf = lam shape:Float. lam scale:Float. lam x:Float.
  externalGammaLogPdf x shape scale
let gammaSample = lam shape:Float. lam scale:Float.
  externalGammaSample shape scale

-- Binomial and Bernoulli
external externalBinomialLogPmf : Int -> Float -> Int -> Float
external externalBinomialSample ! : Float -> Int -> Int
let binomialPmf = lam p:Float. lam n:Int. lam x:Int.
  exp (externalBinomialLogPmf x p n)
let binomialLogPmf = lam p:Float. lam n:Int. lam x:Int.
  externalBinomialLogPmf x p n
let binomialSample = lam p:Float. lam n:Int.
  externalBinomialSample p n
let bernoulliPmf = lam p:Float. lam x:Bool.
  if x then p else subf 1. p
let bernoulliLogPmf = lam p:Float. lam x:Bool.
  log (bernoulliPmf p x)
let bernoulliSample = lam p:Float.
  if eqi 1 (externalBinomialSample p 1) then true else false

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

-- Dirichlet
external externalDirichletLogPdf : [Float] -> [Float] -> Float
external externalDirichletSample : [Float] -> [Float]
let dirichletLogPdf : [Float] -> [Float] -> Float =
  lam alpha. lam xs. if eqfApprox 1e-15 (foldl addf 0. xs) 1. then externalDirichletLogPdf xs alpha else negf inf
let dirichletPdf : [Float] -> [Float] -> Float =
  lam alpha. lam xs. exp (externalDirichletLogPdf xs alpha)
let dirichletSample : [Float] -> [Float] =
  lam alpha. externalDirichletSample alpha

-- Uniform (continuous between a and b)
external externalUniformContinuousSample ! : Float -> Float -> Float
let uniformContinuousSample = lam a. lam b.
  externalUniformContinuousSample a b
let uniformContinuousLogPdf = lam a. lam b. lam x.
  if geqf x a then
    if leqf x b then subf (log 1.0) (log (subf b a))
    else 0.
  else 0.
let uniformContinuousPdf = lam a. lam b. lam x.
  if geqf x a then
    if leqf x b then divf 1.0 (subf b a)
    else 0.
  else 0.

-- Uniform on 0 1
let uniformSample : () -> Float = lam. uniformContinuousSample 0. 1.

-- Random (discrete)
external externalUniformDiscreteSample ! : Int -> Int -> Int
let uniformDiscreteSample = lam a:Int. lam b:Int.
  externalUniformDiscreteSample a b
let uniformDiscreteLogPdf : Int -> Int -> Int -> Float = lam a. lam b. lam x.
  if geqi x a then
    if leqi x b then subf (log 1.0) (log (int2float (addi 1 (subi b a))))
    else 0.
  else 0.
let uniformDiscretePdf : Int -> Int -> Int -> Float = lam a. lam b. lam x.
  if geqi x a then
    if leqi x b then divf 1.0 (int2float (addi 1 (subi b a)))
    else 0.
  else 0.

-- Poisson
let poissonLogPmf = lam lambda:Float. lam x:Int.
  subf (subf (mulf (int2float x) (log lambda)) lambda) (logFactorial x)
let poissonPmf = lam lambda:Float. lam x:Int.
  exp (poissonLogPmf lambda x)
-- Simple but inefficient algorithm for drawing from Poisson. Translated from
-- numpy C source code and originally from Knuth according to Wikipedia.
-- OPT(dlunde,2022-05-16): We want to use an external for this eventually.
let poissonSample = lam lambda:Float.
  let enlam = exp (negf lambda) in
  let x = 0 in
  let prod = 1. in
  recursive let rec = lam x. lam prod.
    let u = uniformSample () in
    let prod = mulf prod u in
    if gtf prod enlam then rec (addi x 1) prod
    else x
  in rec x prod

-- Add exponential
external externalExponentialSample ! : Float -> Float
let exponentialSample = lam lambda:Float.
  externalExponentialSample lambda
let exponentialLogPdf : Float -> Float -> Float = lam lambda. lam x.
  subf (log lambda) (mulf lambda x)
let exponentialPdf : Float -> Float -> Float = lam lambda. lam x.
  exp (exponentialLogPdf lambda x)

-- Negative Binomial
let negativeBinomialSample : Int -> Float -> Int = lam n. lam p.
  poissonSample (externalGammaSample (int2float n) (divf (subf 1. p) p))
let negativeBinomialLogPmf : Int -> Float -> Int -> Float = lam n. lam p. lam x.
  subf (addf (log (int2float n)) (externalBinomialLogPmf x (subf 1. p) (addi x n))) (log (int2float (addi n x)))
let negativeBinomialPmf: Int -> Float -> Int -> Float = lam n. lam p. lam x.
  exp (negativeBinomialLogPmf n p x)

-- Geometric
let geometricSample : Float -> Int = lam p.
  negativeBinomialSample 1 p
let geometricLogPmf : Float -> Int -> Float = lam p. lam x.
  addf (mulf (int2float x) (log (subf 1. p))) (log p)
let geometricPmf : Float -> Int -> Float = lam p. lam x.
  exp (geometricLogPmf p x)

-- Lomax
external externalLomaxLogPdf : Float -> Float -> Float -> Float
external externalLomaxSample ! : Float -> Float -> Float
let lomaxSample = lam shape: Float. lam scale: Float.
  externalLomaxSample shape scale
let lomaxLogPdf:Float -> Float -> Float -> Float = lam shape. lam scale. lam x.
  if ltf x 0. then negf inf else
  let lhs = subf (log shape) (log scale)  in
  let rhs = mulf (log (addf (divf x scale) 1.)) (addf shape 1.) in
  subf lhs rhs
let lomaxPdf = lam shape: Float. lam scale: Float. lam x:Float.
  exp (lomaxLogPdf shape scale x)

-- Beta binomial
let betabinSample = lam n:Int. lam a: Float. lam b: Float.
  let p = betaSample a b in
  binomialSample p n

let betabinLogPmf:Int -> Float -> Float -> Int -> Float = lam n. lam a. lam b. lam x.
  if gti x n then negf inf else
  let lbeta1 = addf (subf (logGamma (addf a (int2float x))) (logGamma (addf (int2float n) (addf a b)))) (logGamma (addf b (int2float (subi n x))))  in
  let lbeta2 = addf (subf (logGamma a) (logGamma (addf a b))) (logGamma b)  in
  let lcomb = (logCombination n x) in
  addf lcomb (subf lbeta1 lbeta2)

let betabinPmf = lam n:Int. lam a: Float. lam b: Float. lam x:Int.
  exp (betabinLogPmf n a b x)

-- Seed
external externalSetSeed ! : Int -> ()
let setSeed : Int -> () = lam seed.

  -- VERY important to also call this intrinsic here. Otherwise, the compiled code
  -- _self-initializes the seed_ at the first call to the intrinsic randIntU.
  randSetSeed seed;

  externalSetSeed seed

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

-- Testing Gamma
utest gammaPdf 1. 2. 1. with 0.303265329856 using _eqf in
utest exp (gammaLogPdf 2. 3. 1.) with 0.0796145900638 using _eqf in
utest gammaSample 1. 2. with 1. using floatRange 0. inf in

-- Testing Binomial and Bernoulli
utest binomialPmf 0.7 20 15 with 0.17886305057 using _eqf in
utest exp (binomialLogPmf 0.5 40 20) with 0.12537068762 using _eqf in
utest binomialSample 0.7 20 with 0 using intRange 0 20 in
utest bernoulliPmf 0.3 false with 0.7 using _eqf in
utest exp (bernoulliLogPmf 0.6 true) with 0.6 using _eqf in
utest bernoulliSample 0.6 with false using lam. lam. true in

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
  lam l. lam r. match l with [v1,v2] then eqi (addi v1 v2) 3 else false in
utest categoricalSample [0.1, 0.4, 0.2, 0.3] with 0 using intRange 0 3 in

-- Testing Dirichlet
utest dirichletLogPdf [1.5, 1.5, 1.5] [0.5, 0.25, 0.25]
  with 1.08321533235 using _eqf in
utest dirichletPdf [1.0, 1.0, 2.0] [0.01, 0.01, 0.98] with 5.88 using _eqf in
utest dirichletSample [5.0, 5.0, 5.0] with [0.] using
  lam l. lam r. _eqf (foldl addf 0. l) 1.0 in

-- Testing Continuous uniform
utest uniformContinuousSample 1.0 2.0 with 0. using floatRange 0. 2. in
utest exp (uniformContinuousLogPdf 1.0 2.0 1.5) with 1.0 using _eqf in
utest uniformContinuousPdf 1.0 2.0 1.5 with 1.0 using _eqf in

-- Testing (0,1)-uniform
utest uniformSample () with 0. using floatRange 0. 1. in

-- Testing Discrete uniform
utest uniformDiscreteSample 3 8 with 3 using intRange 3 8 in
utest exp (uniformDiscreteLogPdf 1 2 1) with 0.5 using _eqf in
utest uniformDiscretePdf 1 2 1 with 0.5 using _eqf in

-- Testing Poisson
utest poissonPmf 2.0 2 with 0.270670566473 using _eqf in
utest exp (poissonLogPmf 3.0 2) with 0.224041807655 using _eqf in
utest poissonSample 2.0 with 3 using intRange 0 100000 in

-- Testing Exponential
utest exponentialSample 1.0 with 0. using floatRange 0. inf in
utest exp (exponentialLogPdf 1.0 2.0) with 0.135335283237 using _eqf in
utest exponentialPdf 2.0 2.0 with 0.0366312777775 using _eqf in

-- Testing Negative Binomial
utest exp (negativeBinomialLogPmf 6 0.3 1) with 0.0030618 using _eqf in
utest negativeBinomialPmf 6 0.3 3 with 0.014002632 using _eqf in
utest exp (negativeBinomialLogPmf 6 0.3 5) with 0.03087580356 using _eqf in
utest negativeBinomialPmf 6 0.3 7 with 0.0475487374824 using _eqf in
utest negativeBinomialSample 6 0.3 with 0 using geqi in

-- Testing Geometric
utest geometricPmf 0.3 0 with 0.3 using _eqf in
utest exp (geometricLogPmf 0.3 1) with 0.21 using _eqf in
utest geometricPmf 0.3 2 with 0.147 using _eqf in
utest exp (geometricLogPmf 0.3 3) with 0.1029 using _eqf in
utest geometricSample 0.3 with 0 using geqi in

-- Testing Beta-Binomial
utest betabinLogPmf 5 1. 1. 2 with -1.79175946923 using _eqf in
utest exp (betabinLogPmf 5 1. 1. 3) with 0.166666666667 using _eqf in
utest betabinPmf 5 1. 1. 3 with 0.166666666667 using _eqf in
utest betabinSample 20 1. 1. with 0 using intRange 0 20 in

-- Testing seed
utest setSeed 0; uniformSample (); uniformSample ()
with setSeed 0; uniformSample (); uniformSample () in
utest setSeed 0; gaussianSample 0. 1.; gaussianSample 0. 1.
with  setSeed 0; gaussianSample 0. 1.; gaussianSample 0. 1. in
utest setSeed 0; uniformSample (); gaussianSample 0. 1.
with  setSeed 0; uniformSample (); gaussianSample 0. 1. in
utest setSeed 0; gaussianSample 0. 1.; gaussianSample 0. 1.; uniformSample ()
with  setSeed 0; gaussianSample 0. 1.; gaussianSample 0. 1.; uniformSample () in

()
