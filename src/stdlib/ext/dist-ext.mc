include "math.mc"
include "bool.mc"
include "seq.mc"
include "ext/math-ext.mc"
include "float.mc"

-- Multinomial and Categorical
external externalMultinomialLogPmf : [Int] -> [Float] -> Float
external externalMultinomialSample ! : Int -> [Float] -> [Int]
external externalCategoricalSample ! : [Float] -> Int
let multinomialLogPmf : [Float] -> [Int] -> Float =
  lam ps. lam ns. externalMultinomialLogPmf ns ps
let multinomialPmf : [Float] -> [Int] -> Float =
  lam ps. lam ns. exp (externalMultinomialLogPmf ns ps)
let categoricalLogPmf : [Float] -> Int -> Float =
  lam ps. lam x.
  if geqi x (length ps) then negf inf else log (get ps x)
let categoricalPmf : [Float] -> Int -> Float =
  lam ps. lam x.
  if geqi x (length ps) then negf inf else get ps x
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

-- Pair distribution
let indexOfUnion = lam pairSets. lam u.
  recursive let helper = lam i.
    if eqi i (length pairSets) then negi 1
    else let v = get pairSets i in
      if eqSeq eqi v u then i else helper (addi i 1)
  in helper 0

let treeInferenceCategoricalPmf = lam p. lam pairSets. lam x.
  let idx = indexOfUnion pairSets x in
  if lti idx 0 then 0.0 else get p idx

let treeInferenceCategoricalLogPmf = lam p. lam pairSets. lam x. log (treeInferenceCategoricalPmf p pairSets x)
let treeInferenceCategoricalSample = lam p. lam pairSets.
  let index = categoricalSample p in
  let pair = get pairSets index in
  pair

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

-- Testing treeInferenceCategorical
let pairSetsTest = [[0,1],[1,2],[2,3]] in
let pTest = [0.2, 0.5, 0.3] in
-- indexOfUnion
utest indexOfUnion pairSetsTest [0,1] with 0 using eqi in
utest indexOfUnion pairSetsTest [1,2] with 1 using eqi in
utest indexOfUnion pairSetsTest [2,3] with 2 using eqi in
utest indexOfUnion pairSetsTest [9,9] with negi 1 using eqi in
-- 
utest treeInferenceCategoricalPmf pTest pairSetsTest [2,3] with 0.3 using _eqf in
utest treeInferenceCategoricalPmf pTest pairSetsTest [9,9] with 0.0 using _eqf in
utest treeInferenceCategoricalLogPmf pTest pairSetsTest [0,1] with log 0.2 using _eqf in
utest treeInferenceCategoricalLogPmf pTest pairSetsTest [9,9] with negf inf using eqf in
-- pairSample: result is one of the support pairs
utest let s = treeInferenceCategoricalSample pTest pairSetsTest in
  any (lam x. eqSeq eqi x s) pairSetsTest
with true in

()
