
include "benchmarkcommon.mc"
include "bool.mc"
include "common.mc"
include "math.mc"

include "rand_sample_n.ml"

-- Generates a uniformly random floating point number in the range [0,1)
let randFloatUniform: () -> Float = lam.
  let upperbound = 1073741823 in
  let x = randIntU 0 upperbound in
  divf (int2float x) (int2float upperbound)

-- Generates a sequence of randomly sampled floats from N(0,1)
let randFloatGaussBoxMullerMany: Int -> [Float] = lam count.
  recursive let generate = lam acc. lam i.
    if eqi i count then
      acc -- even basecase
    else -- continue
    let u1 = randFloatUniform () in
    let u2 = randFloatUniform () in
    let r = sqrt (negf (mulf 2.0 (log u1))) in
    let theta = mulf (mulf 2.0 pi) u2 in
    let z1 = mulf r (cos theta) in
    if eqi (addi i 1) count then
      cons z1 acc -- odd basecase
    else
      let z2 = mulf r (sin theta) in -- (z2 is independent from z1)
      generate (cons z1 (cons z2 acc)) (addi i 2)
  in
  generate [] 0

-- Generates/samples a single normally distributed float from N(0,1)
let randFloatGaussBoxMuller: () -> Float = lam.
  get (randFloatGaussBoxMullerMany 1) 0

mexpr
bc_repeat (lam. randFloatGaussBoxMullerMany n)

