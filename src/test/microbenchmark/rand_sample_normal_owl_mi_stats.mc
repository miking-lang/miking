
include "benchmarkcommon.mc"
include "bool.mc"
include "common.mc"
include "math.mc"
include "ext/dist-ext.mc"

include "rand_sample_n.mc"

-- Generates a sequence of randomly sampled floats from N(0,1)
let randFloatGaussBoxMullerMany: Int -> [Float] = lam count.
  recursive let generate = lam acc. lam i.
    if eqi i count then
      acc -- even basecase
    else -- continue
      let z1 = normalSample 0. 1. in
      generate (cons z1 acc) (addi i 1)
  in
  generate [] 0

mexpr
bc_repeat (lam. randFloatGaussBoxMullerMany n)

