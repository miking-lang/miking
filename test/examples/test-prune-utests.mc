/-
  This program tests external dependent utest removal. To test it evaluate it
  using `boot eval --test`. All test that should remain should fail.
-/

include "math.mc"


-- Should be removed
utest exp (log 1.) with 1.

let myexp = exp

-- Should be removed
utest myexp (log 1.) with 1.

-- Should remain
utest
  let x = myexp (log 1.) in
  1
with 0

-- Should remain
utest
  -- Should be removed
  utest exp (log 1.) with 1. in
  2
with 0

-- Should be removed
utest
  match exp with f then
    f 0.
  else never
with 1.
