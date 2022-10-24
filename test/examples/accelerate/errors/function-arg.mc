-- Using accelerate within a function. This cannot be accelerated because the
-- parameter f, which has an arrow type, must be passed as a parameter to the
-- accelerate function.

include "common.mc" -- printLn
include "string.mc" -- int2string

let accmapsum : (Int -> Int) -> [Int] -> Int = lam f. lam s.
  accelerate (foldl addi 0 (map f s))

mexpr

let s = accmapsum (addi 1) [1, 2, 3] in
printLn (int2string s)
