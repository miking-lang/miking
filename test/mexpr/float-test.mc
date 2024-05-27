-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Floating-point number intrinsics

include "bool.mc"
include "math.mc"

mexpr

-- Floating-point number literals
utest 32.1 with 32.1 using eqf in
utest -32.1 with -32.1 using eqf in
utest 0.01 with 1e-2 using eqf in
utest 0.032 with 3.2e-2 using eqf in
utest 320.0 with 3.2e+2 using eqf in
utest 1.10 with addf 1.0 0.1 using eqf in
utest 8.5 with subf 10.6 2.1 using eqf in
utest 2.2 with mulf 1.1 2.0 using eqf in
utest 10.2 with divf 20.4 2.0 using eqf in

-- Floating-point number operations
-- Float -> Float -> Float
utest addf 1.0 2.0 with 3.0 using eqf in           -- addition
utest addf 0.0 3.0 with 3.0 using eqf in
utest subf 7.0 1.0 with 6.0 using eqf in           -- subtraction
utest subf 8.0 3.0 with 5.0 using eqf in
utest mulf 28.0 1.0 with 28.0 using eqf in         -- multiplication
utest mulf 28.0 0.0 with 0.0 using eqf in
utest mulf 9.0 3.0 with 27.0 using eqf in
utest divf 5.0 5.0 with 1.0 using eqf in           -- division
utest divf 6.0 3.0 with 2.0 using eqf in

-- Negation
-- Float -> Float
utest negf 2.2 with -2.2 using eqf in
utest negf -2.2 with 2.2 using eqf in

-- Floating-point operations
-- Float -> Float -> Bool
let neg = lam f. lam x. lam y. not (f x y) in
utest 0.5 with 2.0 using ltf in          -- less than (float)
utest 2.0 with 0.5 using neg ltf in
utest 0.5 with 0.5 using neg ltf in
utest 0.5 with 2.0 using leqf in         -- less equal (float)
utest 2.0 with 0.5 using neg leqf in
utest 0.5 with 0.5 using leqf in
utest 7.5 with 0.25 using gtf in         -- greater than (float)
utest 0.25 with 7.5 using neg gtf in
utest 0.25 with 0.25 using neg gtf in
utest 7.5 with 0.25 using geqf in        -- greater than or equal (float)
utest 0.25 with 7.5 using neg geqf in
utest 0.25 with 0.25 using geqf in
utest 2.2 with 2.2 using eqf in          -- equal (float)
utest 2.2 with 2.3 using neg eqf in
utest subf 3.0 5.0 with negf 2.0
      using eqf in
utest subf 3.0 5.0 with negf 3.0
      using neg eqf in
utest 0.25 with 0.25 using neg neqf in   -- not equal (float)
utest 0.25 with 0.5 using neqf in


-- Conversion from Float to Int
-- Float->Int
utest floorfi 0.0 with 0 in              -- floor
utest floorfi 3.8 with 3 in
utest floorfi 3.0 with 3 in
utest floorfi 2.999 with 2 in
utest floorfi (negf 1.75) with negi 2 in
utest floorfi (negf 1.25) with negi 2 in
utest floorfi (negf 0.975) with negi 1 in

utest ceilfi 0.0 with 0 in               -- ceiling
utest ceilfi 7.3 with 8 in
utest ceilfi 7.75 with 8 in
utest ceilfi 8.0 with 8 in
utest ceilfi 8.001 with 9 in
utest ceilfi (negf 5.0) with negi 5 in
utest ceilfi (negf 5.75) with negi 5 in
utest ceilfi (negf 6.25) with negi 6 in

utest roundfi 0.0 with 0 in              -- round
utest roundfi 1.0 with 1 in
utest roundfi 1.25 with 1 in
utest roundfi 1.5 with 2 in
utest roundfi 0.75 with 1 in
utest roundfi (negf 2.4) with negi 2 in
utest roundfi (negf 2.0) with negi 2 in
utest roundfi (negf 2.5) with negi 3 in

-- Conversion from Float to Int
-- Int-> Float
utest int2float 0 with 0.0 using eqf in
utest int2float 1 with 1.0 using eqf in
utest int2float 17 with 17.0 using eqf in
utest int2float (negi 10) with negf 10.0 using eqf in

-- Conversion from String to Float
utest stringIsFloat "42" with true in
utest stringIsFloat "3.14159" with true in
utest stringIsFloat "3.2e-2" with true in
utest stringIsFloat "3.2E-2" with true in
utest stringIsFloat "-3.2e2" with true in
utest stringIsFloat "a" with false in
-- String -> Float
utest string2float "42" with 42.0 using eqf in
utest string2float "3.14159" with 3.14159 using eqf in
utest string2float "3.2e-2" with 0.032 using eqf in
utest string2float "3.2e2" with 320.0 using eqf in
utest string2float "3e+2" with 300.0 using eqf in
-- Float -> String
utest float2string 5.0e+25 with "5e+25" in
utest float2string (negf 5.0e+25) with "-5e+25" in
utest float2string (5.0e-5) with "5e-05" in
utest float2string (negf 5.0e-5) with "-5e-05" in

-- Test: computing with floats
-- powf3 x = x^3
let powf3 = lam x. mulf x (mulf x x) in
let taxicab2_1 = addf (powf3 1.0) (powf3 12.0) in
let taxicab2_2 = addf (powf3 9.0) (powf3 10.0) in
utest taxicab2_1 with taxicab2_2 using eqf in

()
