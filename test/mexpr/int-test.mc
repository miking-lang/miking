-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Integer intrinsics
include "bool.mc"

mexpr

-- Ingerger literals
utest 1 with 1 in
utest 35 with 35 in
utest -35 with -35 in

-- Integer operations: add sub mul div mod
-- int -> int -> int
utest 10 with addi 6 4 in             -- addition
utest 20 with subi 30 10 in           -- subtraction
utest 33 with muli 3 11 in            -- multiplication
utest 4 with divi 9 2 in              -- division
utest 1 with modi 9 2 in              -- modulo

-- Integer negations
-- int -> int
utest 15 with addi 20 (negi 5) in
utest negi 1 with -1 in
utest negi -1 with 1 in
-- Integer comparison operators
-- int -> int -> bool
let neg = lam f. lam x. lam y. not (f x y) in
utest 4 with 10 using lti in          -- Less than <
utest 20 with 10 using neg lti in
utest 10 with 10 using neg lti in
utest 4 with 10 using leqi in         -- Less than or equal <=
utest 20 with 10 using neg leqi in
utest 10 with 10 using leqi in
utest 100 with 10 using gti in        -- Greater than >
utest 10 with 20 using neg gti in
utest 10 with 10 using neg gti in
utest 100 with 10 using geqi in       -- Greater than or equal >=
utest 10 with 20 using neg geqi in
utest 10 with 10 using geqi in
utest 100 with 10 using neg eqi in    -- Equal =
utest 10 with 20 using neg eqi in
utest 10 with 10 using eqi in
utest 100 with 10 using neqi in       -- Not equal !=
utest 10 with 20 using neqi in
utest 10 with 10 using neg neqi in


-- Bit-shifting operators
-- int -> int -> int
utest 12 with slli 3 2 in             -- shift left logical
utest negi 12 with slli (negi 6) 1 in
utest 3 with srli 24 3 in             -- shift right logical
utest negi 3 with srai (negi 24) 3 in -- shift right arithmetic

()
