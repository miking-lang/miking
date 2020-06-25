-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Integer intrinsics

mexpr

-- Ingerger literals
utest 1 with 1 in
utest 35 with 35 in

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
utest negi 1 with negi 1 in

-- Integer comparison operators
-- int -> int -> bool
utest true with lti 4 10 in           -- Less than <
utest false with lti 20 10 in
utest false with lti 10 10 in
utest true with leqi 4 10 in          -- Less than and equal <=
utest false with leqi 20 10 in
utest true with leqi 10 10 in
utest true with gti 100 10 in         -- Greater than >
utest false with gti 10 20 in
utest false with gti 10 10 in
utest true with geqi 100 10 in        -- Greater than and equal >=
utest false with geqi 10 20 in
utest true with geqi 10 10 in
utest false with eqi 100 10 in        -- Equal =
utest false with eqi 10 20 in
utest true with eqi 10 10 in
utest true with neqi 100 10 in        -- Not equal !=
utest true with neqi 10 20 in
utest false with neqi 10 10 in

-- Bit-shifting operators
-- int -> int -> int
utest 12 with slli 3 2 in             -- shift left logical
utest negi 12 with slli (negi 6) 1 in
utest 3 with srli 24 3 in             -- shift right logical
utest negi 3 with srai (negi 24) 3 in -- shift right arithmetic


-- Arity of intrinsic functions
utest arity with arity in
utest arity addi with 2 in
utest arity arity with 1 in
utest arity subf with 2 in
utest arity negi with 1 in

()
