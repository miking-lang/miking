// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test integer primitives

mexpr

// Literals
utest 1 with 1 in
utest 35 with 35 in
utest negi 1 with negi 1 in

// Integer intrinsic functions
utest 10 with addi 6 4 in            // Integer addition
utest 20 with subi 30 10 in          // Integer subtractioin
utest 33 with muli 3 11 in           // Integer multiplication
utest 4 with divi 9 2 in             // Integer division
utest 1 with modi 9 2 in             // Integer modulo
utest 15 with addi 20 (negi 5) in    // Integer negation
utest true with lti 4 10 in          // Less than <
utest false with lti 20 10 in
utest false with lti 10 10 in
utest true with leqi 4 10 in         // Less than and equal <=
utest false with leqi 20 10 in
utest true with leqi 10 10 in
utest true with gti 100 10 in        // Greater than >
utest false with gti 10 20 in
utest false with gti 10 10 in
utest true with geqi 100 10 in       // Greater than and equal >=
utest false with geqi 10 20 in
utest true with geqi 10 10 in
utest false with eqi 100 10 in       // Equal =
utest false with eqi 10 20 in
utest true with eqi 10 10 in
utest true with neqi 100 10 in       // Not equal !=
utest true with neqi 10 20 in
utest false with neqi 10 10 in
utest arity with arity in            // Arity of constants
utest arity addi with 2 in
utest arity arity with 1 in
utest arity subf with 2 in
utest arity negi with 1 in


()
