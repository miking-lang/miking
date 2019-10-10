// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test floating-point number primitives and polymorphic primitives



// Boolean intrinsic functions
utest true with true in
utest false with false in
utest true with not false in
utest true with and true true in
utest false with and false true in
utest false with and true false in
utest false with and false false in
utest true with or true true in
utest true with or false true in
utest true with or true false in
utest false with or false false in


// Floating-point number intrinsics
utest 32.1 with 32.1 in
utest 0.01 with 1e-2 in
utest 0.032 with 3.2e-2 in
utest 1.10 with addf 1.0 0.1 in
utest 8.5 with subf 10.6 2.1 in
utest 2.2 with mulf 1.1 2.0 in
utest 10.2 with divf 20.4 2.0 in
utest negf 2.2 with negf 2.2 in

nop
