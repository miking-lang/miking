// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test floating-point comparisons and operations

// Floating-point number intrinsics
utest 32.1 with 32.1 in
utest 0.01 with 1e-2 in
utest 0.032 with 3.2e-2 in
utest 1.10 with addf 1.0 0.1 in
utest 8.5 with subf 10.6 2.1 in
utest 2.2 with mulf 1.1 2.0 in
utest 10.2 with divf 20.4 2.0 in
utest negf 2.2 with negf 2.2 in

// Floating-point operations
utest eqf 2.2 2.2 with true in
utest eqf 2.2 2.3 with false in

utest neqf 0.25 0.25 with false in
utest neqf 0.25 0.5 with true in

utest ltf 0.5 2.0 with true in
utest ltf 2.0 0.5 with false in
utest ltf 0.5 0.5 with false in

utest leqf 0.5 2.0 with true in
utest leqf 2.0 0.5 with false in
utest leqf 0.5 0.5 with true in

utest gtf 7.5 0.25 with true in
utest gtf 0.25 7.5 with false in
utest gtf 0.25 0.25 with false in

utest geqf 7.5 0.25 with true in
utest geqf 0.25 7.5 with false in
utest geqf 0.25 0.25 with true in

utest addf 1.0 2.0 with 3.0 in
utest addf 0.0 3.0 with 3.0 in
utest subf 7.0 1.0 with 6.0 in
utest subf 8.0 3.0 with 5.0 in
utest mulf 28.0 1.0 with 28.0 in
utest mulf 28.0 0.0 with 0.0 in
utest mulf 9.0 3.0 with 27.0 in
utest divf 5.0 5.0 with 1.0 in
utest divf 6.0 3.0 with 2.0 in
utest eqf (subf 3.0 5.0) (negf 2.0) with true in
utest eqf (subf 3.0 5.0) (negf 3.0) with false in

// powf3 x = x^3
let powf3 = lam x. mulf x (mulf x x) in
let taxicab2_1 = addf (powf3 1.0) (powf3 12.0) in
let taxicab2_2 = addf (powf3 9.0) (powf3 10.0) in
utest eqf taxicab2_1 taxicab2_2 with true in

utest string2float "42" with 42.0 in
utest string2float "3.14159" with 3.14159 in
utest string2float "3.2e-2" with 0.032 in
()
