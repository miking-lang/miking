// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test floating-point number primitives and polymorphic primitives

mexpr


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



()
