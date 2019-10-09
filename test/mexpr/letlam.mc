// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test string and char primitives


// lambda
utest (lam x. addi x 2) 3 with 5 in
utest (lam x. lam y. muli x y) 3 4 with 12 in

// let
let x = 10 in
utest x with 10 in

let y = addi x 5 in
utest y with 15 in

let f1 = lam x. muli y x in
let y = f1 (addi 2 1) in
utest y with 45 in

let f2 = lam x. lam y. addi x y in
utest f2 2 3 with 5 in

nop
