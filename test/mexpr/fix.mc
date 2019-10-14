// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test fixpoint usages

// Separate fix-point
let fact_abs = (lam fact. lam n.
    if eqi n 0
    then 1
    else muli n (fact (subi n 1))
) in

let fact = fix fact_abs in

utest fact 5 with 120 in
utest fact 0 with 1 in

// Mutual recursion
let odd_abs = lam odd. lam even. lam n.
    if eqi n 1
    then true
    else if lti n 1
    then false
    else even odd (subi n 1)
in
let even_abs = lam even. lam odd. lam n.
    if eqi n 0
    then true
    else if lti n 0
    then false
    else odd even (subi n 1)
in

let odd = (fix odd_abs) (fix even_abs) in
let even = (fix even_abs) (fix odd_abs) in

utest even 20 with true in
utest even 27 with false in
utest odd 41 with true in
utest odd 42 with false in

()