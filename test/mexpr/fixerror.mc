// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test fixpoint usages

// Mutual recursion
let odd = fix (lam odd. lam even. lam n.
    if eqi n 1
    then true
    else even odd (subi n 1)
) in
let even = fix (lam even. lam odd. lam n.
    if eqi n 0
    then true
    else if lti n 0
    then false
    else odd even (subi n 1)
) in
utest even odd 20 with true in
utest even odd 27 with false in
utest odd even 41 with true in
utest odd even 42 with false in


// Errors (cannot execute the actual error in the test suite)
utest if false then error "message" else 0 with 0 in

()
