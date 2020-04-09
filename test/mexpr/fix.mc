// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test fixpoint usages

mexpr

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

-- Generalized fixpoint for mutual recursion-----------------------------------
let head = lam seq. get seq 0 in
let tail = lam seq. slice seq 1 (length seq) in

let map = fix (lam map. lam f. lam seq.
  if eqi (length seq) 0 then []
  else cons (f (head seq)) (map f (tail seq))
) in

-- Thanks Oleg Kiselyov
let fix_mut =
  lam l. fix (lam self. lam l. map (lam li. lam x. li (self l) x) l) l
in

let odd2_abs = lam funs. lam n.
    let odd = get funs 0 in
    let even = get funs 1 in
    if eqi n 1
    then true
    else if lti n 1
    then false
    else even (subi n 1)
in
let even2_abs = lam funs. lam n.
    let odd = get funs 0 in
    let even = get funs 1 in
    if eqi n 0
    then true
    else if lti n 0
    then false
    else odd (subi n 1)
in

let odd_even = fix_mut [odd2_abs, even2_abs] in
let odd2 = get odd_even 0 in
let even2 = get odd_even 1 in

utest even2 20 with true in
utest even2 27 with false in
utest odd2 41 with true in
utest odd2 42 with false in


()
