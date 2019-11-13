// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//


mexpr

// Mutual recursion


recursive
let fact = lam fact. lam n.
  if eqi n 0
    then 1
    else muli n (fact (subi n 1))
in


recursive
let odd = lam n.
    if eqi n 1 then true
    else if lti n 1 then false
    else even (subi n 1)
let even = lam n.
    if eqi n 0 then true
    else if lti n 0 then false
    else odd (subi n 1)
in

()
