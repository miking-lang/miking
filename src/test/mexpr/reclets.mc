-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--


mexpr

-- Mutual recursion


recursive
let fact = lam n.
  if eqi n 0
    then 1
    else muli n (fact (subi n 1))
in

utest fact 0 with 1 in
utest fact 4 with 24 in
utest fact 5 with 120 in

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

utest odd 4 with false in
utest even 4 with true in

recursive
let fax = lam f. lam e. f (fax f) e in

let fact = fax (lam recur. lam n.
  if eqi n 0
    then 1
    else muli n (recur (subi n 1)))
in

utest fact 0 with 1 in
utest fact 4 with 24 in
utest fact 5 with 120 in

()
