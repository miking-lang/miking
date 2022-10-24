-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test string and char primitives

mexpr

-- lambda
utest (lam x. addi x 2) 3 with 5 in
utest (lam x. lam y. muli x y) 3 4 with 12 in


-- let expressions
let x = 10 in
utest x with 10 in

let y = addi x 5 in
utest y with 15 in

let f1 = lam x. muli y x in
let y = f1 (addi 2 1) in
utest y with 45 in

let f2 = lam x. lam y. addi x y in
utest f2 2 3 with 5 in


-- if expressions
utest if true then 1 else 2 with 1 in
let z = 8 in
let m = lam x. lam y. muli x y in
utest if eqi (m 2 3) 6 then addi z 2 else 0 with 10 in

-- Sequence operator "t1 ; t2", which syntactic sugar for let #var"" = t1 in t2
let foo = lam x.
  dprint "Value x "; dprint x;
  addi x 2 in

-- factorial function
recursive
  let fact = lam n.
    if eqi n 0 then 1
    else muli (fact (subi n 1)) n
in
utest fact 0 with 1 in
utest fact 1 with 1 in
utest fact 3 with 6 in
utest fact 8 with 40320 in

()
