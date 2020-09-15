-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test symbools

mexpr

-- 'gensym()' generates a new unique symbol.
-- () -> Symbol
let x = gensym () in
let y = gensym () in

-- 'eqs s1 s2' returns true if symbol 's1' and symbol 's2'
-- are the same symbol.
-- Symbol -> Symbol -> Bool
let neg = lam f. lam x. lam y. not (f x y) in
utest x with x using eqs in
utest y with y using eqs in
utest y with x using neg eqs in
utest x with y using neg eqs in

-- 'sym2hash s1' returns an integer representation of s1 that fulfills the
-- following criterion: eqs a b => eqi (sym2hash a) (sym2hash b)
-- No guarantees are given for the opposite direction, but a best effort is
-- made to give 2 symbols different integer representation.
-- Symbol -> Int
let z = x in
utest sym2hash x with sym2hash x using eqi in
utest sym2hash x with sym2hash z using eqi in

()
