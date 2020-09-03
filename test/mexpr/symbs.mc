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
utest eqs x x with true in
utest eqs y y with true in
utest eqs y x with false in
utest eqs x y with false in

-- 'sym2hash s1' returns an integer representation of s1 that fulfills the
-- following criterion: eqs a b => eqi (sym2hash a) (sym2hash b)
-- No guarantees are given for the opposite direction, but a best effort is
-- made to give 2 symbols different integer representation.
-- Symbol -> Int
let z = x in
utest eqi (sym2hash x) (sym2hash x) with true in
utest eqi (sym2hash x) (sym2hash z) with true in

()
