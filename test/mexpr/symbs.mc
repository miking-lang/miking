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

()
