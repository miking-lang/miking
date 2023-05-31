-- This program tests an external function with a callback and marshaling of
-- data

include "string.mc"

external extTestListConcatMap : (a -> [b]) -> [a] -> [b]

mexpr
let x = extTestListConcatMap (lam x. [addi x 1]) [1, 2] in
utest x with [2, 3] in
()
