-- This program tests an external functions which needs marshaling of data

include "string.mc"

external testListMap : (a -> b) -> [a] -> [b]

mexpr
let x = testListMap (lam x. addi x 1) [1, 2] in
utest x with [2, 3] in
()
