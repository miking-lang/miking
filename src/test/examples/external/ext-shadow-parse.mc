-- This program tests shadowing of externals, it will parse but note compile

mexpr
external addi : Int -> Int -> Int in
let addi = lam x. lam y. x in
addi 1
