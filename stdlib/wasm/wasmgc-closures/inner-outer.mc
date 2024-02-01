include "common.mc"

mexpr
let outer = lam x.
    let a = addi x 1 in
    let inner = lam y. addi (addi x y) a in
    inner
in
outer 1 2
-- utest outer 1 2 with 5 in ()
