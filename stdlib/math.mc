include "ext/math-ext.mc"

-- Float stuff
let inf = divf 1.0 0.0
let minf = lam r. lam l. if ltf r l then r else l

utest minf 0. 0. with 0. using eqf
utest minf 1. 0. with 0. using eqf
utest minf 0. 1. with 0. using eqf

utest absf 0. with 0. using eqf
utest absf 1. with 1. using eqf
utest absf (negf 1.) with 1. using eqf

-- Int stuff
let maxi = lam r. lam l. if gti r l then r else l
let mini = lam r. lam l. if lti r l then r else l
let absi = lam i. maxi i (negi i)

utest maxi 0 0 with 0
utest maxi 1 0 with 1
utest maxi 0 1 with 1

utest mini 0 0 with 0
utest mini 1 0 with 0
utest mini 0 1 with 0

utest absi 0 with 0
utest absi 1 with 1
utest absi (negi 1) with 1

utest addi 1 (negi 1) with 0

let succ = lam x. addi x 1

utest succ 0 with 1

let pred = lam x. subi x 1

utest pred 1 with 0