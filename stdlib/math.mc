include "ext/math-ext.mc"

let _eqf = eqfApprox 1e-6

-- Float stuff
let inf = divf 1.0 0.0
let minf = lam r. lam l. if ltf r l then r else l

utest minf 0. 0. with 0. using _eqf
utest minf 1. 0. with 0. using _eqf
utest minf 0. 1. with 0. using _eqf

utest absf 0. with 0. using _eqf
utest absf 1. with 1. using _eqf
utest absf (negf 1.) with 1. using _eqf

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
