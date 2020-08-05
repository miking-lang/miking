-- Float stuff

let inf = divf 1.0 0.0
let maxf = lam r. lam l. if gtf r l then r else l
let minf = lam r. lam l. if ltf r l then r else l
let absf = lam f. maxf f (negf f)

utest maxf 0. 0. with 0.
utest maxf 1. 0. with 1.
utest maxf 0. 1. with 1.

utest minf 0. 0. with 0.
utest minf 1. 0. with 0.
utest minf 0. 1. with 0.

utest absf 0. with 0.
utest absf 1. with 1.
utest absf (negf 1.) with 1.

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
