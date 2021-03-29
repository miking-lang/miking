-- Float stuff

let inf = divf 1.0 0.0
let maxf = lam r. lam l. if gtf r l then r else l
let minf = lam r. lam l. if ltf r l then r else l
let absf = lam f. maxf f (negf f)
let eqfApprox = lam epsilon. lam r. lam l. if leqf (absf (subf r l)) epsilon then true else false

utest maxf 0. 0. with 0. using eqfApprox 1e-6
utest maxf 1. 0. with 1. using eqfApprox 1e-6
utest maxf 0. 1. with 1. using eqfApprox 1e-6

utest minf 0. 0. with 0. using eqfApprox 1e-6
utest minf 1. 0. with 0. using eqfApprox 1e-6
utest minf 0. 1. with 0. using eqfApprox 1e-6

utest absf 0. with 0. using eqfApprox 1e-6
utest absf 1. with 1. using eqfApprox 1e-6
utest absf (negf 1.) with 1. using eqfApprox 1e-6

utest 1. with 1.01 using eqfApprox 0.011
utest negf 1.0 with negf 1.009 using eqfApprox 0.01
utest 0.0 with 0.0  using (eqfApprox 0.)
utest eqfApprox 0.01 1.0 1.011 with false
utest 1. with 1.000009 using eqfApprox 0.00001
utest eqfApprox 0.00001 1.0 1.000011 with false

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
