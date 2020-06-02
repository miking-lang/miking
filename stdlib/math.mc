-- Float stuff

let inf = divf 1.0 0.0
let maxf = lam r. lam l. if gtf r l then r else l
let minf = lam r. lam l. if ltf r l then r else l

-- Int stuff

let maxi = lam r. lam l. if gti r l then r else l
let mini = lam r. lam l. if lti r l then r else l

mexpr

utest maxf 0. 0. with 0. in
utest maxf 1. 0. with 1. in
utest maxf 0. 1. with 1. in

utest minf 0. 0. with 0. in
utest minf 1. 0. with 0. in
utest minf 0. 1. with 0. in

utest maxi 0 0 with 0 in
utest maxi 1 0 with 1 in
utest maxi 0 1 with 1 in

utest mini 0 0 with 0 in
utest mini 1 0 with 0 in
utest mini 0 1 with 0 in

utest addi 1 (negi 1) with 0 in

()
