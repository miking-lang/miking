
let idaRCSuccess = 0
let idaRCRootsFound = 2
let idaRCStopTimeReached = 1

let idaVarIdDifferential = 1.
let idaVarIdAlgebraic = 0.

let noroots = (0, lam _. error "Called noroots")

let sArr2Seq = lam a.
  recursive let work = lam seq. lam i.
    if lti i 0 then seq
    else work (cons (sArrGet a i) seq) (subi i 1)
  in
  work [] (subi (sArrLength a) 1)
