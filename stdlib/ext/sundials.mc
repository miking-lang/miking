type SResf = SArray -> SArray -> Float -> SArray -> ()

let IDA_SUCCESS = 0
let IDA_ROOTS_FOUND = 2
let IDA_STOP_TIME_REACHED = 1

let noroots = (0, lam _. error "Called noroots")

let sArr2Seq = lam a.
  recursive let work = lam seq. lam i.
    if lti i 0 then seq
    else work (cons (sArrGet a i) seq) (subi i 1)
  in
  work [] (subi (sArrLength a) 1)
