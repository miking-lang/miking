include "ext/sundials.mc"

mexpr
let a = sArrCreate 3 in
let _ = sArrSet a 0 0. in
let _ = sArrSet a 1 1. in
let _ = sArrSet a 2 2. in

utest sArrGet a 0 with 0. in
utest sArrGet a 1 with 1. in
utest sArrGet a 2 with 2. in
utest sArrLength a with 3 in
utest sArr2Seq a with [0., 1., 2.] in

let y = sArrCreate 2 in
let yp = sArrCreate 2 in
let _ = sArrSet y 0 1. in
let _ = sArrSet y 1 2. in
let _ = sArrSet yp 0 3. in
let _ = sArrSet yp 1 4. in
let tol = (1e-6, 1e-6) in
let resf = lam t. lam y. lam yp. lam r.
  let _ = sArrSet r 0 (subf (sArrGet yp 0) (sArrGet y 1)) in
  sArrSet r 1 (addf (sArrGet yp 1) (sArrGet y 0))
in
let s = idaInitDense tol resf 0. y yp in
utest idaCalcICYY s y 0.001 with () in
utest idaSolveNormal s 10. y yp with (10., IDA_SUCCESS) in

let jacf = lam t. lam c. lam y. lam yp. lam m.
  let _ = sMatrixDenseSet m 0 0 c in
  let _ = sMatrixDenseSet m 0 1 (negf 1.) in
  let _ = sMatrixDenseSet m 1 0 1. in
  sMatrixDenseSet m 1 1 c
in
let s = idaInitDenseJac tol jacf resf 0. y yp in
utest idaCalcICYY s y 0.001 with () in
utest idaSolveNormal s 10. y yp with (10., IDA_SUCCESS) in

()
