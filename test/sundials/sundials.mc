include "sundials/sundials.mc"

mexpr
let a = sArrMake 3 0. in
sArrSet a 0 0.;
sArrSet a 1 1.;
sArrSet a 2 2.;

utest sArrGet a 0 with 0. in
utest sArrGet a 1 with 1. in
utest sArrGet a 2 with 2. in
utest sArrLength a with 3 in
utest sArr2Seq a with [0., 1., 2.] in

let y = sArrMake 2 0. in
let yp = sArrMake 2 0. in
sArrSet y 0 1.;
sArrSet y 1 2.;
sArrSet yp 0 3.;
sArrSet yp 1 4.;
let tol = (1e-6, 1e-6) in
let resf = lam t. lam y. lam yp. lam r.
  sArrSet r 0 (subf (sArrGet yp 0) (sArrGet y 1));
  sArrSet r 1 (addf (sArrGet yp 1) (sArrGet y 0))
in
let s = idaInitDense tol resf noroots 0. y yp in
utest idaCalcICYY s y 0.001 with () in
utest idaSolveNormal s 10. y yp with (10., idaRCSuccess) in

let jacf = lam t. lam c. lam y. lam yp. lam m.
  sMatrixDenseSet m 0 0 c;
  sMatrixDenseSet m 0 1 (negf 1.);
  sMatrixDenseSet m 1 0 1.;
  sMatrixDenseSet m 1 1 c
in
let rootf = lam t. lam. lam. lam g.
  sArrSet g 0 (subf t 5.)
in
let s = idaInitDenseJac tol jacf resf (1, rootf) 0. y yp in
utest idaCalcICYY s y 0.001 with () in
utest idaSolveNormal s 10. y yp with (5., idaRCRootsFound) in
utest idaReinit s 5. y yp with () in
utest idaSolveNormal s 10. y yp with (10., idaRCSuccess) in

utest idaGetDky s y (subf (idaGetCurrentTime s) (idaGetLastStep s)) 0 with () in
utest idaGetDky s yp (subf (idaGetCurrentTime s) (idaGetLastStep s)) 1 with () in

let m = sMatrixDenseCreate 2 2 in
sMatrixDenseSet m 0 0 1.;
sMatrixDenseSet m 0 1 1.;
sMatrixDenseSet m 1 0 1.;
sMatrixDenseSet m 1 1 1.;

utest sMatrixDenseGet m 0 0 with 1. in
utest sMatrixDenseGet m 0 1 with 1. in
utest sMatrixDenseGet m 1 0 with 1. in
utest sMatrixDenseGet m 1 1 with 1. in

let y = sArrMake 2 0. in
let yp = sArrMake 2 0. in
sArrSet y 0 1.;
sArrSet y 1 2.;
sArrSet yp 0 3.;
sArrSet yp 1 4.;
let varid = sArrMake 2 idaVarIdDifferential in

let s = idaInitDense tol resf noroots 0. y yp in

utest idaCalcICYYYP s y yp varid 0.001 with () in

()
