include "sundials/ida.mc"
include "ad/dualnum.mc"
include "ad/dualtensor-tree.mc"

type IdaAdVResFn = DualNum -> DualTensor -> DualTensor -> DualTensor -> ()

-- See `IdaInitArg`.
type IdaAdVInitArg = {
  tol      : IdaTolerance,
  nlsolver : SundialsNonlinearSolver,
  lsolver  : IdaDlsSolverSession,
  resf    : IdaAdVResFn,
  varid   : NvectorSerial,
  roots   : (Int, IdaRootFn),
  t       : Float,
  y       : NvectorSerial,
  yp      : NvectorSerial
}

-- See `idaInit`.
let idaAdVInit = lam arg : IdaAdVInitArg.
  match arg with {
    tol      = tol,
    nlsolver = nlsolver,
    lsolver  = lsolver,
    resf     = resf,
    varid    = varid,
    roots    = roots,
    t        = t,
    y        = y,
    yp       = yp
  } in
  let resf = lam t. lam y. lam yp. lam r.
    resf (Primal t) (PrimalTensor y) (PrimalTensor yp) (PrimalTensor r)
  in
  idaInit {
    tol      = tol,
    nlsolver = nlsolver,
    lsolver  = lsolver,
    resf     = resf,
    varid    = varid,
    roots    = roots,
    t        = t,
    y        = y,
    yp       = yp
  }

-- `idaAdDlsSolverJacf resf solver` is a variant of `idaDlsSolverJacf` where the
-- Jacobian function is computed from the residual function `resf` using
-- automatic differentiation.
let idaAdVDlsSolverJacf = lam resf : IdaAdVResFn.
  let jacf = lam jacargs : IdaJacArgs. lam m.
    -- m is in column major order which means that we have to compute the
    -- transpose of df(t, y, y')/dy + c df(t, y, y')/dy' since our tensors are
    -- in row major order.
    let m = sundialsMatrixDenseUnwrap m in
    match jacargs with {c = c, t = t, y = y, yp = yp, tmp = (tmp1, _, _)} in
    -- Compute ∇f(t, y, y') w.r.t. y.
    dualtensorJacT
      (lam y. resf (Primal t) y (PrimalTensor yp))
      (PrimalTensor y)
      (PrimalTensor m);
    -- Compute c∇f(t, y, y') w.r.t. y' and add to m.
    tensorIterSlice
      (lam j. lam r.
        dualtensorJacj
          (resf (Primal t) (PrimalTensor y))
          (PrimalTensor yp) j (PrimalTensor tmp1);
        tensorMapInplace (mulf c) tmp1;
        tensorMapExn addf tmp1 r)
      m;
    ()
  in
  idaDlsSolverJacf jacf

mexpr

utest
  let tget = tensorGetExn in
  let tset = tensorSetExn in
  let dtget = dualtensorGetExn in
  let dtset = dualtensorSetExn in
  let tcreate = tensorCreateCArrayFloat in

  let resf = lam. lam y. lam yp. lam r.
    let x = dtget y [0] in
    let vx = dtget y [1] in
    let dx = dtget yp [0] in
    let dvx = dtget yp [1] in
    dtset r [0] (subn dx vx);
    dtset r [1] (addn dvx (addn vx x));
    ()
  in

  let runTests = lam mklsolver.
    let y = tcreate [2] (lam. 0.) in
    let yp = tcreate [2] (lam. 0.) in

    tset y [0] 1.;
    tset yp [1] (negf 1.);

    let v = nvectorSerialWrap y in
    let vp = nvectorSerialWrap yp in

    let m = sundialsMatrixDense 2 in

    let nlsolver = sundialsNonlinearSolverNewtonMake v in

    let lsolver = mklsolver (idaDlsDense v m) in
    let tol = idaSSTolerances 1.e-4 1.e-6 in

    let varid = nvectorSerialWrap (tcreate [2] (lam. idaVarIdDifferential)) in
    let t0 = 0. in

    let s = idaAdVInit {
      tol      = tol,
      nlsolver = nlsolver,
      lsolver  = lsolver,
      resf     = resf,
      varid    = varid,
      roots    = idaNoRoots,
      t        = t0,
      y        = v,
      yp       = vp
    } in
    idaCalcICYaYd s { tend = 1.e-4, y = v, yp = vp };

    match idaSolveNormal s { tend = 2., y = v, yp = vp } with (tend, r) in
    utest r with IdaSuccess {} in
    utest tend with 2. using eqf in

    let y = nvectorSerialUnwrap v in
    let yp = nvectorSerialUnwrap vp in

    tset y [0] 1.;
    tset y [1] 0.;
    tset yp [0] 0.;
    tset yp [1] (negf 0.);
    idaReinit s { roots = idaNoRoots, t = t0, y = v, yp = vp };
    idaCalcICYaYd s { tend = 1.e-4, y = v, yp = vp };

    match idaSolveNormal s { tend = 2., y = v, yp = vp } with (tend, r) in
    utest r with IdaSuccess {} in
    utest tend with 2. using eqf in
    ()
  in

  runTests (lam lsolver. idaDlsSolver lsolver);
  runTests (lam lsolver. idaAdVDlsSolverJacf resf lsolver);

  ()
with () in
()
