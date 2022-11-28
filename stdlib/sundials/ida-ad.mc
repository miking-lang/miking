include "sundials/ida.mc"
include "ad/dualnum.mc"
include "ad/dualtensor-tree.mc"

type IdaAdResFn =
  DualNum -> Tensor[DualNum] -> Tensor[DualNum] -> Tensor[DualNum] -> ()

-- See `IdaInitArg`.
type IdaAdInitArg = {
  tol      : IdaTolerance,
  nlsolver : SundialsNonlinearSolver,
  lsolver  : IdaDlsSolverSession,
  resf     : IdaAdResFn,
  varid    : NvectorSerial,
  roots    : (Int, IdaRootFn),
  t        : Float,
  y        : NvectorSerial,
  yp       : NvectorSerial
}

-- See `idaInit`.
let idaAdInit = lam arg : IdaAdInitArg.
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
  let ny = tensorSize (nvectorSerialUnwrap arg.y) in
  let yd = tensorCreateDense [ny] (lam. Primal 0.) in
  let ypd = tensorCopy yd in
  let rd = tensorCopy yd in
  let resf = lam t. lam y. lam yp. lam r.
    tensorMapExn (lam x. lam. Primal x) y yd;
    tensorMapExn (lam x. lam. Primal x) yp ypd;
    resf (Primal t) yd ypd rd;
    tensorMapExn (lam x. lam. dualnumPrimalDeep x) rd r;
    ()
  in
  idaInit {
    tol     = tol,
    nlsolver = nlsolver,
    lsolver = lsolver,
    resf    = resf,
    varid   = varid,
    roots   = roots,
    t       = t,
    y       = y,
    yp      = yp
  }

-- `idaAdDlsSolverJacf n resf solver` is a variant of `idaDlsSolverJacf` where
-- the Jacobian function is computed from the residual function `resf` using
-- automatic differentiation and the paramter `n` is the size of the problem.
let idaAdDlsSolverJacf = lam n. lam resf : IdaAdResFn.
  let yd = tensorCreateDense [n] (lam. Primal 0.) in
  let ypd = tensorCopy yd in
  let dm = tensorCreateDense [n, n] (lam. Primal 0.) in
  let jacf = lam jacargs : IdaJacArgs. lam m.
    -- m is in column major order which means that we have to compute the
    -- transpose of df(t, y, y')/dy + c df(t, y, y')/dy' since our tensors are
    -- in row major order.
    let m = sundialsMatrixDenseUnwrap m in
    match jacargs with {c = c, t = t, y = y, yp = yp} in
    tensorMapExn (lam x. lam. Primal x) y yd;
    tensorMapExn (lam x. lam. Primal x) yp ypd;
    -- Compute ∇f(t, y, y') w.r.t. y.
    dualnumJacT (lam y. resf (Primal t) y ypd) yd dm;
    tensorMapExn (lam x. lam. dualnumPrimalDeep x) dm m;
    -- Compute c∇f(t, y, y') w.r.t. y' and add to m.
    dualnumJacT (resf (Primal t) yd) ypd dm;
    tensorMapExn (lam x. lam y. addf (mulf c (dualnumPrimalDeep x)) y) dm m;
    ()
  in
  idaDlsSolverJacf jacf

mexpr

utest
  let tget = tensorGetExn in
  let tset = tensorSetExn in
  let tcreate = tensorCreateCArrayFloat in

  let n = 2 in

  let resf = lam. lam y. lam yp. lam r.
    let x = tget y [0] in
    let vx = tget y [1] in
    let dx = tget yp [0] in
    let dvx = tget yp [1] in
    tset r [0] (subn dx vx);
    tset r [1] (addn dvx (addn vx x));
    ()
  in

  let runTests = lam mklsolver.
    let y = tcreate [n] (lam. 0.) in
    let yp = tcreate [n] (lam. 0.) in

    tset y [0] 1.;
    tset yp [1] (negf 1.);

    let v = nvectorSerialWrap y in
    let vp = nvectorSerialWrap yp in

    let m = sundialsMatrixDense 2 in

    let nlsolver = sundialsNonlinearSolverNewtonMake v in

    let lsolver = mklsolver (idaDlsDense v m) in
    let tol = idaSSTolerances 1.e-4 1.e-6 in

    let varid = nvectorSerialWrap (tcreate [n] (lam. idaVarIdDifferential)) in
    let t0 = 0. in

    let s = idaAdInit {
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
    let r = idaSolveNormal s { tend = 2., y = v, yp = vp } in

    match r with (tend, r) in
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
    let r = idaSolveNormal s { tend = 2., y = v, yp = vp } in

    match r with (tend, r) in
    utest r with IdaSuccess {} in
    utest tend with 2. using eqf in
    ()
  in

  runTests (lam lsolver. idaDlsSolver lsolver);
  runTests (lam lsolver. idaAdDlsSolverJacf n resf lsolver);

  ()
with () in
()
