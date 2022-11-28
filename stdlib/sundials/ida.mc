-- Interface to the IDA module in sundialsml
-- https://inria-parkas.github.io/sundialsml/Ida.html

include "sundials/sundials.mc"

type IdaDlsDense
type IdaDlsSolver
type IdaDlsSolverSession
type IdaTolerance
type IdaSession
type IdaSolverResultInternal

type IdaSolverResult
con IdaSuccess : {} -> IdaSolverResult
con IdaStopTimeReached : {} -> IdaSolverResult
con IdaRootsFound : {} -> IdaSolverResult

type IdaJacArgs = {
  -- The current time.
  t   : Float,

  -- The values of y.
  y   : Tensor[Float],

  -- The values of y'.
  yp  : Tensor[Float],

  -- The current value of the residual.
  res : Tensor[Float],

  -- The scaling coefficient c in dF/dy + c dF/dy'.
  c   : Float,

  -- workspace data
  tmp : (Tensor[Float], Tensor[Float], Tensor[Float])
}

-- System Jacobian dF/dy + c dF/dy', where the matrix argument is in column
-- major order.
type IdaJacFn = IdaJacArgs -> SundialsMatrixDense -> ()

type IdaResFn = Float -> Tensor[Float] -> Tensor[Float] -> Tensor[Float] -> ()

type IdaRootFn = IdaResFn
let idaNoRoots = (0, lam. lam. lam. lam. error "not implemented")

external idaDlsDense ! : NvectorSerial -> SundialsMatrixDense -> IdaDlsDense

-- `idaDlsDense y m` returns a linear solver associated with the state vector
-- `y` and dense Jacobian iteration matrix `m`.
let idaDlsDense = lam y. lam m. idaDlsDense y m

external idaDlsSolver ! : IdaDlsDense -> IdaDlsSolverSession

-- `idaDlsSolver solver` initializes the solver `solver`. This solver will
-- internally approximate the system Jacobian.
let idaDlsSolver = lam solver. idaDlsSolver solver

external idaDlsSolverJacf ! : IdaJacFn -> IdaDlsDense -> IdaDlsSolverSession

-- `idaDlsSolver jacf solver` initializes the solver `solver` with the system
-- Jacobian `jacf`.
let idaDlsSolverJacf = lam jacf. lam solver. idaDlsSolverJacf jacf solver

external idaVarIdAlgebraic : Float    -- Indicates an algebraic variable
external idaVarIdDifferential : Float -- Indicates a differential variable

external idaSSTolerances : Float -> Float -> IdaTolerance

-- `idaSSTolerances rtol atol` constructs scalar error tolerances where `rtol`
-- is the relative tolerance and `atol` the absolute tolerance.
let idaSSTolerances = lam rtol. lam atol. idaSSTolerances rtol atol

external idaRetcode : IdaSolverResultInternal -> Int

-- `idaRetcode r` converts internal solver result `r` to a return code.
let idaRetcode = lam r. idaRetcode r

-- `idaSolverResult rc` convert the return code `rc` to a solver result.
let idaSolverResult : IdaSolverResultInternal -> IdaSolverResult =
  lam rc.
    switch idaRetcode rc
    case 0 then IdaSuccess {}
    case 1 then IdaStopTimeReached {}
    case 2 then IdaRootsFound {}
    end

external idaInit !
  : IdaTolerance ->
    SundialsNonlinearSolver ->
    IdaDlsSolverSession ->
    IdaResFn ->
    NvectorSerial ->
    (Int, IdaRootFn) ->
    Float ->
    NvectorSerial ->
    NvectorSerial ->
    IdaSession

type IdaInitArg = {
  -- The error tolerances.
  tol     : IdaTolerance,

  -- The linear solver to use when calculating consistent inital conditions and
  -- calculating integrations steps.
  nlsolver : SundialsNonlinearSolver,

  -- The linear solver.
  lsolver : IdaDlsSolverSession,

  -- The residual function.
  resf    : IdaResFn,

  -- A vector indicating algebraic and differential variables. See
  -- `idaVarIdAlgebraic` and `idaVarIdDifferential`.
  varid   : NvectorSerial,

  -- A tuple `(n, rootf)` where `n` is the number of roots and `rootf` id the
  -- root function.
  roots   : (Int, IdaRootFn),

  -- The initial time.
  t       : Float,

  -- The initial states.
  y       : NvectorSerial,

  -- The initial derivatives of the states.
  yp      : NvectorSerial
}

-- `idaInit arg` creates an IDA session given arguments `arg`.
let idaInit = lam arg : IdaInitArg.
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
  idaInit tol nlsolver lsolver resf varid roots t y yp

external idaCalcICYaYd !
  : IdaSession -> Float -> NvectorSerial -> NvectorSerial -> ()

type IdaCalcICYaYdArg = {
  -- The time where to end the consistent initial value search.
  tend  : Float,

  -- A vector where the consistent initial values y should be written to.
  y  : NvectorSerial,

  -- A vector where the consistent initial values y' should be written to.
  yp : NvectorSerial
}

-- `idaCalcICYaYd s arg` tries to find consistent initial values of session `s`
-- with the argument `arg`. Will produce an error if the search fails.
let idaCalcICYaYd = lam s. lam arg : IdaCalcICYaYdArg.
  match arg with { tend = tend, y = y, yp = yp } in idaCalcICYaYd s tend y yp


external idaSolveNormal
 : IdaSession ->
   Float ->
   NvectorSerial ->
   NvectorSerial ->
   (Float, IdaSolverResultInternal)


type IdaSolveNormalArg = {
  tend : Float,         -- The time at which the solution is requested
  y    : NvectorSerial, -- The solution to y at `tend`.
  yp   : NvectorSerial  -- The solution to y' at `tend`.
}

-- `idaSolveNormal s arg` solves problem in session `s` given `arg`.
let idaSolveNormal =
  lam s. lam arg : IdaSolveNormalArg.
  match arg with { tend = tend, y = y, yp = yp } in
  match (idaSolveNormal s tend y yp) with (tend, r) in
  (tend, idaSolverResult r)

external idaReinit
  : IdaSession ->
    (Int, IdaRootFn) ->
    Float ->
    NvectorSerial ->
    NvectorSerial ->
    ()

-- See `IdaInitArg`.
type IdaReinitArg = {
  roots : (Int, IdaRootFn),
  t     : Float,
  y     : NvectorSerial,
  yp    : NvectorSerial
}

-- `idaReinit s arg` reinitialize sessions s with arguments `arg`. Must be
-- called after roots are found.
let idaReinit = lam s. lam arg : IdaReinitArg.
  match arg with { roots = roots, t = t, y = y, yp = yp } in
  idaReinit s roots t y yp

mexpr

utest
  let tget = tensorGetExn in
  let tset = tensorSetExn in
  let tcreate = tensorCreateCArrayFloat in

  let jacf = lam jacargs : IdaJacArgs. lam m : SundialsMatrixDense.
    let m = sundialsMatrixDenseUnwrap m in
    let x = tget jacargs.y [0] in
    let vx = tget jacargs.y [1] in
    let dx = tget jacargs.yp [0] in
    let dvx = tget jacargs.yp [1] in
    tset m [0, 0] jacargs.c;
    tset m [0, 1] (negf 1.);
    tset m [1, 0] 1.;
    tset m [1, 1] (addf 1. jacargs.c);
    ()
  in

  let resf = lam. lam y. lam yp. lam r.
    let x = tget y [0] in
    let vx = tget y [1] in
    let dx = tget yp [0] in
    let dvx = tget yp [1] in
    tset r [0] (subf dx vx);
    tset r [1] (addf dvx (addf vx x));
    ()
  in

  let runTests = lam mknlsolver. lam mklsolver.
    let y = tcreate [2] (lam. 0.) in
    let yp = tcreate [2] (lam. 0.) in

    tset y [0] 1.;
    tset yp [1] (negf 1.);

    let v = nvectorSerialWrap y in
    let vp = nvectorSerialWrap yp in

    let m = sundialsMatrixDense 2 in

    let nlsolver = mknlsolver v in

    let lsolver = mklsolver (idaDlsDense v m) in
    let tol = idaSSTolerances 1.e-4 1.e-6 in

    let varid = nvectorSerialWrap (tcreate [2] (lam. idaVarIdDifferential)) in
    let t0 = 0. in

    let s = idaInit {
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

  let nlnewton = sundialsNonlinearSolverNewtonMake in
  let nlfixedpoint = sundialsNonlinearSolverFixedPointMake 0 in

  runTests nlnewton (lam lsolver. idaDlsSolver lsolver);
  runTests nlnewton (lam lsolver. idaDlsSolverJacf jacf lsolver);

  -- runTests nlfixedpoint (lam lsolver. idaDlsSolver lsolver);
  -- runTests nlfixedpoint (lam lsolver. idaDlsSolverJacf jacf lsolver);

  ()
with () in ()
