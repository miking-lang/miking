-- Interface to the CVODE module in sundialsml
-- https://inria-parkas.github.io/sundialsml/Cvode.html

include "sundials/sundials.mc"

type CVODEDlsDense
type CVODEDlsSolverSession
type CVODETolerance
type CVODELinearMultistepMethod
type CVODESession

type CVODESolveError
-- Missing or illegal solver inputs.
con CVODEIllInput : {} -> CVODESolveError
-- The initial and final times are too close to each other and not initial step
-- size was specified.
con CVODETooClose : {} -> CVODESolveError
-- The requested time could not be reached in mxstep internal steps.
con CVODETooMuchWork : {} -> CVODESolveError
-- The requested accuracy could not be satisfied.
con CVODETooMuchAccuracy : {} -> CVODESolveError
-- Too many error test failures within a step or at the minimum step size.
con CVODEErrFailure : {} -> CVODESolveError
-- Too many convergence test failures within a step or at the minimum step size.
con CVODEConvergenceFailure : {} -> CVODESolveError
-- Linear solver initialization failed.
con CVODELinearInitFailure : {} -> CVODESolveError
-- Linear solver setup failed unrecoverably.
con CVODELinearSetupFailure : {} -> CVODESolveError
-- Linear solver solution failed unrecoverably.
con CVODELinearSolveFailure : {} -> CVODESolveError
-- Unrecoverable failure in the RHS function f.
con CVODERhsFuncFailure : {} -> CVODESolveError
-- Initial unrecoverable failure in the RHS function f.
con CVODEFirstRhsFuncFailure : {} -> CVODESolveError
-- Too many convergence test failures, or unable to estimate the initial step
-- size, due to repeated recoverable errors in the right-hand side function.
con CVODERepeatedRhsFuncFailure : {} -> CVODESolveError
-- The right-hand side function had a recoverable error, but no recovery was
-- possible. This error can only occur after an error test failure at order one.
con CVODEUnrecoverableRhsFuncFailure : {} -> CVODESolveError
-- Failure in the rootfinding function g.
con CVODERootFuncFailure : {} -> CVODESolveError
-- Unspecified solver failure.
con CVODEErrUnspecified : {} -> CVODESolveError

let _cvodeErrorCodeToError : Int -> CVODESolveError
  = lam ec.
  switch ec
    case 0 then CVODEIllInput {}
    case 1 then CVODETooClose {}
    case 2 then CVODETooMuchWork {}
    case 3 then CVODETooMuchAccuracy {}
    case 4 then CVODEErrFailure {}
    case 5 then CVODEConvergenceFailure {}
    case 6 then CVODELinearInitFailure {}
    case 7 then CVODELinearSetupFailure {}
    case 8 then CVODELinearSolveFailure {}
    case 9 then CVODERhsFuncFailure {}
    case 10 then CVODEFirstRhsFuncFailure {}
    case 11 then CVODERepeatedRhsFuncFailure {}
    case 12 then CVODEUnrecoverableRhsFuncFailure {}
    case 13 then CVODERootFuncFailure {}
    case _ then CVODEErrUnspecified {}
  end

type CVODESolverResult
-- The solution was advanced.
con CVODESuccess : {} -> CVODESolverResult
-- A root was found.
con CVODERootsFound : {} -> CVODESolverResult
-- The stop time was reached.
con CVODEStopTimeReached : {} -> CVODESolverResult
-- Solver error.
con CVODESolveError : CVODESolveError -> CVODESolverResult

let _cvodeSolverCodeToSolverResult : (Int, Int) -> CVODESolverResult
  = lam rc.
  switch rc
    case (0, _) then CVODESuccess {}
    case (1, _) then CVODERootsFound {}
    case (2, _) then CVODEStopTimeReached {}
    case (3, ec) then CVODESolveError (_cvodeErrorCodeToError ec)
  end

-- Right-hand side functions for calculating ODE derivatives. They are passed
-- three arguments:
-- - t, the value of the independent variable, i.e., the simulation time,
-- - y, the vector of dependent-variable values, i.e., y(t), and,
-- - y', a vector for storing the value of f(t,y).
type CVODERHS = Float -> Tensor[Float] -> Tensor[Float] -> ()

external cvodeDlsDense !
  : NvectorSerial -> SundialsMatrixDense -> CVODEDlsDense

-- `cvodeDlsDense y m` returns a linear solver associated with the state vector
-- `y` and dense Jacobian iteration matrix `m`.
let cvodeDlsDense = lam y. lam m. cvodeDlsDense y m

external cvodeDlsSolver ! : CVODEDlsDense -> CVODEDlsSolverSession

-- `cvodeDlsSolver solver` initializes the solver `solver`. This solver will
-- internally approximate the system Jacobian.
let cvodeDlsSolver = lam solver. cvodeDlsSolver solver

external cvodeSSTolerances : Float -> Float -> CVODETolerance

-- `cvodeSSTolerances rtol atol` constructs scalar error tolerances where `rtol`
-- is the relative tolerance and `atol` the absolute tolerance.
let cvodeSSTolerances = lam rtol. lam atol. cvodeSSTolerances rtol atol
let cvodeDefaultTolerances = cvodeSSTolerances 1.e-4 1.e-8

-- Adams-Moulton formulas (non-stiff systems).
external cvodeLMMAdams : CVODELinearMultistepMethod
-- Backward Differentiation Formulas (stiff systems).
external cvodeLMMBDF : CVODELinearMultistepMethod

external cvodeInit !
  : CVODELinearMultistepMethod ->
    CVODETolerance ->
    CVODEDlsSolverSession ->
    CVODERHS ->
    Float ->
    NvectorSerial ->
    CVODESession

type CVODEInitArg = {
  -- The linear multistep method.
  lmm : CVODELinearMultistepMethod,

  -- The integration tolerances.
  tol : CVODETolerance,

  -- Used by non-linear solver based on Newton interations.
  lsolver : CVODEDlsSolverSession,

  -- The ODE right-hand-side function.
  rhs : CVODERHS,

  -- The initial value of the independent variable.
  t0 : Float,

  --  Initial state values that also determines the number of equations.
  y0 : NvectorSerial
}

-- `cvodeInit arg` creates an CVODE session given arguments `arg`.
let cvodeInit = lam arg : CVODEInitArg.
  cvodeInit arg.lmm arg.tol arg.lsolver arg.rhs arg.t0 arg.y0

external cvodeSolveNormal !
  : CVODESession ->
    Float ->
    NvectorSerial ->
    (Float, (Int, Int))

type CVODESolveNormalArg = {
  -- A solver session.
  s : CVODESession,

  -- The next time at which a solution is desired.
  tend : Float,

  -- A vector to store the computed solution.
  y : NvectorSerial
}

-- `cvodeSolveNormal s arg` solves problem in session `s` given `arg`.
let cvodeSolveNormal = lam arg : CVODESolveNormalArg.
  match cvodeSolveNormal arg.s arg.tend arg.y with (tend, rc) in
  (tend, _cvodeSolverCodeToSolverResult rc)

external cvodeSetStopTime ! : CVODESession -> Float -> ()

-- Limits the value of the independent variable t when solving. By default no
-- stop time is imposed.
let cvodeSetStopTime = lam s : CVODESession. lam tend : Float.
  cvodeSetStopTime s tend

mexpr

utest
  let tget = tensorLinearGetExn in
  let tset = tensorLinearSetExn in
  let tcreate = tensorCreateCArrayFloat in

  let rhs = lam. lam y. lam dy.
    let x = tget y 0 in
    let vx = tget y 1 in
    tset dy 0 vx;
    tset dy 1 (negf (addf vx x));
    ()
  in

  let runTests = lam.
    let y = tcreate [2] (lam. 0.) in
    tset y 0 1.;
    let v = nvectorSerialWrap y in

    let m = sundialsMatrixDense 2 in
    let lsolver = cvodeDlsSolver (cvodeDlsDense v m) in

    let t0 = 0. in

    let s = cvodeInit {
      lmm      = cvodeLMMBDF,
      tol      = cvodeDefaultTolerances,
      lsolver  = lsolver,
      rhs      = rhs,
      t0       = t0,
      y0       = v
    } in

    cvodeSetStopTime s 10.;

    recursive let recur = lam t.
      switch cvodeSolveNormal { s = s, tend = addf t 0.1, y = v }
        case (tend, CVODEStopTimeReached _) then (tend, true)
        case (tend, CVODESuccess _) then recur tend
        case _ then (t, false)
      end
    in
    utest recur 0. with (10., true) in
    ()
  in
  runTests ();
  ()
with () in ()
