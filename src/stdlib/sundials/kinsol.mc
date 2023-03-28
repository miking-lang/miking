-- Interface to the Kinsol module in sundialsml
-- https://inria-parkas.github.io/sundialsml/Kinsol.html

include "sundials/sundials.mc"

type KinsolDlsDense
type KinsolDlsSolverSession
type KinsolSession

type KinsolError
-- A linear solver is required but was not given.
con KinsolMissingLinearSolver : {} -> KinsolError  
--  Missing or illegal solver inputs.
con KinsolIllInput : {} -> KinsolError 
-- Line search could not find a suitable iterate.
con KinsolLineSearchNonConvergence : {} -> KinsolError 
-- The maximum number of nonlinear iterations was reached.
con KinsolMaxIterationsReached : {} -> KinsolError 
-- Five consecutive steps satisfied a scaled step length test.
con KinsolMaxNewtonStepExceeded : {} -> KinsolError 
-- Line search could not satisfy the beta-condition.
con KinsolLineSearchBetaConditionFailure : {} -> KinsolError
-- The Kinsol.Spils.prec_solve_fn callback raised Sundials.RecoverableFailure
-- but the preconditioner is already current.
con KinsolLinearSolverNoRecovery : {} -> KinsolError
-- Linear solver initialization failed.
con KinsolLinearSolverInitFailure : {} -> KinsolError
-- Linear solver setup failed unrecoverably.
con KinsolLinearSetupFailure : {} -> KinsolError 
-- Linear solver solution failed unrecoverably.
con KinsolLinearSolveFailure : {} -> KinsolError 
-- The callback F(u) failed unrecoverably.
con KinsolSystemFunctionFailure : {} -> KinsolError 
-- The callback F(u) failed when first called.
con KinsolFirstSystemFunctionFailure : {} -> KinsolError 
-- The callback F(u) failed repeatedly.
con KinsolRepeatedSystemFunctionFailure : {} -> KinsolError 

let _kinsolErrorCodeToError = lam errorCode : Int.
  switch errorCode
    case 0 then KinsolMissingLinearSolver {}  
    case 1 then KinsolIllInput {} 
    case 2 then KinsolLineSearchNonConvergence {} 
    case 3 then KinsolMaxIterationsReached {} 
    case 4 then KinsolMaxNewtonStepExceeded {} 
    case 5 then KinsolLineSearchBetaConditionFailure {} 
    case 6 then KinsolLinearSolverNoRecovery {}
    case 7 then KinsolLinearSolverInitFailure {}
    case 8 then KinsolLinearSetupFailure {} 
    case 9 then KinsolLinearSolveFailure {} 
    case 10 then KinsolSystemFunctionFailure {} 
    case 11 then KinsolFirstSystemFunctionFailure {} 
    case 12 then KinsolRepeatedSystemFunctionFailure {} 
  end

type KinsolSolverResult
con KinsolSuccess : {} -> KinsolSolverResult
con KinsolInitialGuessOK : {} -> KinsolSolverResult
con KinsolStoppedOnStepTol : {} -> KinsolSolverResult
con KinsolError : KinsolError -> KinsolSolverResult

let _kinsolSolverCodeToSolverResult = lam solverCode : (Int, Int).
  switch solverCode
    case (0, _) then KinsolSuccess {}
    case (1, _) then KinsolInitialGuessOK {}
    case (2, _) then KinsolStoppedOnStepTol {}
    case (3, ec) then KinsolError (_kinsolErrorCodeToError ec)
  end

type KinsolStrategy
-- Basic Newton iteration.
external kinsolNewton : KinsolStrategy
-- Newton iteration with globalization.
external kinsolLineSearch : KinsolStrategy
-- Picard iteration with Anderson Acceleration.
external kinsolPicard : KinsolStrategy
-- Fixed-point iteration with Anderson Acceleration.
external kinsolFixedPoint : KinsolStrategy

type KinsolResFn = Tensor[Float] -> Tensor[Float] -> ()

external kinsolDlsDense !
  : NvectorSerial -> SundialsMatrixDense -> KinsolDlsDense

-- `kinsolDlsDense u m` returns a linear solver associated with the data vector
-- `u` and dense Jacobian iteration matrix `m`.
let kinsolDlsDense = lam u. lam m. kinsolDlsDense u m

external kinsolDlsSolver ! : KinsolDlsDense -> KinsolDlsSolverSession

-- `kinsolDlsSolver solver` initializes the solver `solver`. This solver will
-- internally approximate the system Jacobian.
let kinsolDlsSolver = lam solver. kinsolDlsSolver solver

external kinsolInit !
: KinsolDlsSolverSession ->
  KinsolResFn ->
  NvectorSerial ->
  KinsolSession

type KinsolInitArg = {
  -- the linear solver to use (required for the Newton, LineSearch, and
  -- Picard strategies).
  lsolver : KinsolDlsSolverSession,

  -- The residual function.
  resf : KinsolResFn,

  -- A template to initialize the session (e.g., the initial guess vector).
  u : NvectorSerial
}

-- `kinsolInit arg` creates an Kinsol session given arguments `arg`.
let kinsolInit = lam arg : KinsolInitArg. kinsolInit arg.lsolver arg.resf arg.u

external kinsolSolve ! 
  : KinsolSession ->
    NvectorSerial ->
    KinsolStrategy ->
    NvectorSerial ->
    NvectorSerial ->
    (Int, Int)

type KinsolSolveArg = {
  -- A solver session.
  s : KinsolSession,

  -- An initial guess that is replaced with an approximate solution for
  -- F(u)=0.
  u : NvectorSerial,

  -- Strategy used to solve the nonlinear system.
  strategy : KinsolStrategy,

  -- The diagonal elements of the scaling matrix Du for vector u chosen so
  -- that all Duu all have roughly the same magnitude when u is close to a
  -- root of F(u).
  uScale : NvectorSerial,

  -- The diagonal elements of the scaling matrix D_f for F(u) chosen so that
  -- all D_fF(u) have roughtly the same magnitude when u is not near a root of
  -- F(u).
  fScale : NvectorSerial
}

-- `kinsolSolve arg` solves a problem given in arguments `arg`.
let kinsolSolve = lam arg : KinsolSolveArg.
  let r = kinsolSolve arg.s arg.u arg.strategy arg.uScale arg.fScale in
  _kinsolSolverCodeToSolverResult r

mexpr

utest
  let tget = tensorLinearGetExn in
  let tset = tensorLinearSetExn in
  let tcreate = tensorCreateCArrayFloat in

  let resf = lam u. lam r.
    let x = tget u 0 in
    let y = tget u 1 in
    tset r 0 (subf x y);
    tset r 1 (subf y 3.);
    ()
  in

  let runTest = lam mklsolver. lam u0.
    let u = nvectorSerialWrap u0 in
    let m = sundialsMatrixDense 2 in
    let lsolver = mklsolver (kinsolDlsDense u m) in
    let s = kinsolInit { lsolver = lsolver, resf = resf, u = u } in
    let uScale = nvectorSerialWrap (tcreate [2] (lam. 1.)) in
    let fScale = nvectorSerialWrap (tcreate [2] (lam. 1.)) in
    kinsolSolve {
      s = s, u = u, strategy = kinsolNewton, uScale = uScale, fScale = fScale
    }
  in

  let u0 = tcreate [2] (lam. 0.) in
  utest runTest kinsolDlsSolver u0 with KinsolSuccess {} in
  utest runTest kinsolDlsSolver u0 with KinsolInitialGuessOK {} in
  ()
with () in ()