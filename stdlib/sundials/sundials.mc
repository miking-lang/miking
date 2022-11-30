include "string.mc"
include "tensor.mc"

type NvectorSerial
type SundialsMatrixDense
type SundialsRealArray
type SundialsNonlinearSolver

external nvectorSerialWrap : Tensor[Float] -> NvectorSerial

-- `nvectorSerialWrap t` wraps tensor `t` of rank 1 in a serial NVector.
let nvectorSerialWrap = lam t. nvectorSerialWrap t

external nvectorSerialUnwrap : NvectorSerial -> Tensor[Float]

-- `nvectorSerialUnwrap v` uwraps serial NVector `v` to a rank 1 tensor.
let nvectorSerialUnwrap = lam t. nvectorSerialUnwrap t

external sundialsMatrixDense : Int -> SundialsMatrixDense

-- `sundialsMatrixDense n` creates a square dense matrix of size `n` for use in
-- Sundials linear solvers, e.g. `idaDlsSolver`.
let sundialsMatrixDense = lam n. sundialsMatrixDense n

external sundialsMatrixDenseUnwrap ! : SundialsMatrixDense -> Tensor[Float]

-- `sundialsMatrixDenseUnwrap m` unwraps the sundials dense matrix `m` to a rank
-- 2 tensor.
let sundialsMatrixDenseUnwrap = lam m. sundialsMatrixDenseUnwrap m

external sundialsNonlinearSolverNewtonMake
  : NvectorSerial -> SundialsNonlinearSolver

-- `sundialsNonlinearSolverNewtonMake` creates a generic nonlinear solver based
-- on Newtons method.
let sundialsNonlinearSolverNewtonMake =
  lam y. sundialsNonlinearSolverNewtonMake y

external sundialsNonlinearSolverFixedPointMake
  : Int -> NvectorSerial -> SundialsNonlinearSolver

-- `sundialsNonlinearSolverFixedPointMake` creates a generic nonlinear solver
-- for fixed-point (functional) iteration with optional Anderson acceleration.
let sundialsNonlinearSolverFixedPointMake =
  lam n. lam y. sundialsNonlinearSolverFixedPointMake n y