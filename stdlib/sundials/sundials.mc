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

external sundialsMatrixDenseUnwrap : SundialsMatrixDense -> Tensor[Float]

-- `sundialsMatrixDenseUnwrap m` unwraps the sundials dense matrix `m` to a rank
-- 2 tensor. This tensor will be the transpose of the input matrix `m`.
let sundialsMatrixDenseUnwrap = lam m. sundialsMatrixDenseUnwrap m

external sundialsMatrixDenseGet : SundialsMatrixDense -> Int -> Int -> Float

-- `sundialsMatrixDenseGet m i j` gets the `i`,`j`'th element in `m`.
let sundialsMatrixDenseGet = lam m. lam i. lam j. sundialsMatrixDenseGet m i j

external sundialsMatrixDenseSet ! : SundialsMatrixDense -> Int -> Int -> Float -> ()

-- `sundialsMatrixDenseSet m i j v` sets, inplace, the `i`,`j`'th element in `m`
-- to the value `v`.
let sundialsMatrixDenseSet = lam m. lam i. lam j. lam v. sundialsMatrixDenseSet m i j v

external sundialsMatrixDenseUpdate !
  : SundialsMatrixDense -> Int -> Int -> (Float -> Float) -> ()

-- `sundialsMatrixDenseUpdate m i j f` updates, inplace, the `i`,`j`'th element
-- in `m` according to the function `f`, where the argument to this function is
-- the current value at that index in `m`.
let sundialsMatrixDenseUpdate = lam m. lam i. lam j. lam f.
  sundialsMatrixDenseUpdate m i j f

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
