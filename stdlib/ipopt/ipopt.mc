/-
  Miking interface to the IPOPT constrained Non-Linear Program (NLP) solver.
  @see <https://coin-or.github.io/Ipopt/index.html> for the IPOPT documentation.
-/

include "math.mc"
include "tensor.mc"
include "common.mc"

type IpoptNLP                     -- Constrained Non-Linear Program
type IpoptApplicationReturnStatus -- Internal representation of return status

type Vector = Tensor[Float]

-- Callback function to evaluate the objective function f(x). The function
-- argument `x` is the values of the variables.
type IpoptEvalF = Vector -> Float

-- Callback function to evaluate the gradient 𝛁f(x) of the objective
-- function. The function arguments are:
--   - `x`, the values of the variables,
--   - `grad_f`, a vector for storing the values of 𝛁f(x), in the same order
--               as `x`. I.e. `grad_f[i]` should hold the value of the gradient
--               of f(x) with respect to `x[i]`.
type IpoptEvalGradF = Vector -> Vector -> ()

-- Callback function to evaluate the constraints g(x). The function arguments
-- are:
--   - `x`, the values of the variables,
--   - `g`, a vector for storing the value of g(x).
type IpoptEvalG = Vector -> Vector -> ()

-- Encodes the structure of a sparse matrix. The tuple `(i, j)` in position `k`
-- associates the matrix element `m[i, j]` with the sequence element `a[k]`. If
-- `(i, j)` appears multiple times in the structure sequence, `m[i, j]` is
-- associated with the sum of these elements in `a`. Matrix elements missing
-- from the structure sequence are assumed to be zero.
-- @see <https://coin-or.github.io/Ipopt/IMPL.html#TRIPLET> for documentation on
-- the triplet format.
type IpoptStructure = [(Int, Int)]

-- Callback function to evaluate the Jacobian 𝛁g(x)^T of the constraints. The
-- function arguments are:
-- - `x`, the values of the variables,
-- - `jac_g`, a vector for storing the non-zero values of 𝛁g(x)^T, where
--            `jac_g` assumes some pre-defined structure.
type IpoptEvalJacG = Vector -> Vector -> ()


-- Callback function to evaluate the Hessian
-- σ𝛁^2f(x_k) + Σ_i[λ_i𝛁^2g_i(x_k)]
-- of the Lagrangian. The function arguments are:
-- - `sigma`, the factor σ in front of the objective term,
-- - `x`, the values of the variables,
-- - `lambda`, the values of the constraint multiplier λ,
-- - `h`, a vector for storing the non-zero values of the Hessian, where `h`
--        assumes some pre-defined structure. This Hessian is symmetric and
--        only the lower diagonal entries must be specified.
type IpoptEvalH = Float -> Vector -> Vector -> Vector -> ()


type IpoptReturnStatus
con SolveSucceeded : () -> IpoptReturnStatus
con SolvedToAcceptableLevel : () -> IpoptReturnStatus
con InfeasibleProblemDetected : () -> IpoptReturnStatus
con SearchDirectionBecomesTooSmall : () -> IpoptReturnStatus
con DivergingIterates : () -> IpoptReturnStatus
con UserRequestedStop : () -> IpoptReturnStatus
con FeasiblePointFound : () -> IpoptReturnStatus
con MaximumIterationsExceeded : () -> IpoptReturnStatus
con RestorationFailed : () -> IpoptReturnStatus
con ErrorInStepComputation : () -> IpoptReturnStatus
con MaximumCpuTimeExceeded : () -> IpoptReturnStatus
con NotEnoughDegreesOfFreedom : () -> IpoptReturnStatus
con InvalidProblemDefinition : () -> IpoptReturnStatus
con InvalidOption : () -> IpoptReturnStatus
con InvalidNumberDetected : () -> IpoptReturnStatus
con UnrecoverableException : () -> IpoptReturnStatus
con NonIpoptExceptionThrown : () -> IpoptReturnStatus
con InsufficientMemory : () -> IpoptReturnStatus
con InternalError : () -> IpoptReturnStatus


external externalIpoptApplicationReturnStatusRetcode
  : IpoptApplicationReturnStatus -> Int

let _rctoreturnstatus = lam rc : Int.
  if eqi rc 0 then SolveSucceeded ()
  else if eqi rc 1 then SolvedToAcceptableLevel ()
  else if eqi rc 2 then InfeasibleProblemDetected ()
  else if eqi rc 3 then SearchDirectionBecomesTooSmall ()
  else if eqi rc 4 then DivergingIterates ()
  else if eqi rc 5 then UserRequestedStop ()
  else if eqi rc 6 then FeasiblePointFound ()
  else if eqi rc (negi 1) then MaximumIterationsExceeded ()
  else if eqi rc (negi 2) then RestorationFailed ()
  else if eqi rc (negi 3) then ErrorInStepComputation ()
  else if eqi rc (negi 4) then MaximumCpuTimeExceeded ()
  else if eqi rc (negi 10) then NotEnoughDegreesOfFreedom ()
  else if eqi rc (negi 11) then InvalidProblemDefinition ()
  else if eqi rc (negi 12) then InvalidOption ()
  else if eqi rc (negi 13) then InvalidNumberDetected ()
  else if eqi rc (negi 100) then UnrecoverableException ()
  else if eqi rc (negi 101) then NonIpoptExceptionThrown ()
  else if eqi rc (negi 102) then InsufficientMemory ()
  else if eqi rc (negi 199) then InternalError ()
  else error "Ipopt._rctoreturnstatus: Unknown return code"


external externalIpoptCreateNLP
  : IpoptEvalF ->
    IpoptEvalGradF ->
    IpoptEvalG ->
    IpoptStructure ->
    IpoptEvalJacG ->
    IpoptStructure ->
    IpoptEvalH ->
    Vector ->
    Vector ->
    Vector ->
    Vector ->
    IpoptNLP

type IpoptCreateNLPArg = {
  -- Callback function to evaluate objective function.
  evalF : IpoptEvalF,

  -- Callback function to evaluate the gradient of the objective function.
  evalGradF : IpoptEvalGradF,

  -- Callback function to evaluate the constraint function.
  evalG : IpoptEvalG,

  -- Structure of the constraint Jacobian.
  jacGStructure : IpoptStructure,

  -- Callback function to evalute the Jacobian of the constraint function
  evalJacG : IpoptEvalJacG,

  -- Structure of the Hessian of the Lagrangian.
  hStructure : IpoptStructure,

  -- Callback function to evaluate the Hessian of the Lagrangian.
  evalH : IpoptEvalH,

  -- Lower bounds on the variables xL_k.
  lb : Vector,

  -- Upper bounds on the variables xU_k.
  ub : Vector,

  -- Lower bounds on the constraints gL_i.
  constraintsLb : Vector,

  -- Upper bounds on the constraints gU_i.
  constraintsUb : Vector
}

-- Creates a constrained NLP:
-- min_x[f(x)] s.t. xL_k ≤ x_k ≤ xU_k and gL_i ≤ g_i(x) ≤ gU_i.
let ipoptCreateNLP : IpoptCreateNLPArg -> IpoptNLP = lam arg.
  if
    all
      (flip tensorHasRank 1)
      [arg.lb, arg.ub, arg.constraintsLb, arg.constraintsUb]
  then
    let nx = tensorSize arg.lb in
    let ng = tensorSize arg.constraintsLb in
    if
      and
        (tensorHasSameShape arg.lb arg.ub)
        (tensorHasSameShape arg.constraintsLb arg.constraintsUb)
    then
      -- copy over constraints to carrays
      let lb = tensorCreateCArrayFloat [nx] (tensorGetExn arg.lb) in
      let ub = tensorCreateCArrayFloat [nx] (tensorGetExn arg.ub) in
      let constraintsLb =
        tensorCreateCArrayFloat [ng] (tensorGetExn arg.constraintsLb)
      in
      let constraintsUb =
        tensorCreateCArrayFloat [ng] (tensorGetExn arg.constraintsUb)
      in
      externalIpoptCreateNLP
        arg.evalF
        arg.evalGradF
        arg.evalG
        arg.jacGStructure
        arg.evalJacG
        arg.hStructure
        arg.evalH
        lb
        ub
        constraintsLb
        constraintsUb
    else error "Invalid Argument: ipoptCreateNLP"
  else error "Invalid Argument: ipoptCreateNLP"

external externalIpoptAddStrOption ! : IpoptNLP -> String -> String -> ()

-- `ipoptAddStrOption p key val` sets the option `key` to the `String` value
-- `val` in the NLP `p`. @see <https://coin-or.github.io/Ipopt/OPTIONS.html> for
-- a summary of options.
let ipoptAddStrOption : IpoptNLP -> String -> String -> ()
= lam p. lam key. lam val. externalIpoptAddStrOption p key val


external externalIpoptAddNumOption ! : IpoptNLP -> String -> Float -> ()

-- As `ipoptAddStrOption`, but for `Float` values.
let ipoptAddNumOption : IpoptNLP -> String -> Float -> ()
= lam p. lam key. lam val. externalIpoptAddNumOption p key val


external externalIpoptAddIntOption ! : IpoptNLP -> String -> Int -> ()

-- As `ipoptAddStrOption`, but for `Int` values.
let ipoptAddIntOption : IpoptNLP -> String -> Int -> ()
= lam p. lam key. lam val. externalIpoptAddIntOption p key val


external externalIpoptSolve !
  : IpoptNLP -> Vector -> (IpoptApplicationReturnStatus, Float)

-- `solve p x` tries to solve the constrained NLP `p` with initial values `x`.
-- The function arguments are:
-- - `p`, the constrained NLP,
-- - `x`, Initial values of the variables. Will hold the optimal solution after
--        calling `solve`.
-- Returns: The tuple tuple `(rs, f)`, where `rs` is the return status and `f`
--          is the final value of the objective function.
let ipoptSolve : IpoptNLP -> Vector -> (IpoptReturnStatus, Float)
= lam p. lam x.
  match externalIpoptSolve p x with (r, f) then
    (_rctoreturnstatus (externalIpoptApplicationReturnStatusRetcode r), f)
  else never

mexpr

let tget = tensorGetExn in
let tset = tensorSetExn in
let tcreate = tensorCreateCArrayFloat in

-- Example problem from https://coin-or.github.io/Ipopt/
-- min_x f(x), where f(x) = x[0]x[3](x[0] + x[1] + x[2]) + x[2],
-- s.t.
--  x[0]x[1]x[2]x[3] ≥ 25,
--  x[0]^2 + x[1]^2 + x[2]^2 + x[3]^2 = 40,
--  1 ≤ x[0], x[1], x[2], x[3] ≤ 5.

let evalF = lam x.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  addf (mulf x0 (mulf x3 (addf x0 (addf x1 x2)))) x2
in

let evalGradF = lam x. lam gradF.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  tset gradF [0] (addf (mulf x0 x3) (mulf x3 (addf x0 (addf x1 x2))));
  tset gradF [1] (mulf x0 x3);
  tset gradF [2] (addf (mulf x0 x3) 1.);
  tset gradF [3] (mulf x0 (addf x0 (addf x1 x2)));
  ()
in

let evalG = lam x. lam g.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  tset g [0] (mulf x0 (mulf x1 (mulf x2 x3)));
  tset g [1] (addf (mulf x0 x0) (addf (mulf x1 x1)
                                      (addf (mulf x2 x2) (mulf x3 x3))));
  ()
in

let jacGStructure =
  [ (0, 0)
  , (0, 1)
  , (0, 2)
  , (0, 3)
  , (1, 0)
  , (1, 1)
  , (1, 2)
  , (1, 3) ]
in

let evalJacG = lam x. lam jacG.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  tset jacG [0] (mulf x1 (mulf x2 x3));
  tset jacG [1] (mulf x0 (mulf x2 x3));
  tset jacG [2] (mulf x0 (mulf x1 x3));
  tset jacG [3] (mulf x0 (mulf x1 x2));
  tset jacG [4] (mulf 2. x0);
  tset jacG [5] (mulf 2. x1);
  tset jacG [6] (mulf 2. x2);
  tset jacG [7] (mulf 2. x3);
  ()
in

let hStructure =
  [ (0, 0)
  , (1, 0)
  , (1, 1)
  , (2, 0)
  , (2, 1)
  , (2, 2)
  , (3, 0)
  , (3, 1)
  , (3, 2)
  , (3, 3) ]
in

let evalH = lam sigma. lam x. lam lambda. lam h.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  let l0 = tget lambda [0] in
  let l1 = tget lambda [1] in
  tset h [0] (mulf sigma (mulf 2. x3));
  tset h [1] (mulf sigma x3);
  tset h [2] 0.;
  tset h [3] (mulf sigma x3);
  tset h [4] 0.;
  tset h [5] 0.;
  tset h [6] (mulf sigma (addf (mulf 2. x0) (addf x1 x2)));
  tset h [7] (mulf sigma x0);
  tset h [8] (mulf sigma x0);
  tset h [9] 0.;
  tset h [1] (addf (tget h [1]) (mulf l0 (mulf x2 x3)));
  tset h [3] (addf (tget h [3]) (mulf l0 (mulf x1 x3)));
  tset h [4] (addf (tget h [4]) (mulf l0 (mulf x0 x3)));
  tset h [6] (addf (tget h [6]) (mulf l0 (mulf x1 x2)));
  tset h [7] (addf (tget h [7]) (mulf l0 (mulf x0 x2)));
  tset h [8] (addf (tget h [8]) (mulf l0 (mulf x0 x1)));
  tset h [0] (addf (tget h [0]) (mulf l1 2.));
  tset h [2] (addf (tget h [2]) (mulf l1 2.));
  tset h [5] (addf (tget h [5]) (mulf l1 2.));
  tset h [9] (addf (tget h [9]) (mulf l1 2.));
  ()
in

let lb = tensorOfSeqExn tcreate [4] [1., 1., 1., 1.] in
let ub = tensorOfSeqExn tcreate [4] [5., 5., 5., 5.] in
let constraintsLb = tensorOfSeqExn tcreate [2] [25., 40.] in
let constraintsUb = tensorOfSeqExn tcreate [2] [inf, 40.] in

let p = ipoptCreateNLP {
  evalF = evalF,
  evalGradF = evalGradF,
  evalG = evalG,
  jacGStructure = jacGStructure,
  evalJacG = evalJacG,
  hStructure = hStructure,
  evalH = evalH,
  lb = lb,
  ub = ub,
  constraintsLb = constraintsLb,
  constraintsUb = constraintsUb
} in

ipoptAddNumOption p "tol" 3.82e-6;
ipoptAddStrOption p "mu_strategy" "adaptive";

let x = tensorOfSeqExn tcreate [4] [1., 5., 5., 1.] in

utest
  match ipoptSolve p x with (SolveSucceeded _, _) then true
  else false
with true
in

()
