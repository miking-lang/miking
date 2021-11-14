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
let ipoptCreateNLP : IpoptCreateNLPArg -> IpoptNLP =
lam arg.
  if
    forAll
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

let testSolve = lam p. lam x.
  utest
    match ipoptSolve p x with (SolveSucceeded _, obj) then
      print "\nObjective: ";
      printLn (float2string obj);
      printLn "Solution:";
      printLn (tensor2string float2string x);
      printLn "";
      true
    else false
  with true
  in
  ()
in

utest
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
    tset jacG [0] (mulf x1 (mulf x2 x3));   -- (0, 0)
    tset jacG [1] (mulf x0 (mulf x2 x3));   -- (0, 1)
    tset jacG [2] (mulf x0 (mulf x1 x3));   -- (0, 2)
    tset jacG [3] (mulf x0 (mulf x1 x2));   -- (0, 3)
    tset jacG [4] (mulf 2. x0);             -- (1, 0)
    tset jacG [5] (mulf 2. x1);             -- (1, 1)
    tset jacG [6] (mulf 2. x2);             -- (1, 2)
    tset jacG [7] (mulf 2. x3);             -- (1, 3)
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
  ipoptAddStrOption p "derivative_test" "second-order";

  let x = tensorOfSeqExn tcreate [4] [1., 5., 5., 1.] in

  testSolve p x;

  -- Find consistent initial values for a pendulum model expressed in Carteisan
  -- coordinates.
  -- the DAE is as follows:
  -- f1 = x1'' - x1 x3
  -- f2 = x2'' - x2 x3 + 1
  -- f3 = x1^2 + x2^2 - 1^2.
  --
  -- We augment this DAE with the last equation, the algebraic constraint,
  -- differentiated twice:
  -- f3' = 2x1'x2 + 2x'2x1
  -- f3'' = 2x1''x2 + 2x''2x1 + 2x1'x2' + 2x'2x1'.
  --
  -- From this we form the objective function
  -- f(x) = f1^2 + f2^2 + f3^2 + f3'^2 + f3''^2.
  --
  -- We add the following constraints:
  -- x1 = sin(pi/4) and x2 ≤ 0

  -- helper functions to more easily reuse output from mathematica
  let plus = foldl1 addf in
  let times = foldl1 mulf in
  let power = lam arg.
    match arg with [base, exp] then pow base exp
    else never
  in
  let rational = foldl1 divf in

  let evalF = lam v.
    let x = tget v [0] in
    let dx = tget v [1] in
    let ddx = tget v [2] in
    let y = tget v [3] in
    let dy = tget v [4] in
    let ddy = tget v [5] in
    let z = tget v [6] in
    plus [power [plus [times [2., power [dx, 2.]], times[2., power [dy, 2.]], times [2., ddx, x], times [2., ddy, y]], 2.], power [plus [times [2., dx, x], times [2., dy, y]], 2.], power [plus [negf 1., power [x, 2.], power [y, 2.]], 2.], power [plus [ddx, times [negf 1., x, z]], 2.], power [plus [1., ddy, times [negf 1., y, z]], 2.]]
  in

  let evalGradF = lam v. lam gradF.
    let x = tget v [0] in
    let dx = tget v [1] in
    let ddx = tget v [2] in
    let y = tget v [3] in
    let dy = tget v [4] in
    let ddy = tget v [5] in
    let z = tget v [6] in
    tset gradF [0] (plus [times [8., ddx, plus [power [dx, 2.], power [dy, 2.], times [ddx, x], times [ddy, y]]], times [8., dx, plus [times [dx, x], times [dy, y]]], times [4., x, plus [negf 1., power [x, 2.], power [y, 2.]]], times [2., z, plus [times [negf 1., ddx], times [x, z]]]]);
    tset gradF [1] (times [8., plus [times [2., power [dx, 3.]], times [dy, x, y], times [dx, plus [times [2., power [dy, 2.]], times [2., ddx, x], power [x, 2.], times [2., ddy, y]]]]]);
    tset gradF [2] (times [2., plus [ddx, times [4., x, plus [power [dx, 2.], power [dy, 2.], times [ddx, x], times [ddy, y]]], times [negf 1., x, z]]]);
    tset gradF [3] (plus [times [8., ddy, plus [power [dx, 2.], power [dy, 2.], times [ddx, x], times [ddy, y]]], times [8., dy, plus [times [dx, x], times [dy, y]]], times [4., y, plus [negf 1., power [x, 2.], power [y, 2.]]], times [negf 2., z, plus [1., ddy, times [negf 1., y, z]]]]);
    tset gradF [4] (times [8., plus [times [2., power [dx, 2.], dy], times [dx, x, y], times [dy, plus [times [2., power [dy, 2.]], times [2., ddx, x], times [2., ddy, y], power [y, 2.]]]]]);
    tset gradF [5] (times [2., plus [1., ddy, times [4., y, plus [power [dx, 2.], power [dy, 2.], times [ddx, x], times [ddy, y]]], times [negf 1., y, z]]]);
    tset gradF [6] (plus [times [2., x, plus [times [negf 1., ddx], times [x, z]]], times [negf 2., y, plus [1., ddy, times [negf 1., y, z]]]]);
    ()
  in

  let evalG = lam v. lam g.
    let x = tget v [0] in
    let dx = tget v [1] in
    let ddx = tget v [2] in
    let y = tget v [3] in
    let dy = tget v [4] in
    let ddy = tget v [5] in
    let z = tget v [6] in
    tset g [0] (plus [times [negf 1., power [2., rational [negf 1., 2.]]], x]);
    tset g [1] y;
    ()
  in

  let jacGStructure =
    [(0, 0), (1, 3)]
  in

  let evalJacG = lam. lam jacG.
    tset jacG [0] 1.;
    tset jacG [1] 1.;
    ()
  in

  let hStructure =
  [
    (0, 0),
    (1, 0),
    (2, 0),
    (3, 0),
    (4, 0),
    (5, 0),
    (6, 0),
    (1, 1),
    (2, 1),
    (3, 1),
    (4, 1),
    (5, 1),
    -- (6, 1) is zero
    (2, 2),
    (3, 2),
    (4, 2),
    (5, 2),
    (6, 2),
    (3, 3),
    (4, 3),
    (5, 3),
    (6, 3),
    (4, 4),
    (5, 4),
    -- (6, 4) is zero
    (5, 5),
    (6, 5),
    (6, 6)
  ]
  in

  let evalH = lam sigma. lam v. lam. lam h.
    let x = tget v [0] in
    let dx = tget v [1] in
    let ddx = tget v [2] in
    let y = tget v [3] in
    let dy = tget v [4] in
    let ddy = tget v [5] in
    let z = tget v [6] in
    -- (0, 0)
    tset h [0] (times [2., plus [negf 2., times [4., power [ddx, 2.]], times [4., power [dx, 2.]], times [6., power [x, 2.]], times [2., power [y, 2.]], power [z, 2.]]]);
    -- (1, 0)
    tset h [1] (times [8., plus [times [2., ddx, dx], times [2., dx, x], times [dy, y]]]);
    -- (2, 0)
    tset h [2] (plus [times [8., power [dx, 2.]], times [8., power [dy, 2.]], times [16., ddx, x], times [8., ddy, y], times [negf 2., z]]);
    -- (3, 0)
    tset h [3] (times [8., plus [times [ddx, ddy], times [dx, dy], times [x, y]]]);
    -- (4, 0)
    tset h [4] (times [8., plus [times [2., ddx, dy], times [dx, y]]]);
    -- (5, 0)
    tset h [5] (times [8., ddx, y]);
    -- (6, 0)
    tset h [6] (plus [times [negf 2., ddx], times [4., x, z]]);
    -- (1, 1)
    tset h [7] (times [8., plus [times [6., power [dx, 2.]], times [2., power [dy, 2.]], times [2., ddx, x], power [x, 2.], times [2., ddy, y]]]);
    -- (2, 1)
    tset h [8] (times [16., dx, x]);
    -- (3, 1)
    tset h [9] (times [8., plus [times [2., ddy, dx], times [dy, x]]]);
    -- (4, 1)
    tset h [10] (times [8., plus [times [4., dx, dy], times [x, y]]]);
    -- (5, 1)
    tset h [11] (times [16., dx, y]);
    -- (6, 1) is zero
    -- (2, 2)
    tset h [12] (plus [2., times [8., power [x, 2.]]]);
    -- (3, 2)
    tset h [13] (times [8., ddy, x]);
    -- (4, 2)
    tset h [14] (times [16., dy, x]);
    -- (5, 2)
    tset h [15] (times [8., x, y]);
    -- (6, 2)
    tset h [16] (times [negf 2., x]);
    -- (3, 3)
    tset h [17] (times [2., plus [negf 2., times [4., power [ddy, 2.]], times [4., power [dy, 2.]], times [2., power [x, 2.]], times [6., power [y, 2.]], power [z, 2.]]]);
    -- (4, 3)
    tset h [18] (times [8., plus [times [2., ddy, dy], times [dx, x], times [2., dy, y]]]);
    -- (5, 3)
    tset h [19] (plus [times [8., power [dx, 2.]], times [8., power [dy, 2.]], times [8., ddx, x], times [16., ddy, y], times [negf 2., z]]);
    -- (6, 3)
    tset h [20] (times [negf 2., plus [1., ddy, times [negf 2., y, z]]]);
    -- (4, 4)
    tset h [21] (times [8., plus [times [2., power [dx, 2.]], times [6., power [dy, 2.]], times [2., ddx, x], times [2., ddy, y], power [y, 2.]]]);
    -- (5, 4)
    tset h [22] (times [16., dy, y]);
    -- (6, 4) is zero
    -- (5, 5)
    tset h [23] (plus [2., times [8., power [y, 2.]]]);
    -- (6, 5)
    tset h [24] (times [negf 2.,  y]);
    -- (6, 6)
    tset h [25] (times [2., plus [power [x, 2.], power [y, 2.]]]);
    tensorMapInplace (mulf sigma) h;
    ()
  in

  let lb = tcreate [7] (lam. negf inf) in
  let ub = tcreate [7] (lam. inf) in
  let constraintsLb = tensorOfSeqExn tcreate [2] [0., negf inf] in
  let constraintsUb = tensorOfSeqExn tcreate [2] [0., 0.] in

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
  ipoptAddStrOption p "derivative_test" "second-order";

  let x = tcreate [7] (lam. 0.) in
  tset x [0] (sin (divf pi 4.));
  tset x [3] (mulf (negf 1.) (cos (divf pi 4.)));
  testSolve p x
with () in

()
