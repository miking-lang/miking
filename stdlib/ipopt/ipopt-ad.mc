include "ad/dualnum.mc"
include "ipopt.mc"

-- for brevity
let num = dualnumNum
let primalDeep = dualnumPrimalDeep
let tset = tensorSetExn
let tget = tensorGetExn
let tcreate = tensorCreateCArrayFloat

type Vector a = Tensor[a]

type IpoptAdCreateNLPArg = {
  -- Objective function f(x).
  f : Vector Dualnum -> Dualnum,

  -- Constraint functions g_i(x).
  g : Vector Dualnum -> Vector Dualnum,

  -- Lower bounds on the variables xL_k.
  lb : Vector Float,

  -- Upper bounds on the variables xU_k.
  ub : Vector Float,

  -- Lower bounds on the constraints gL_i.
  constraintsLb : Vector Float,

  -- Upper bounds on the constraints gU_i.
  constraintsUb : Vector Float
}

-- Creates a constrained NLP:
-- min_x[f(x)] s.t. xL_k ≤ x_k ≤ xU_k and gL_i ≤ g_i(x) ≤ gU_i.
-- This functions wraps `ipoptCreateNLP` and calculates Jacobians and the
-- Hessian using Automatic Differentation.
let ipoptAdCreateNLP : IpoptAdCreateNLPArg -> IpoptNLP
= lam arg.
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
      -- Pre-allocate some memory.
      let xd = tensorCreate [nx] (lam. num 0.) in
      let gd = tensorCreate [ng] (lam. num 0.) in
      let gradFd = tensorCreate [nx] (lam. num 0.) in
      let jacGd = tensorCreate [nx, ng] (lam. num 0.) in
      let hij = tensorCreate [ng] (lam. 0.) in
      let hijd = tensorCreate [ng] (lam. num 0.) in
      -- Computes f(x)
      let evalF = lam x.
        tensorMapExn (lam x. lam. num x) x xd;
        primalDeep (arg.f xd)
      in
      -- Computes g(x)
      let evalG = lam x. lam g.
        tensorMapExn (lam x. lam. num x) x xd;
        arg.g xd gd;
        tensorMapExn (lam x. lam. primalDeep x) gd g;
        ()
      in
      -- Computes 𝛁f(x)
      let evalGradF = lam x. lam gradF.
        tensorMapExn (lam x. lam. num x) x xd;
        grad arg.f xd gradFd;
        tensorMapExn (lam x. lam. primalDeep x) gradFd gradF;
        ()
      in
      -- jacT gives us the transpose of the Jacobian.
      let jacGStructure = join (create nx (lam i. create ng (lam j. (j, i)))) in
      let nJacG = muli ng nx in
      -- Computes 𝛁g(x)
      let evalJacG = lam x. lam jacG.
        tensorMapExn (lam x. lam. num x) x xd;
        jacT arg.g xd jacGd;
        tensorMapExn
          (lam x. lam. primalDeep x)
          (tensorReshapeExn jacGd [nJacG]) jacG;
        ()
      in
      -- The Hessian of the Lagrangian is symmetric so we only need the lower
      -- triangular part.
      let hStructure =
        join
          (create
            nx
            (lam i.
              unfoldr
                (lam j. if gti j i then None () else Some ((i, j), succ j))
                0))
      in
      -- Computes σ𝛁^2f(x_k) + Σ_i[λ_i𝛁^2g_i(x_k)]
      let evalH = lam sigma. lam x. lam lambda. lam h.
        tensorMapExn (lam x. lam. num x) x xd;
        iteri
          (lam k : Int. lam ij : (Int, Int).
            match ij with (i, j) then
              tset h [k] (mulf sigma (primalDeep (hessij arg.f i j xd)));
              hessijs arg.g i j xd hijd;
              tensorMapExn (lam x. lam. primalDeep x) hijd hij;
              tensorMapExn mulf lambda hij;
              tset h [k] (tensorFold addf (tget h [k]) hij);
              ()
            else never)
          hStructure;
        ()
      in
      ipoptCreateNLP {
        evalF = evalF,
        evalGradF = evalGradF,
        evalG = evalG,
        jacGStructure = jacGStructure,
        evalJacG = evalJacG,
        hStructure = hStructure,
        evalH = evalH,
        lb = arg.lb,
        ub = arg.ub,
        constraintsLb = arg.constraintsLb,
        constraintsUb = arg.constraintsUb
      }
  else error "Invalid Argument: ipoptAdCreateNLP"
  else error "Invalid Argument: ipoptAdCreateNLP"

mexpr

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

-- Example problem from https://coin-or.github.io/Ipopt/
-- min_x f(x), where f(x) = x[0]x[3](x[0] + x[1] + x[2]) + x[2],
-- s.t.
--  x[0]x[1]x[2]x[3] ≥ 25,
--  x[0]^2 + x[1]^2 + x[2]^2 + x[3]^2 = 40,
--  1 ≤ x[0], x[1], x[2], x[3] ≤ 5.

let f = lam x.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  addn (muln x0 (muln x3 (addn x0 (addn x1 x2)))) x2
in

let g = lam x. lam r.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  tset r [0] (muln x0 (muln x1 (muln x2 x3)));
  tset r [1] (addn (muln x0 x0) (addn (muln x1 x1)
                                (addn (muln x2 x2) (muln x3 x3))));
  ()
in

let lb = tensorOfSeqExn tcreate [4] [1., 1., 1., 1.] in
let ub = tensorOfSeqExn tcreate [4] [5., 5., 5., 5.] in
let constraintsLb = tensorOfSeqExn tcreate [2] [25., 40.] in
let constraintsUb = tensorOfSeqExn tcreate [2] [inf, 40.] in

let p = ipoptAdCreateNLP {
  f = f,
  g = g,
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
-- The DAE is as follows:
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

let f = lam x.
  let x1 = tget x [0] in
  let dx1 = tget x [1] in
  let ddx1 = tget x [2] in
  let x2 = tget x [3] in
  let dx2 = tget x [4] in
  let ddx2 = tget x [5] in
  let x3 = tget x [6] in
  let f1 = subn ddx1 (muln x1 x3) in
  let f2 = addn (subn ddx2 (muln x2 x3)) (num 1.) in
  let f3 = subn (addn (muln x1 x1) (muln x2 x2)) (num 1.) in
  let df3 = muln (num 2.) (addn (muln dx1 x1) (muln dx2 x2)) in
  let ddf3 =
    addn
      (muln (num 2.) (addn (muln ddx1 x1) (muln ddx2 x2)))
      (muln (num 2.) (addn (muln dx1 dx1) (muln dx2 dx2)))
  in
  foldl (lam r. lam f. addn r (muln f f)) (num 0.) [f1, f2, f3, df3, ddf3]
in

let g = lam x. lam r.
  let x1 = tget x [0] in
  let x2 = tget x [3] in
  tset r [0] (subn x1 (sinn (num (divf pi 4.))));
  tset r [1] x2;
  ()
in

let lb = tcreate [7] (lam. negf inf) in
let ub = tcreate [7] (lam. inf) in
let constraintsLb = tensorOfSeqExn tcreate [2] [0., negf inf] in
let constraintsUb = tensorOfSeqExn tcreate [2] [0., 0.] in

let p = ipoptAdCreateNLP {
  f = f,
  g = g,
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
testSolve p x;

()
