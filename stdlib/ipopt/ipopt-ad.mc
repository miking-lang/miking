include "ad/dualnum.mc"
include "ipopt.mc"

-- for brevity
let num = dualnumNum
let unpack = compose dualnumPrimalDeep dualnumUnpackNum
let tset = tensorSetExn
let tget = tensorGetExn
let tcreate = tensorCreateCArrayFloat

type Vector = Tensor[Dualnum]

type IpoptAdCreateNLPArg = {
  -- Objective function f(x).
  f : Vector -> Dualnum,

  -- Constraint functions g_i(x).
  gs : [Vector -> Dualnum],

  -- Lower bounds on the variables xL_k.
  lb : [Float],

  -- Upper bounds on the variables xU_k.
  ub : [Float],

  -- Lower bounds on the constraints gL_i.
  constraintsLb : [Float],

  -- Upper bounds on the constraints gU_i.
  constraintsUb : [Float]
}

-- Creates a constrained NLP:
-- min_x[f(x)] s.t. xL_k ≤ x_k ≤ xU_k and gL_i ≤ g_i(x) ≤ gU_i.
-- This functions wraps `ipoptCreateNLP` and calculates Jacobians and the
-- Hessian using Automatic Differentation.
let ipoptAdCreateNLP : IpoptAdCreateNLPArg -> IpoptNLP
= lam arg.
  let nx = length arg.lb in
  let ng = length arg.constraintsLb in
  if and (eqi (length arg.ub) nx) (eqi (length arg.constraintsUb) ng)
  then
  if eqi (length arg.gs) ng then
      -- Pre-allocate some memory.
      let xd = tensorCreate [nx] (lam. num 0.) in
      let gradFd = tensorCreate [nx] (lam. num 0.) in
      let jacGd = tensorCreate [nx, ng] (lam. num 0.) in
      -- Computes f(x)
      let evalF = lam x.
        tensorMapExn (lam x. lam. num x) x xd;
        unpack (arg.f xd)
      in
      -- Computes g(x)
      let evalG = lam x. lam r.
        tensorMapExn (lam x. lam. num x) x xd;
        iteri (lam i. lam g. tset r [i] (unpack (g xd))) arg.gs;
        ()
      in
      -- We use this function to compute the Jacobian.
      let evalGd = lam x. lam r.
        iteri (lam i. lam g. tset r [i] (g x)) arg.gs
      in
      -- Computes 𝛁f(x)
      let evalGradF = lam x. lam gradF.
        tensorMapExn (lam x. lam. num x) x xd;
        grad arg.f xd gradFd;
        tensorMapExn (lam x. lam. unpack x) gradFd gradF;
        ()
      in
      -- jacT gives us the transpose of the Jacobian.
      let jacGStructure = join (create nx (lam i. create ng (lam j. (j, i)))) in
      let nJacG = muli ng nx in
      -- Computes 𝛁g(x)
      let evalJacG = lam x. lam jacG.
        tensorMapExn (lam x. lam. num x) x xd;
        jacT evalGd xd jacGd;
        tensorMapExn (lam x. lam. unpack x) (tensorReshapeExn jacGd [nJacG]) jacG;
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
              tset h [k] (mulf sigma (unpack (hessij arg.f [i] [j] xd)));
              iteri
                (lam l. lam g.
                  let hk = tget h [k] in
                  let ll = tget lambda [l] in
                  let gij = unpack (hessij g [i] [j] xd) in
                  tset h [k] (addf hk (mulf ll gij)))
                arg.gs
            else never)
          hStructure;
        ()
      in
      let lb = tensorOfSeqExn tcreate [nx] arg.lb in
      let ub = tensorOfSeqExn tcreate [nx] arg.ub in
      let constraintsLb = tensorOfSeqExn tcreate [ng] arg.constraintsLb in
      let constraintsUb = tensorOfSeqExn tcreate [ng] arg.constraintsUb in
      ipoptCreateNLP {
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
      }
    else error "ipoptAdCreateNLP: Shape mismatch between constraints"
  else error "ipoptAdCreateNLP: Shape mismatch between lower and upper bounds"

mexpr

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

let g0 = lam x.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  muln x0 (muln x1 (muln x2 x3))
in

let g1 = lam x.
  let x0 = tget x [0] in
  let x1 = tget x [1] in
  let x2 = tget x [2] in
  let x3 = tget x [3] in
  addn (muln x0 x0) (addn (muln x1 x1)
                    (addn (muln x2 x2) (muln x3 x3)))
in

let gs = [g0, g1] in

let lb = [1., 1., 1., 1.] in
let ub = [5., 5., 5., 5.] in
let constraintsLb = [25., 40.] in
let constraintsUb = [inf, 40.] in

let p = ipoptAdCreateNLP {
  f = f,
  gs = gs,
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
