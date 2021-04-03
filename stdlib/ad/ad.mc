-- This file contains implementations of nestable derivative operators and
-- related functions using the dual-number API described in this paper:

-- Siskind, Jeffrey Mark, and Barak A. Pearl mutter. “Nesting Forward-Mode AD in
-- a Functional Framework.” Higher-Order and Symbolic Computation 21, no. 4
-- (December 1, 2008): 361–76. https://doi.org/10.1007/s10990-008-9037-1.



include "dualnum-arith.mc"
include "dualnum-bool.mc"
include "vec.mc"
include "string.mc"

let num = dualnumNum
let dnum = dualnumDNum
let genEpsilon = dualnumGenEpsilon
let pertubation = dualnumPertubation
let zeron = lam n. make n (num 0.)

-- directed derivative of vector function f at x in the direction xp
let dder : ([DualNum] -> [DualNum]) -> [DualNum] -> [DualNum] -> ([DualNum] -> [DualNum]) =
lam f. lam x. lam xp.
  let e = genEpsilon () in
  map (pertubation e) (f (vecBop (dnum e) x xp))

-- derivative of scalar function f at x
let der : (DualNum -> DualNum) -> DualNum -> (DualNum -> DualNum) =
lam f. lam x. head (dder (lam x. [f (head x)]) [x] [num 1.])

-- n'th derivative of scalar function f at x
recursive
let dern : Int -> (DualNum -> DualNum) -> DualNum -> (DualNum -> DualNum) =
lam n. lam f. lam x.
  if lti n 0 then error "Negative derivative order"
  else if eqi n 0 then f x
  else dern (subi n 1) (der f) x
end

let der2 = dern 2

-- j'th column of the Jacobian of function f at x
let jacj = lam f. lam x. lam j.
  let n = length x in
  let xp = set (zeron n) j (num 1.) in
  dder f x xp

-- transpose of Jacobian of f at x
let jac : ([DualNum] -> [DualNum]) -> [DualNum] -> [[DualNum]] =
lam f. lam x. mapi (lam j. lam. jacj f x j) x

-- gradient of f at x
let grad : ([DualNum] -> DualNum) -> [DualNum] -> [DualNum] =
lam f. lam x. join (jac (lam x. [f x]) x)

mexpr

let x2 = lam x. muln x x in

-- test der
utest der negn (num 2.) with num (negf 1.) in
utest der x2 (num 3.) with num 6. in
utest der (der x2) (num 2.) with num 2. in

recursive let xn = lam n. lam x.
  if eqi n 0 then num 1.
  else muln x (xn (subi n 1) x)
in

let fs = unfoldr (lam b. if eqi b 0 then None ()
                         else Some (xn b, subi b 1))
                 10
in

let num10to1 = unfoldr (lam b. if eqi b 0 then None ()
                               else Some (num (int2float b), subi b 1 ))
                       10
in

utest map (lam f. der f (num 1.)) fs with num10to1 in

let derFs = unfoldr (lam b. if eqi b.0 0 then None ()
                            else Some (b.1 (num 1.), (subi b.0 1, der b.1)))
                    (4, xn 4)
in

utest derFs with [num 1., num 4., num 12., num 24.] in

let xDxy = lam y. lam x. muln x (der (lam y. muln y x) y) in
utest der (xDxy (num 2.)) (num 1.) with num 2. in

-- test dder
let x0x1 = lam x. [muln (get x 0) (get x 1)] in
utest dder x0x1 [num 1., num 0.] [num 1., num 2.] with [num 2.] in

let x0x0Dx1 = lam x.
  [muln (get x 0) (der (lam x1. muln (get x 0) x1) (get x 1))]
in

utest dder x0x0Dx1 [num 1., num 2.] [num 1., num 0.] with [num 2.] in

let f_u = lam u. [muln (get u 0) (get u 1),
                  addn (get u 0) (get u 1)]
in

utest dder f_u [num 1., num 2.] [num 1., num 0.] with [num 2., num 1.]
in

utest dder f_u [num 1., num 2.] [num 0., num 1.] with [num 1., num 1.]
in

-- test dern
utest dern 0 x2 (num 1.) with x2 (num 1.) in
utest dern 2 x2 (num  1.) with der (der x2) (num 1.) in

-- test jac
utest jac x0x1 [num 1., num 2.] with [[num 2.], [num 1.]] in
utest jac f_u [num 1., num 2.] with [[num 2., num 1.], [num 1., num 1.]] in

-- test grad
utest grad (lam x. addn (get x 0) (get x 1)) [num 2., num 3.]
with [num 1., num 1.] in

utest grad (lam x. subn (get x 0) (get x 1)) [num 2., num 3.]
with [num 1., num (negf 1.)] in

utest grad (lam x. muln (get x 0) (get x 1)) [num 2., num 3.]
with [num 3., num 2.] in

utest grad (lam x. divn (get x 0) (get x 1)) [num 2., num 3.]
with [num (divf 1. 3.), num (divf (negf 2.) (9.))] in

-- test Newton-Raphsons implementation

let ex = num 1.e-6 in
let ef = num 0.001 in
let x0 = num 10. in

let newtonRaphsons = lam f.
  recursive let work = lam x.
    let fp = der f x in
    if eqn fp (num 0.) then error "Initial guess lies on saddle point"
    else
      let xn = subn x (divn (f x) fp) in
      let dx = subn x xn in
      if ltn (muln dx dx) (muln ex ex) then xn -- Naive convergence check
      else work xn
  in
  work x0
in

let root = newtonRaphsons in

-- checks if tr is sufficiently close to fnd
let isCorrect = lam tr. lam fnd.
  let err = subn tr fnd in
  leqn (muln err err) (muln ef ef)
in

let f1 = lam x. addn x (num 2.) in
let root1 = num (negf 2.) in
let froot1 = root f1 in

utest isCorrect root1 froot1 with true in

let f2 = lam x. subn (muln x x) (num 4.) in
let root2a = num (negf 2.) in
let root2a = num 2. in
let froot2 = root f2 in

utest or (isCorrect root2a froot2)
         (isCorrect root2a froot2)

with true in

let f3 = lam x. subn (muln (muln x x) x) (num 8.) in
let root3 = num 2. in
let froot3 = root f3 in

utest isCorrect root3 froot3 with true in

-- test stationary point function

-- stationary point of function f
let stationaryPoint = lam f. root (der f) in

let minf2 = stationaryPoint f2 in
let minf3 = stationaryPoint f3 in

utest isCorrect (num 0.) minf2 with true in
utest isCorrect (num 0.) minf3 with true in

-- test function with conditional
let f4 = lam x. if ltn x (num 0.) then num 0.0 else x in

utest der f4 (num (negf 1.)) with num 0. in
utest der f4 (num 1.) with num 1. in

()
