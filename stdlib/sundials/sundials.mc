include "string.mc"
include "tensor.mc"

type NvectorSerial
type SundialsMatrixDense
type SundialsRealArray
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
  t : Float,
  y : Tensor[Float],
  yp : Tensor[Float],
  res : Tensor[Float],
  c : Float,
  tmp : (Tensor[Float], Tensor[Float], Tensor[Float])
}

type IdaJacFn = IdaJacArgs -> SundialsMatrixDense -> ()
type IdaResFn = Float -> Tensor[Float] -> Tensor[Float] -> Tensor[Float] -> ()
type IdaRootFn = IdaResFn

external externalSundialsRealArrayCreate : Int -> SundialsRealArray
let sundialsRealArrayCreate = lam n. externalSundialsRealArrayCreate n

external externalNvectorSerialWrap : Tensor[Float] -> NvectorSerial
let nvectorSerialWrap = lam t. externalNvectorSerialWrap t

external externalNvectorSerialUnwrap : NvectorSerial -> Tensor[Float]
let nvectorSerialUnwrap = lam t. externalNvectorSerialUnwrap t

external externalSundialsMatrixDense : Int -> SundialsMatrixDense
let sundialsMatrixDense =
  lam n. externalSundialsMatrixDense n

external externalSundialsMatrixDenseUnwrap !
  : SundialsMatrixDense -> Tensor[Float]
let sundialsMatrixDenseUnwrap = lam m. externalSundialsMatrixDenseUnwrap m

external externalIdaDlsDense !
  : NvectorSerial -> SundialsMatrixDense -> IdaDlsDense
let idaDlsDense = lam v. lam m. externalIdaDlsDense v m

external externalIdaDlsSolver ! : IdaDlsDense -> IdaDlsSolverSession
let idaDlsSolver = lam solver. externalIdaDlsSolver solver

external externalIdaDlsSolverJacf !
  : IdaJacFn -> IdaDlsDense -> IdaDlsSolverSession
let idaDlsSolverJacf =
  lam jacf. lam solver. externalIdaDlsSolverJacf jacf solver

external idaVarIdAlgebraic : Float
external idaVarIdDifferential : Float

external externalIdaSSTolerances : Float -> Float -> IdaTolerance
let idaSSTolerances = lam rtol. lam atol. externalIdaSSTolerances rtol atol

external externalIdaRetcode : IdaSolverResultInternal -> Int
let idaRetcode = lam r. externalIdaRetcode r

let idaSolverResult : IdaSolverResultInternal -> IdaSolverResult =
  lam r.
    let rc = idaRetcode r in
    if eqi rc 0 then IdaSuccess {} else
    if eqi rc 1 then IdaStopTimeReached {} else
    if eqi rc 2 then IdaRootsFound {} else
    never

external externalIdaInit !
  : IdaDlsSolverSession ->
    IdaTolerance ->
    IdaResFn ->
    NvectorSerial ->
    (Int, IdaRootFn) ->
    Float ->
    NvectorSerial ->
    NvectorSerial ->
    IdaSession

let idaInit =
  lam lsolver.
  lam tol.
  lam resf.
  lam varid.
  lam roots.
  lam t.
  lam v.
  lam vp.
  externalIdaInit lsolver tol resf varid roots t v vp

external externalIdaCalcICYaYd !
  : IdaSession -> Float -> NvectorSerial -> NvectorSerial -> ()
let idaCalcICYaYd = lam s. lam t. lam y. lam yp. externalIdaCalcICYaYd s t y yp

external externalIdaSolveNormal
 : IdaSession ->
   Float ->
   NvectorSerial ->
   NvectorSerial ->
   (Float, IdaSolverResultInternal)
let idaSolveNormal =
  lam s. lam tend. lam v. lam vp. externalIdaSolveNormal s tend v vp

external externalIdaReinit
  : IdaSession ->
    (Int, IdaRootFn) ->
    Float ->
    NvectorSerial ->
    NvectorSerial ->
    ()
let idaReinit =
  lam s.
  lam roots.
  lam t.
  lam v.
  lam vp.
  externalIdaReinit s roots t v vp

mexpr

utest
  let tget = tensorGetExn in
  let tset = tensorSetExn in
  let tcreate = tensorCreateCArrayFloat in

  let y = tcreate [2] (lam. 0.) in
  let yp = tcreate [2] (lam. 0.) in

  tset y [0] 1.;
  tset yp [1] (negf 1.);

  let v = nvectorSerialWrap y in
  let vp = nvectorSerialWrap yp in

  let m = sundialsMatrixDense 2 in

  let lsolver = idaDlsDense v m in

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

  -- let lsolver = idaDlsSolverJacf jacf lsolver in
  let lsolver = idaDlsSolver lsolver in
  let tol = idaSSTolerances 1.e-4 1.e-6 in

  let resf = lam. lam y. lam yp. lam r.
    let x = tget y [0] in
    let vx = tget y [1] in
    let dx = tget yp [0] in
    let dvx = tget yp [1] in
    tset r [0] (subf dx vx);
    tset r [1] (addf dvx (addf vx x));
    ()
  in

  let varid = nvectorSerialWrap (tcreate [2] (lam. idaVarIdDifferential)) in
  let rootf = lam. lam. lam. lam. () in
  let t0 = 0. in

  let s = idaInit lsolver tol resf varid (0, rootf) t0 v vp in
  idaCalcICYaYd s 1.e-4 v vp;
  let r = idaSolveNormal s 2. v vp in

  (match r with (tend, r) then
    utest idaSolverResult r with IdaSuccess {} in
    utest tend with 2. using eqf in
    ()
  else never);

  let y = nvectorSerialUnwrap v in
  let yp = nvectorSerialUnwrap vp in

  tset y [0] 1.;
  tset y [1] 0.;
  tset yp [0] 0.;
  tset yp [1] (negf 0.);
  idaReinit s (0, rootf) t0 v vp;
  idaCalcICYaYd s 1.e-4 v vp;
  let r = idaSolveNormal s 2. v vp in

  (match r with (tend, r) then
    utest idaSolverResult r with IdaSuccess {} in
    utest tend with 2. using eqf in
    ()
  else never)
with () in
()
