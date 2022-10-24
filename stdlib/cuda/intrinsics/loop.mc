-- Defines the code generation for a sequential loop.

include "cuda/intrinsics/intrinsic.mc"

lang CudaLoopIntrinsic = CudaIntrinsic
  sem generateCudaIntrinsicCallNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | CESeqLoop t ->
    match _getFunctionIdAndArgs t.f with (funId, args) in
    let i = nameSym "i" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some i,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let loopFunAppStmt = CSExpr {expr = CEApp {
      fun = funId, args = snoc args (CEVar {id = i})}} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = i},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = i},
        rhs = CEInt {i = 1}}}} in
    let loopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = i},
        rhs = t.n},
      body = [loopFunAppStmt, iterIncrementStmt]} in
    (acc, CSComp {stmts = [iterInitStmt, loopStmt]})
end
