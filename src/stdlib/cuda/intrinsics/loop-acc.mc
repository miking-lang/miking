-- Defines the code generation for a left-folding loop. Unlike the default
-- looping construct, this one also produces an accumulated value that is
-- returned as output.

include "cuda/intrinsics/intrinsic.mc"

lang CudaLoopAccIntrinsic = CudaIntrinsic
  sem generateCudaIntrinsicCall (ccEnv : CompileCEnv) (acc : [CuTop])
                                (outExpr : CExpr) =
  | CESeqLoopAcc t ->
    match _getFunctionIdAndArgs t.f with (funId, args) in
    let i = nameSym "i" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some i,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let initOutStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = outExpr,
      rhs = t.ne}} in
    let accIdent = nameSym "acc" in
    let accInitStmt = CSDef {
      ty = t.neTy, id = Some accIdent,
      init = Some (CIExpr {expr = t.ne})} in
    let loopFunAppStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = accIdent},
      rhs = CEApp {
        fun = funId,
        args = concat args [CEVar {id = accIdent}, CEVar {id = i}]}}} in
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
    let outAssignStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = outExpr,
      rhs = CEVar {id = accIdent}}} in
    (acc, CSComp {stmts = [iterInitStmt, accInitStmt, loopStmt, outAssignStmt]})
end
