-- Defines the CUDA code generation for a foldl expression.

include "cuda/intrinsics/intrinsic.mc"

lang CudaFoldlIntrinsic = CudaIntrinsic
  sem generateCudaIntrinsicFunction (ccEnv : CompileCEnv) =
  | CESeqFoldl t ->
    match _getFunctionIdAndArgs t.f with (funId, args) in
    let accParamId = nameSym "acc_init" in
    let sParamId = nameSym "s" in
    let accId = nameSym "acc" in
    let accType = t.ty in
    let sType = t.sTy in
    let accDefStmt = CSDef {
      ty = accType,
      id = Some accId,
      init = Some (CIExpr {expr = CEVar {id = accParamId}})} in
    let indexId = nameSym "i" in
    let indexDefStmt = CSDef {
      ty = getCIntType ccEnv,
      id = Some indexId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let foldArgs = [
      CEVar {id = accId},
      CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = CEVar {id = sParamId}, id = _seqKey},
        rhs = CEVar {id = indexId}}] in
    let foldStepStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = accId},
      rhs = CEApp {
        fun = funId,
        args = concat args foldArgs}}} in
    let indexIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = indexId},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = indexId},
        rhs = CEInt {i = 1}}}} in
    let whileCondExpr = CEBinOp {
      op = COLt (),
      lhs = CEVar {id = indexId},
      rhs = CEMember {lhs = CEVar {id = sParamId}, id = _seqLenKey}} in
    let whileBodyStmts = [foldStepStmt, indexIncrementStmt] in
    let whileStmt = CSWhile {cond = whileCondExpr, body = whileBodyStmts} in
    let retStmt = CSRet {val = Some (CEVar {id = accId})} in
    let argIds = _getFunctionArgNames t.f in
    let params =
      concat
        [(accType, accParamId), (sType, sParamId)] (zip t.argTypes argIds) in
    let stmts = [accDefStmt, indexDefStmt, whileStmt, retStmt] in
    let intrinsicId = nameSym "foldl" in
    let top = CuTTop {
      attrs = [CuAHost (), CuADevice ()],
      top = CTFun {
        ret = accType, id = intrinsicId,
        params = params,
        body = stmts}} in
    (intrinsicId, top)

  sem generateCudaIntrinsicCall (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | CESeqFoldl t ->
    match generateCudaIntrinsicFunction ccEnv (CESeqFoldl t) with (id, top) in
    match _getFunctionIdAndArgs t.f with (_, args) in
    let foldlCall = CEApp {fun = id, args = concat [t.acc, t.s] args} in
    let acc = cons top acc in
    let stmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = outExpr,
      rhs = foldlCall}} in
    (acc, stmt)
end
