-- Defines the CUDA code generation for a foldl expression.

include "cuda/compile.mc"

lang CudaFoldlIntrinsic = CudaCompile
  sem generateCudaIntrinsicFunction (ccEnv : CompileCEnv) =
  | CESeqFoldl t ->
    let fId =
      match t.f with CEVar {id = id} then id
      else error "Cannot compile foldl function argument" in
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
    let foldStepStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = accId},
      rhs = CEApp {
        fun = fId,
        args = [
          CEVar {id = accId},
          CEBinOp {
            op = COSubScript (),
            lhs = CEMember {lhs = CEVar {id = sParamId}, id = _seqKey},
            rhs = CEVar {id = indexId}}]}}} in
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
    let stmts = [accDefStmt, indexDefStmt, whileStmt, retStmt] in
    let intrinsicId = nameSym "foldl" in
    let top = CuTTop {
      attrs = [CuAHost (), CuADevice ()],
      top = CTFun {
        ret = accType, id = intrinsicId,
        params = [(accType, accParamId), (sType, sParamId)],
        body = stmts}} in
    (intrinsicId, top)

  sem generateCudaIntrinsicCall (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | CESeqFoldl t ->
    match generateCudaIntrinsicFunction ccEnv (CESeqFoldl t) with (id, top) in
    let foldlCall = CEApp {fun = id, args = [t.acc, t.s]} in
    let acc = cons top acc in
    let stmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = outExpr,
      rhs = foldlCall}} in
    (acc, stmt)
end
