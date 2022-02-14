-- Defines the CUDA code generation for a foldl expression.

include "cuda/ast.mc"

lang CudaFoldlIntrinsic = CudaAst
  sem generateCudaIntrinsicFunction =
  | CEFoldl t ->
    let fId =
      match t.f with CEVar {id = id} then id
      else error "Cannot compile foldl function argument" in
    let accParamId = nameSym "acc_init" in
    let sParamId = nameSym "s" in
    let accId = nameSym "acc" in
    -- TODO: How can we figure out the type of acc and s?
    let accTypeId = nameSym "T" in
    let sTypeId = nameSym "T" in
    let accType = CTyVar {id = accTypeId} in
    let accDefStmt = CSDef {
      ty = accType,
      id = Some accId,
      init = Some (CIExpr {expr = CEVar {id = accParamId}})} in
    let indexId = nameSym "i" in
    let indexDefStmt = CSDef {
      ty = CTyInt64 (),
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
    let sType = CTyVar {id = sTypeId} in
    let top = CuTTop {
      templates = [accTypeId, sTypeId],
      attrs = [CuAHost (), CuADevice ()],
      top = CTFun {
        ret = accType, id = intrinsicId,
        params = [(accType, accParamId), (sType, sParamId)],
        body = stmts}} in
    (intrinsicId, top)

  sem generateCudaIntrinsicCall (acc : [CuTop]) (outExpr : CExpr) =
  | CEFoldl t ->
    match generateCudaIntrinsicFunction (CEFoldl t) with (id, top) in
    let foldlCall = CEApp {fun = id, args = [t.acc, t.s]} in
    let acc = cons top acc in
    (acc, _reconstructStmt outExpr foldlCall)

  sem _reconstructStmt (outExpr : CExpr) =
  | intrinsicCall ->
    CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = intrinsicCall}}
end
