-- Defines the CUDA code generation for a (non-kernel) map expression.

include "cuda/intrinsics/intrinsic.mc"

lang CudaMapIntrinsic = CudaIntrinsic
  sem generateCudaIntrinsicFunction (ccEnv : CompileCEnv) =
  | CESeqMap t ->
    let fId =
      match t.f with CEVar {id = id} then id
      else error "Cannot compile map function argument" in
    let outParamId = nameSym "out" in
    let sParamId = nameSym "s" in
		let outType = t.ty in
		let sType = t.sTy in
    let indexId = nameSym "i" in
    let indexDefStmt = CSDef {
      ty = getCIntType ccEnv,
      id = Some indexId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let mapStepStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = CEVar {id = outParamId}, id = _seqKey},
        rhs = CEVar {id = indexId}},
      rhs = CEApp {
        fun = fId,
        args = [CEBinOp {
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
    let whileBodyStmts = [mapStepStmt, indexIncrementStmt] in
    let whileStmt = CSWhile {cond = whileCondExpr, body = whileBodyStmts} in
    let stmts = [indexDefStmt, whileStmt] in
    let intrinsicId = nameSym "map" in
    let top = CuTTop {
      attrs = [CuAHost (), CuADevice ()],
      top = CTFun {
        ret = CTyVoid (), id = intrinsicId,
        params = [(outType, outParamId), (sType, sParamId)],
        body = stmts}} in
    (intrinsicId, top)

  sem generateCudaIntrinsicCall (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | CESeqMap t ->
    match generateCudaIntrinsicFunction ccEnv (CESeqMap t) with (id, top) in
    let acc = cons top acc in
    let setLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = outExpr, id = _seqLenKey},
      rhs = CEMember {lhs = t.s, id = _seqLenKey}}} in
    -- TODO(larshum, 2022-02-14): Deallocation of memory
    let elemType = _getStructDataElemType ccEnv t.ty in
    let seqType = CTyPtr {ty = elemType} in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEMember {lhs = outExpr, id = _seqLenKey},
      rhs = CESizeOfType {ty = elemType}} in
    let allocStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = outExpr, id = _seqKey},
      rhs = CECast {
        ty = seqType,
        rhs = CEApp {
          fun = _malloc,
          args = [sizeExpr]}}}} in
    let mapCallStmt = CSExpr {expr = CEApp {fun = id, args = [outExpr, t.s]}} in
    let stmts = [setLenStmt, allocStmt, mapCallStmt] in
    (acc, CSComp {stmts = stmts})
end
