-- Defines the CUDA code generation for a (non-kernel) map expression.

include "cuda/ast.mc"

lang CudaMapIntrinsic = CudaAst
  sem generateCudaIntrinsicFunction =
  | CEMap t ->
    let fId =
      match t.f with CEVar {id = id} then id
      else error "Cannot compile map function argument" in
    let outParamId = nameSym "out" in
    let sParamId = nameSym "s" in
    let outTypeId = nameSym "T" in
    let sTypeId = nameSym "T" in
    let indexId = nameSym "i" in
    let indexDefStmt = CSDef {
      ty = CTyInt64 (),
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
    let outType = CTyVar {id = outTypeId} in
    let sType = CTyVar {id = sTypeId} in
    let top = CuTTop {
      templates = [outTypeId, sTypeId],
      attrs = [CuAHost (), CuADevice ()],
      top = CTFun {
        ret = CTyVoid (), id = intrinsicId,
        params = [(outType, outParamId), (sType, sParamId)],
        body = stmts}} in
    (intrinsicId, top)

  sem generateCudaIntrinsicCall (acc : [CuTop]) (outExpr : CExpr) =
  | CEMap t ->
    match generateCudaIntrinsicFunction (CEMap t) with (id, top) in
    let acc = cons top acc in
    let setLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = outExpr, id = _seqLenKey},
      rhs = CEMember {lhs = t.s, id = _seqLenKey}}} in
    -- TODO(larshum, 2022-02-14): Deallocation of memory
    -- TODO(larshum, 2022-02-14): Eliminate use of 'decltype' and
    -- 'std::remove_pointer' by storing the type in every CExpr node.
    let seqType = CTyDecltype {e = CEMember {lhs = outExpr, id = _seqKey}} in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEMember {lhs = outExpr, id = _seqLenKey},
      rhs = CESizeOfType {ty = CTyRmPtr {ty = seqType}}} in
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
