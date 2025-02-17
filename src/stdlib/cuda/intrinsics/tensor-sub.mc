-- Defines the CUDA code generation for a tensorSubExn expression.

include "cuda/intrinsics/intrinsic.mc"

lang CudaTensorSubIntrinsic = CudaIntrinsic
  sem generateCudaIntrinsicFunction (ccEnv : CompileCEnv) =
  | CETensorSubExn t ->
    let tId = nameSym "t" in
    let ofsId = nameSym "ofs" in
    let lenId = nameSym "len" in
    let tensor = CEVar {id = tId} in

    let intType = getCIntType ccEnv in
    let cartIdxSeq = nameSym "cartesian_idx_seq" in
    let cartIdx = nameSym "cartesian_idx" in
    let seqIntTypeName = _lookupTypeName ccEnv.typeEnv (tyseq_ tyint_) in
    let seqIntType = CTyVar {id = seqIntTypeName} in
    let initCartesianSeqStmts = [
      CSDef {
        ty = CTyArray {ty = intType, size = Some (CEInt {i = 1})},
        id = Some cartIdxSeq, init = None ()},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = cartIdxSeq},
          rhs = CEInt {i = 0}},
        rhs = CEVar {id = ofsId}}},
      CSDef {ty = seqIntType, id = Some cartIdx, init = None ()},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = CEVar {id = cartIdx}, id = _seqKey},
        rhs = CEVar {id = cartIdxSeq}}},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = CEVar {id = cartIdx}, id = _seqLenKey},
        rhs = CEInt {i = 1}}}] in
    let stmts = concat initCartesianSeqStmts [
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = tensor, id = _tensorDataKey},
        rhs = CEBinOp {
          op = COAdd (),
          lhs = CEMember {lhs = tensor, id = _tensorDataKey},
          rhs = tensorComputeLinearIndex tensor (CEVar {id = cartIdx})}}},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEBinOp {
          op = COSubScript (),
          lhs = CEMember {lhs = tensor, id = _tensorDimsKey},
          rhs = CEInt {i = 0}},
        rhs = CEVar {id = lenId}}},
      CSRet {val = Some tensor}] in

    let intrinsicId = nameSym "tensor_sub" in
    let top = CuTTop {
      attrs = [CuAHost (), CuADevice ()],
      top = CTFun {
        ret = t.ty, id = intrinsicId,
        params = [(t.ty, tId), (intType, ofsId), (intType, lenId)],
        body = stmts}} in
    (intrinsicId, top)

  sem generateCudaIntrinsicCall (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | CETensorSubExn t ->
    match generateCudaIntrinsicFunction ccEnv (CETensorSubExn t) with (id, top) in
    let tensorSubCall = CEApp {fun = id, args = [t.t, t.ofs, t.len]} in
    let acc = cons top acc in
    let stmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = outExpr,
      rhs = tensorSubCall}} in
    (acc, stmt)
end
