-- Defines the CUDA code generation for a map kernel.

include "cuda/pmexpr-ast.mc"
include "cuda/intrinsics/intrinsic.mc"

lang CudaMapKernelIntrinsic = CudaIntrinsic + CudaPMExprAst
  sem generateCudaKernelFunction =
  | CEMapKernel t ->
    let seqIdx = lam seqId. lam idxId.
      CEBinOp {
        op = COSubScript (),
        lhs = CEArrow {lhs = CEVar {id = seqId}, id = _seqKey},
        rhs = CEVar {id = idxId}} in
    match _getFunctionIdAndArgs t.f with (funId, _) in
    let kernelId = nameSym "mapKernel" in
    let outParamId = nameSym "out" in
    let sParamId = nameSym "s" in
    let indexId = nameSym "idx" in
    let indexStmt = CSDef {
      ty = CTyInt64 (), id = Some indexId,
      init = Some (CIExpr {expr = CEBinOp {
        op = COAdd (),
        lhs = CEBinOp {
          op = COMul (),
          lhs = CEBlockDim {dim = CuDX ()},
          rhs = CEBlockIdx {dim = CuDX ()}},
        rhs = CEThreadIdx {dim = CuDX ()}}})} in
    let strideId = nameSym "stride" in
    let strideStmt = CSDef {
      ty = CTyInt64 (), id = Some strideId,
      init = Some (CIExpr {expr = CEBinOp {
        op = COMul (),
        lhs = CEGridDim {dim = CuDX ()},
        rhs = CEBlockDim {dim = CuDX ()}}})} in
    let mapAssignStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = seqIdx outParamId indexId,
      rhs = CEApp {
        fun = funId,
        args = [seqIdx sParamId indexId]}}} in
    let indexIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = indexId},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = indexId},
        rhs = CEVar {id = strideId}}}} in
    let whileCondExpr = CEBinOp {
      op = COLt (),
      lhs = CEVar {id = indexId},
      rhs = CEArrow {lhs = CEVar {id = sParamId}, id = _seqLenKey}} in
    let whileStmt = CSWhile {
      cond = whileCondExpr,
      body = [mapAssignStmt, indexIncrementStmt]} in
    let stmts = [indexStmt, strideStmt, whileStmt] in
    let outTy = CTyPtr {ty = t.ty} in
    let sTy = CTyPtr {ty = t.sTy} in
    let top = CuTTop {
      attrs = [CuAGlobal ()],
      top = CTFun {
        ret = CTyVoid (), id = kernelId,
        params = [(outTy, outParamId), (sTy, sParamId)], body = stmts}} in
    (kernelId, top)

  sem generateCudaKernelCall (ccEnv : CompileCEnv) (outExpr : CExpr) =
  | CEMapKernel t ->
    match generateCudaKernelFunction (CEMapKernel t) with (kernelId, kernelTop) in

    -- Determine the length of the input sequence. As it is stored on the GPU
    -- at this point, we need to copy the struct (not all data) back to the CPU
    -- to get access to the length field.
    let tempId = nameSym "t" in
    let tempSeqDeclStmt = CSDef {
      ty = t.sTy, id = Some tempId, init = None ()} in
    let cudaMemcpyStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}},
        t.s,
        CESizeOfType {ty = t.sTy},
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let lenId = nameSym "n" in
    let lenStmt = CSDef {
      ty = getCIntType ccEnv, id = Some lenId,
      init = Some (CIExpr {expr =
        CEMember {lhs = CEVar {id = tempId}, id = _seqLenKey}})} in

    -- Pre-allocate memory for the output
    let outElemType = _getStructDataElemType ccEnv t.ty in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = lenId},
      rhs = CESizeOfType {ty = outElemType}} in
    let allocTempDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMalloc,
      args = [
        CEUnOp {op = COAddrOf (),
                arg = CEMember {lhs = CEVar {id = tempId}, id = _seqKey}},
        sizeExpr]}} in
    let allocSeqStmt = CSExpr {expr = CEApp {
      fun = _cudaMalloc,
      args = [
        CEUnOp {op = COAddrOf (), arg = outExpr},
        CESizeOfType {ty = t.ty}]}} in
    let memcpySeqStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        outExpr,
        CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}},
        CESizeOfType {ty = t.ty},
        CEVar {id = _cudaMemcpyHostToDevice}]}} in

    -- Compute launch parameters and start kernel
    -- NOTE(larshum, 2022-02-08): For now, the number of threads per block is
    -- hard-coded. We may want more fine-grained control in the future.
    let tpbId = nameSym "tpb" in
    let tpbStmt = CSDef {
      ty = getCIntType ccEnv, id = Some tpbId,
      init = Some (CIExpr {expr = CEInt {i = 512}})} in
    -- Each block consists of 'tpb' threads, and each such thread should
    -- process a specified number of elements.
    let operationsPerBlockExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = tpbId},
      rhs = CEInt {i = t.opsPerThread}} in
    let nblocksId = nameSym "nblocks" in
    let nblocksExpr = CEBinOp {
      op = CODiv (),
      lhs = CEBinOp {
        op = COSub (),
        lhs = CEBinOp {
          op = COAdd (),
          lhs = CEVar {id = lenId},
          rhs = operationsPerBlockExpr},
        rhs = CEInt {i = 1}},
      rhs = operationsPerBlockExpr} in
    let nblocksStmt = CSDef {
      ty = getCIntType ccEnv, id = Some nblocksId,
      init = Some (CIExpr {expr = nblocksExpr})} in
    let kernelLaunchStmt = CSExpr {expr = CEKernelApp {
      fun = kernelId,
      gridSize = CEVar {id = nblocksId},
      blockSize = CEVar {id = tpbId},
      args = [outExpr, t.s]}} in

    let compStmt = CSComp {stmts = [
      tempSeqDeclStmt, cudaMemcpyStmt, lenStmt, allocTempDataStmt,
      allocSeqStmt, memcpySeqStmt, tpbStmt, nblocksStmt,
      kernelLaunchStmt]} in
    (kernelTop, compStmt)
end
