-- Defines the CUDA code generation for a parallel loop kernel.

include "cuda/pmexpr-ast.mc"
include "cuda/intrinsics/intrinsic.mc"

lang CudaLoopKernelIntrinsic = CudaIntrinsic + CudaPMExprAst
  sem generateCudaKernelFunctionNoRet =
  | CELoopKernel t ->
    let seqIdx = lam seqId. lam idxId.
      CEBinOp {
        op = COSubScript (),
        lhs = CEArrow {lhs = CEVar {id = seqId}, id = _seqKey},
        rhs = CEVar {id = idxId}} in
    match _getFunctionIdAndArgs t.f with (funId, args) in
    let kernelId = nameSym "loopKernel" in
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
    let loopRunStmt = CSExpr {expr = CEApp {
      fun = funId, args = snoc args (CEVar {id = indexId})}} in
    let indexIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = indexId},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = indexId},
        rhs = CEVar {id = strideId}}}} in
    let n = nameSym "n" in
    let whileCondExpr = CEBinOp {
      op = COLt (),
      lhs = CEVar {id = indexId},
      rhs = CEVar {id = n}} in
    let whileStmt = CSWhile {
      cond = whileCondExpr,
      body = [loopRunStmt, indexIncrementStmt]} in
    let stmts = [indexStmt, strideStmt, whileStmt] in
    let argIds = _getFunctionArgNames t.f in
    let params = cons (CTyInt64 (), n) (zip t.argTypes argIds) in
    let top = CuTTop {
      attrs = [CuAGlobal ()],
      top = CTFun {
        ret = CTyVoid (), id = kernelId, params = params, body = stmts}} in
    (kernelId, top)

  sem generateCudaKernelCallNoRet (ccEnv : CompileCEnv) =
  | CELoopKernel t ->
    match generateCudaKernelFunctionNoRet (CELoopKernel t) with (kernelId, kernelTop) in

    let iterId = nameSym "niterations" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId, init = Some (CIExpr {expr = t.n})} in

    -- Compute launch parameters and start kernel
    -- NOTE(larshum, 2022-02-08): For now, the number of threads per block is
    -- hard-coded. We may want more fine-grained control in the future.
    let tpbId = nameSym "tpb" in
    let tpbStmt = CSDef {
      ty = getCIntType ccEnv, id = Some tpbId,
      init = Some (CIExpr {expr = CEInt {i = 256}})} in
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
          lhs = CEVar {id = iterId},
          rhs = operationsPerBlockExpr},
        rhs = CEInt {i = 1}},
      rhs = operationsPerBlockExpr} in
    let nblocksStmt = CSDef {
      ty = getCIntType ccEnv, id = Some nblocksId,
      init = Some (CIExpr {expr = nblocksExpr})} in
    match _getFunctionIdAndArgs t.f with (_, args) in
    let kernelLaunchStmt = CSExpr {expr = CEKernelApp {
      fun = kernelId,
      gridSize = CEVar {id = nblocksId},
      blockSize = CEVar {id = tpbId},
      args = cons t.n args}} in
    let errorCheckStmt = CSExpr {expr = CEApp {
        fun = _CUDA_UTILS_CHECK_CUDA_ERROR,
        args = []
      }} in
    let deviceSynchronizeStmt = CSExpr {expr = CEApp {
      fun = _cudaDeviceSynchronize, args = []}} in

    let stmts =
      [ iterInitStmt, tpbStmt, nblocksStmt, kernelLaunchStmt, errorCheckStmt
      , deviceSynchronizeStmt, errorCheckStmt ] in
    (kernelTop, CSComp {stmts = stmts})
end
