-- Translates C top-level definitions to the CUDA specific representation of
-- tops. This includes the addition of CUDA attributes, and providing distinct
-- names for the CUDA wrapper functions, which handle interaction with CUDA
-- kernels. It also involves updating GPU variables to be pointers, rather than
-- being allocated on the (CPU) stack.

include "name.mc"
include "set.mc"
include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/compile.mc"
include "cuda/memory.mc"

lang CudaMapKernelTranslate = CudaAst + CudaPMExprAst
  sem generateMapKernel =
  | CEMapKernel t ->
    let seqIdx = lam seqId. lam idxId.
      CEBinOp {
        op = COSubScript (),
        lhs = CEArrow {lhs = CEVar {id = seqId}, id = _seqKey},
        rhs = CEVar {id = idxId}} in
    let fId =
      match t.f with CEVar {id = id} then id
      else error "Unsupported function expression" in
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
        fun = fId,
        args = [seqIdx sParamId indexId]}}} in
    let indexIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = indexId},
      rhs = CEVar {id = strideId}}} in
    let whileCondExpr = CEBinOp {
      op = COLt (),
      lhs = CEVar {id = indexId},
      rhs = CEArrow {lhs = CEVar {id = sParamId}, id = _seqLenKey}} in
    let whileStmt = CSWhile {
      cond = whileCondExpr,
      body = [mapAssignStmt, indexIncrementStmt]} in
    let stmts = [indexStmt, strideStmt, whileStmt] in
    let outTy = CTyPtr {ty = t.retTy} in
    let sTy = CTyPtr {ty = t.sTy} in
    let top = CuTTop {
      attrs = [CuAGlobal ()],
      top = CTFun {
        ret = CTyVoid (), id = kernelId,
        params = [(outTy, outParamId), (sTy, sParamId)], body = stmts}} in
    (kernelId, top)
end

lang CudaKernelTranslate =
  CudaAst + CudaMemoryManagement + CudaMapKernelTranslate + MExprCCompile

  sem translateCudaTops (cudaMemEnv : Map Name AllocEnv)
                        (ccEnv : CompileCEnv) =
  | tops ->
    let emptyEnv = mapEmpty nameCmp in
    let tops = map (translateTopToCudaFormat cudaMemEnv) tops in
    generateKernels cudaMemEnv ccEnv tops

  sem generateKernels (cudaMemEnv : Map Name AllocEnv)
                      (ccEnv : CompileCEnv) =
  | tops ->
    match mapAccumL (generateKernelsTop cudaMemEnv ccEnv)
                    (mapEmpty nameCmp) tops
    with (wrapperMap, tops) in
    (wrapperMap, join tops)

  sem generateKernelsTop (cudaMemEnv : Map Name AllocEnv)
                         (ccEnv : CompileCEnv)
                         (wrapperMap : Map Name Name) =
  | CuTTop (cuTop & {top = CTFun t}) ->
    match mapLookup t.id cudaMemEnv with Some _ then
      match mapAccumL (generateKernelStmt ccEnv) [] t.body
      with (kernelTops, body) in
      let cudaWrapperId = nameSym "cuda_wrap" in
      let wrapperMap = mapInsert t.id cudaWrapperId wrapperMap in
      let newTop = CTFun {{t with id = cudaWrapperId}
                             with body = body} in
      let cudaTop = CuTTop {cuTop with top = newTop} in
      let tops = snoc kernelTops cudaTop in
      (wrapperMap, tops)
    else (wrapperMap, [CuTTop cuTop])
  | t -> (wrapperMap, [t])

  -- NOTE(larshum, 2022-02-08): We assume that the expression for the function
  -- f is a variable containing an identifier. This will not work for closures
  -- or for functions that take additional variables, including those that
  -- capture variables (due to lambda lifting).
  sem generateKernelStmt (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr,
                            rhs = CEMapKernel t}} ->
    match generateMapKernel (CEMapKernel t) with (kernelId, kernelTop) in
    let acc = cons kernelTop acc in

    -- Determine the length of the input sequence. As it is stored on the GPU
    -- at this point, we need to copy the struct (not all data) back to the CPU
    -- to get access to the length field.
    let tempId = nameSym "t" in
    let tempSeqDeclStmt = CSDef {ty = t.sTy, id = Some tempId, init = None ()} in
    let cudaMemcpyStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}}, t.s,
        CESizeOfType {ty = t.sTy},
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let lenId = nameSym "n" in
    let lenStmt = CSDef {
      ty = CTyInt64 (), id = Some lenId,
      init = Some (CIExpr {expr =
        CEMember {lhs = CEVar {id = tempId}, id = _seqLenKey}})} in

    -- Pre-allocate memory for the output
    let outElemType =
      match t.retTy with CTyVar {id = seqId} then
        -- TODO(larshum, 2022-02-09): Only works for 1d sequences.
        -- OPT(larshum, 2022-02-09): We need the type environment as an
        -- associative sequence, so that we can compile the element type to a C
        -- type. However, that also requires a linear-time lookup.
        match assocSeqLookup {eq=nameEq} seqId ccEnv.typeEnv
        with Some (TySeq {ty = elemTy}) then
          compileType ccEnv elemTy
        else error "Expected output of map kernel to be a sequence"
      else error "Unexpected type of map kernel output" in
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
        CESizeOfType {ty = t.retTy}]}} in
    let memcpySeqStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        outExpr, CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}},
        CESizeOfType {ty = t.retTy},
        CEVar {id = _cudaMemcpyHostToDevice}]}} in

    -- Compute launch parameters and start kernel
    -- NOTE(larshum, 2022-02-08): For now, the number of threads per block is
    -- hard-coded. We may want more fine-grained control in the future.
    let tpbId = nameSym "tpb" in
    let tpbStmt = CSDef {
      ty = CTyInt64 (), id = Some tpbId,
      init = Some (CIExpr {expr = CEInt {i = 512}})} in
    let nblocksId = nameSym "nblocks" in
    let nblocksExpr = CEBinOp {
      op = CODiv (),
      lhs = CEBinOp {
        op = COSub (),
        lhs = CEBinOp {
          op = COAdd (),
          lhs = CEVar {id = lenId},
          rhs = CEVar {id = tpbId}},
        rhs = CEInt {i = 1}},
      rhs = CEVar {id = tpbId}} in
    let nblocksStmt = CSDef {
      ty = CTyInt64 (), id = Some nblocksId,
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
    (acc, compStmt)
  | stmt -> (acc, stmt)

  sem translateTopToCudaFormat (cudaMemEnv : Map Name AllocEnv) =
  | CTTyDef t -> CuTTop {attrs = [], top = CTTyDef t}
  | CTDef t -> CuTTop {attrs = [CuAHost (), CuADevice ()], top = CTDef t}
  | CTFun t ->
    match mapLookup t.id cudaMemEnv with Some allocEnv then
      let body = map (usePointerToGpuVariablesStmt allocEnv) t.body in
      let cTop = CTFun {t with body = body} in
      CuTTop {attrs = [], top = cTop}
    else
      let attrs = [CuAHost (), CuADevice ()] in
      CuTTop {attrs = attrs, top = CTFun t}

  sem usePointerToGpuVariablesStmt (env : AllocEnv) =
  | CSDef (t & {id = Some id}) ->
    match allocEnvLookup id env with Some (Gpu _) then
      CSDef {t with ty = CTyPtr {ty = t.ty}}
    else CSDef t
  | stmt -> stmt
end
