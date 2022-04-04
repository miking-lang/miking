-- CUDA management of tensor memory.

include "cuda/ast.mc"
include "cuda/compile.mc"
include "cuda/wrapper.mc"

lang CudaTensorMemoryBase = CudaCompile
  type CudaTensorEnv = {
    ccEnv : CompileCEnv,
    useTensorUnifiedMemory : Bool
  }
end

-- Produces additional code to insert at the beginning of each wrapper
-- function, to initialize the global memory data used to keep track of
-- tensors.
lang CudaTensorGlobalWrapper = CudaTensorMemoryBase
  sem tensorInitWrapperCode : CudaTensorEnv -> CType -> CExpr -> [CStmt]
  sem tensorInitWrapperCode env elemTy =
  | tensorExpr ->
    let env : CudaTensorEnv = env in
    let indexExpr = CEMember {lhs = tensorExpr, id = _tensorIdKey} in
    let tensorDataAccess = lam dataId.
      CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = dataId},
        rhs = indexExpr} in
    let cpuDataInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = tensorDataAccess _tensorCpuData,
      rhs = CEMember {lhs = tensorExpr, id = _tensorDataKey}}} in
    let gpuInitExpr =
      if env.useTensorUnifiedMemory then
        CEMember {lhs = tensorExpr, id = _tensorDataKey}
      else CEVar {id = _getIdentExn "NULL"} in
    let gpuDataInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = tensorDataAccess _tensorGpuData,
      rhs = gpuInitExpr}} in
    let sizeExpr = tensorDataAccess _tensorSizeData in
    let sizeCountInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = sizeExpr,
      rhs = CESizeOfType {ty = elemTy}}} in
    let iterId = nameSym "i" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let sizeCountLoopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = iterId},
        rhs = CEMember {lhs = tensorExpr, id = _tensorRankKey}},
      body = [
        CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = sizeExpr,
          rhs = CEBinOp {
            op = COMul (),
            lhs = sizeExpr,
            rhs = CEBinOp {
              op = COSubScript (),
              lhs = CEMember {lhs = tensorExpr, id = _tensorDimsKey},
              rhs = CEVar {id = iterId}}}}},
        CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEVar {id = iterId},
          rhs = CEBinOp {
            op = COAdd (),
            lhs = CEVar {id = iterId},
            rhs = CEInt {i = 1}}}}]} in
    let stateInitExpr =
      if env.useTensorUnifiedMemory then CEVar {id = _tensorStateOk}
      else CEVar {id = _tensorStateGpuInvalid} in
    let stateInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = tensorDataAccess _tensorStateData,
      rhs = stateInitExpr}} in
    [ cpuDataInitStmt, gpuDataInitStmt, sizeCountInitStmt, iterInitStmt
    , sizeCountLoopStmt, stateInitStmt ]

  sem mapTensors : CudaTensorEnv -> (CudaTensorEnv -> CType -> CExpr -> [CStmt])
                -> (CType, Name) -> [CStmt]
  sem mapTensors env tensorCallFn =
  | (CTyPtr {ty = CTyVar {id = tyId}}, id)
  | (CTyVar {id = tyId}, id) ->
    recursive let work = lam ty : Type. lam expr : CExpr.
      let env : CudaTensorEnv = env in
      let ty = _unwrapType env.ccEnv.typeEnv ty in
      match ty with TyTensor {ty = elemTy} then
        let cElemTy = compileType env.ccEnv elemTy in
        tensorCallFn env cElemTy expr
      else match ty with TyRecord t then
        mapFoldWithKey
          (lam acc : [CStmt]. lam key : SID. lam fieldTy : Type.
            let fieldId = nameNoSym (sidToString key) in
            let fieldExpr = CEMember {lhs = expr, id = fieldId} in
            concat acc (work fieldTy fieldExpr))
          [] t.fields
      else match ty with TySeq t then
        -- TODO(larshum, 2022-03-30): Only generate a loop for sequences that
        -- could contain tensors.
        let iterId = nameSym "i" in
        let iter = CEVar {id = iterId} in
        let iterInitStmt = CSDef {
          ty = CTyInt64 (), id = Some iterId,
          init = Some (CIExpr {expr = CEInt {i = 0}})} in
        let innerExpr = CEBinOp {
          op = COSubScript (),
          lhs = CEMember {lhs = expr, id = _seqKey},
          rhs = iter} in
        let innerTensorStmts = work t.ty innerExpr in
        let iterIncrementStmt = CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = iter,
          rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
        let lenExpr = CEMember {lhs = expr, id = _seqLenKey} in
        let loopStmt = CSWhile {
          cond = CEBinOp {op = COLt (), lhs = iter, rhs = lenExpr},
          body = snoc innerTensorStmts iterIncrementStmt} in
        [iterInitStmt, loopStmt]
      else match ty with TyVariant t then
        -- TODO(larshum, 2022-03-30): Only generate code for variants that may
        -- contain a tensor at runtime.
        let counter = ref 0 in
        let constrId = CEArrow {lhs = expr, id = _constrKey} in
        mapFoldWithKey
          (lam acc : [CStmt]. lam constrIdent : Name. lam constrTy : Type.
            let constrExpr = CEArrow {lhs = expr, id = constrIdent} in
            let count = deref counter in
            modref counter (addi count 1);
            [ CSIf {
                cond = CEBinOp {
                  op = COEq (), lhs = constrId, rhs = CEInt {i = count}},
                thn = work constrTy constrExpr,
                els = acc} ])
          [] t.constrs
      else []
    in
    let idExpr = CEVar {id = id} in
    let lookupType = TyCon {ident = tyId, info = NoInfo ()} in
    work lookupType idExpr
  | _ -> []

  -- Adds code for initialization of tensor data within wrapper functions.
  sem addWrapperTensorCode : CudaTensorEnv -> CuTop -> CuTop
  sem addWrapperTensorCode env =
  | CuTTop (tt & {attrs = [], top = CTFun t}) ->
    let tensorInitStmts =
      foldl
        (lam acc : [CExpr]. lam param : (CType, Name).
          concat acc (mapTensors env tensorInitWrapperCode param))
        [] t.params in
    CuTTop {tt with top = CTFun {t with body = concat tensorInitStmts t.body}}
  | t -> t
end

lang CudaTensorStatusUpdate = CudaTensorMemoryBase
  -- After every update of a tensor value, we insert an update of the
  -- appropriate status. As we cannot know at runtime whether the code runs on
  -- the CPU or the GPU, we use a macro to detect this statically (different
  -- code is generated for CPU and GPU) and update the appropriate status.
  sem updateStatusAfterTensorSetStmt =
  | (CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = tensorExpr, id = key}}}}) & stmt ->
    if nameEq _tensorDataKey key then
      let setStateStmt = lam statusId.
        CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEBinOp {
            op = COSubScript (),
            lhs = CEVar {id = _tensorStateData},
            rhs = CEMember {lhs = tensorExpr, id = _tensorIdKey}},
          rhs = CEVar {id = statusId}}} in
      let cudaArchVar = CEVar {id = nameNoSym "__CUDA_ARCH__"} in
      let isFirstThreadExpr = CEBinOp {
        op = COEq (),
        lhs = CEBinOp {
          op = COAdd (),
          lhs = CEBinOp {
            op = COMul (),
            lhs = CEBlockDim {dim = CuDX ()},
            rhs = CEBlockIdx {dim = CuDX ()}},
          rhs = CEThreadIdx {dim = CuDX ()}},
        rhs = CEInt {i = 0}} in
      let stateUpdateMacroStmt = CSIfMacro {
        cond = CEBinOp {
          op = COAnd (),
          lhs = CEApp {fun = nameNoSym "defined", args = [cudaArchVar]},
          rhs = CEBinOp {
            op = COGt (),
            lhs = cudaArchVar,
            rhs = CEInt {i = 0}}},
        thn = [
          -- NOTE(larshum, 2022-03-25): We only update the state in the first
          -- thread, or we will get a big negative performance impact. Probably
          -- due to multiple threads writing to the same global data.
          CSIf {
            cond = isFirstThreadExpr,
            thn = [setStateStmt _tensorStateCpuInvalid],
            els = []}],
        els = [setStateStmt _tensorStateGpuInvalid]} in
      [stmt, stateUpdateMacroStmt]
    else [stmt]
  | stmt -> [stmt]

  -- Adds code for updating the status after every 'tensorSetExn' update (as
  -- this is C code, it is a write to the .data key of a tensor).
  sem updateStatusAfterTensorSet =
  | CuTTop (tt & {top = CTFun t}) ->
    let newBody = join (map updateStatusAfterTensorSetStmt t.body) in
    CuTTop {tt with top = CTFun {t with body = newBody}}
  | t -> t
end

-- Replaces the tensor copy and free operation statement nodes with actual code
-- for handling tensor data, by making use of the global tensor memory
-- variables.
lang CudaTensorReplaceMemoryOperations = CudaTensorMemoryBase
  sem _tensorDataAccess (id : Name) =
  | cexpr ->
    CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = id},
      rhs = CEMember {lhs = cexpr, id = _tensorIdKey}}

  sem replaceTensorMemoryOperationStmt : CudaTensorEnv -> [CStmt] -> CStmt -> [CStmt]
  sem replaceTensorMemoryOperationStmt env acc =
  | CSTensorDataCopyCpu t ->
    let env : CudaTensorEnv = env in
    let cpuData = _tensorDataAccess _tensorCpuData t.src in
    let gpuData = _tensorDataAccess _tensorGpuData t.src in
    let sizeData = _tensorDataAccess _tensorSizeData t.src in
    let status = _tensorDataAccess _tensorStateData t.src in
    let assignStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = t.dst,
      rhs = t.src}} in
    let copyGpuToCpuStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        cpuData, gpuData, sizeData,
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let setStatusOkStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = status,
      rhs = CEVar {id = _tensorStateOk}}} in
    let copyIfInvalidStmt = CSIf {
      cond = CEBinOp {
        op = COEq (),
        lhs = status,
        rhs = CEVar {id = _tensorStateCpuInvalid}},
      thn = [copyGpuToCpuStmt, setStatusOkStmt],
      els = []} in
    let setDstDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = t.dst, id = _tensorDataKey},
      rhs = CECast {ty = t.dataTy, rhs = cpuData}}} in
    if env.useTensorUnifiedMemory then
      concat acc [assignStmt, setDstDataStmt]
    else concat acc [assignStmt, copyIfInvalidStmt, setDstDataStmt]
  | CSTensorDataCopyGpu t ->
    let env : CudaTensorEnv = env in
    let cpuData = _tensorDataAccess _tensorCpuData t.src in
    let gpuData = _tensorDataAccess _tensorGpuData t.src in
    let sizeData = _tensorDataAccess _tensorSizeData t.src in
    let status = _tensorDataAccess _tensorStateData t.src in
    let null = CEVar {id = nameNoSym "NULL"} in
    let assignStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = t.dst,
      rhs = t.src}} in
    let allocGpuDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMalloc,
      args = [CEUnOp {op = COAddrOf (), arg = gpuData}, sizeData]}} in
    let allocIfNullStmt = CSIf {
      cond = CEBinOp {
        op = COEq (),
        lhs = gpuData,
        rhs = null},
      thn = [allocGpuDataStmt],
      els = []} in
    let copyCpuToGpuStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        gpuData, cpuData, sizeData, CEVar {id = _cudaMemcpyHostToDevice}]}} in
    let setStatusOkStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = status,
      rhs = CEVar {id = _tensorStateOk}}} in
    let copyIfInvalidStmt = CSIf {
      cond = CEBinOp {
        op = COEq (),
        lhs = status,
        rhs = CEVar {id = _tensorStateGpuInvalid}},
      thn = [copyCpuToGpuStmt, setStatusOkStmt],
      els = []} in
    let setDstDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = t.dst, id = _tensorDataKey},
      rhs = CECast {ty = t.dataTy, rhs = gpuData}}} in
    if env.useTensorUnifiedMemory then
      concat acc [assignStmt, setDstDataStmt]
    else
      concat acc [assignStmt, allocIfNullStmt, copyIfInvalidStmt, setDstDataStmt]
  | CSIf t ->
    snoc acc
      (CSIf {{t with thn = foldl (replaceTensorMemoryOperationStmt env) [] t.thn}
                with els = foldl (replaceTensorMemoryOperationStmt env) [] t.els})
  | CSSwitch t ->
    let replaceTensorOpsCase : (Int, [CStmt]) -> (Int, [CStmt]) =
      lam switchCase.
      match switchCase with (i, stmts) in
      (i, foldl (replaceTensorMemoryOperationStmt env) [] stmts) in
    let default = optionMap (foldl (replaceTensorMemoryOperationStmt env) []) t.default in
    snoc acc
      (CSSwitch {{t with body = map replaceTensorOpsCase t.body}
                    with default = default})
  | CSWhile t ->
    snoc acc
      (CSWhile {t with body = foldl (replaceTensorMemoryOperationStmt env) [] t.body})
  | CSComp t ->
    snoc acc
      (CSComp {t with stmts = foldl (replaceTensorMemoryOperationStmt env) [] t.stmts})
  | stmt -> snoc acc stmt

  sem replaceTensorMemoryOperations : CudaTensorEnv -> CuTop -> CuTop
  sem replaceTensorMemoryOperations env =
  | CuTTop (tt & {top = CTFun t}) ->
    let newBody = foldl (replaceTensorMemoryOperationStmt env) [] t.body in
    CuTTop {tt with top = CTFun {t with body = newBody}}
  | t -> t
end

lang CudaTensorMemory =
  CudaTensorGlobalWrapper + CudaTensorStatusUpdate +
  CudaTensorReplaceMemoryOperations

  sem _constructCudaTensorEnv : CompileCEnv -> Bool -> CudaTensorEnv
  sem _constructCudaTensorEnv ccEnv =
  | useTensorUnifiedMemory ->
    {ccEnv = ccEnv, useTensorUnifiedMemory = useTensorUnifiedMemory}

  sem applyTopTransformations : CudaTensorEnv -> CuTop -> CuTop
  sem applyTopTransformations env =
  | cudaTop ->
    let env : CudaTensorEnv = env in
    let cudaTop = addWrapperTensorCode env cudaTop in
    let cudaTop = updateStatusAfterTensorSet cudaTop in
    replaceTensorMemoryOperations env cudaTop

  sem addCudaTensorMemoryManagement : CompileCEnv -> [CuTop] -> Bool -> [CuTop]
  sem addCudaTensorMemoryManagement ccEnv tops =
  | useTensorUnifiedMemory ->
    let env = _constructCudaTensorEnv ccEnv useTensorUnifiedMemory in
    map (applyTopTransformations env) tops
end
