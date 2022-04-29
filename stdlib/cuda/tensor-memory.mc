-- CUDA management of tensor memory. The data of tensors 

include "cuda/ast.mc"
include "cuda/compile.mc"

let _tensorStateOk = nameSym "STATE_OK"
let _tensorStateCpuInvalid = nameSym "STATE_CPU_INVALID"
let _tensorStateGpuInvalid = nameSym "STATE_GPU_INVALID"
let _tensorStateNames = [_tensorStateOk, _tensorStateCpuInvalid, _tensorStateGpuInvalid]

let _tensorDataId = nameSym "tensor_data"
let _tensorDataTypeId = nameSym "TensorData"
let _tensorCpuKey = nameSym "cpu"
let _tensorGpuKey = nameSym "gpu"
let _tensorSizeKey = nameSym "size"
let _tensorStateKey = nameSym "state"

-- Produces additional code to insert at the beginning and end of each wrapper
-- function, for managing the memory of tensors.
lang CudaTensorGlobalWrapper = CudaCompile
  sem tensorInitWrapperCode (elemTy : CType) =
  | tensorExpr ->
    let indexExpr = CEMember {lhs = tensorExpr, id = _tensorIdKey} in
    let tensorDataAccess = lam key.
      CEMember {
        lhs = CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = _tensorDataId},
          rhs = indexExpr},
        id = key} in
    let cpuDataInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = tensorDataAccess _tensorCpuKey,
      rhs = CEMember {lhs = tensorExpr, id = _tensorDataKey}}} in
    let gpuDataInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = tensorDataAccess _tensorGpuKey,
      rhs = CEVar {id = nameNoSym "NULL"}}} in
    let sizeExpr = tensorDataAccess _tensorSizeKey in
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
    let sizeDataInitStmts = [sizeCountInitStmt, iterInitStmt, sizeCountLoopStmt] in
    let statusInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = tensorDataAccess _tensorStateKey,
      rhs = CEVar {id = _tensorStateGpuInvalid}}} in
    join [[cpuDataInitStmt, gpuDataInitStmt], sizeDataInitStmts, [statusInitStmt]]

  sem mapTensors : CompileCEnv -> (CType -> CExpr -> [CStmt])
                -> (CType, Name) -> [CStmt]
  sem mapTensors (ccEnv : CompileCEnv) (tensorCallFn : CType -> CExpr -> [CStmt]) =
  | (CTyPtr {ty = CTyVar {id = tyId}}, id)
  | (CTyVar {id = tyId}, id) ->
    recursive let work = lam ty : Type. lam expr : CExpr.
      let ty = _unwrapType ccEnv.typeEnv ty in
      match ty with TyTensor {ty = elemTy} then
        let cElemTy = compileType ccEnv elemTy in
        tensorCallFn cElemTy expr
      else match ty with TyRecord t then
        let labels = tyRecordOrderedLabels ty in
        foldl
          (lam acc : [CStmt]. lam key : SID.
            let fieldTy = mapFindExn key t.fields in
            let fieldId = nameNoSym (sidToString key) in
            let fieldExpr = CEMember {lhs = expr, id = fieldId} in
            concat acc (work fieldTy fieldExpr))
          [] labels
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

  -- NOTE(larshum, 2022-03-18): All tensors are copied back (if needed) and
  -- freed at the end of the wrapper function.
  sem tensorFreeCode =
  | tensorCountId ->
    let iterId = nameSym "i" in
    let iterTensorKey = lam key.
      CEMember {
        lhs = CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = _tensorDataId},
          rhs = CEVar {id = iterId}},
        id = key} in
    let cpuData = iterTensorKey _tensorCpuKey in
    let gpuData = iterTensorKey _tensorGpuKey in
    let sizeData = iterTensorKey _tensorSizeKey in
    let status = iterTensorKey _tensorStateKey in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let copyDataToCpuStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        cpuData, gpuData, sizeData,
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let setStatusOkStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = status,
      rhs = CEVar {id = _tensorStateOk}}} in
    let copyDataToCpuIfInvalidStmt = CSIf {
      cond = CEBinOp {
        op = COAnd (),
        lhs = gpuData,
        rhs = CEBinOp {
          op = COEq (), lhs = status,
          rhs = CEVar {id = _tensorStateCpuInvalid}}},
      thn = [copyDataToCpuStmt, setStatusOkStmt],
      els = []} in
    let cudaFreeStmt = CSExpr {expr = CEApp {
      fun = _cudaFree, args = [gpuData]}} in
    let null = CEVar {id = nameNoSym "NULL"} in
    let setToNullStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = gpuData,
      rhs = null}} in
    let freeGpuDataStmt = CSIf {
      cond = gpuData,
      thn = [cudaFreeStmt, setToNullStmt],
      els = []} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = iterId},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = iterId},
        rhs = CEInt {i = 1}}}} in
    let loopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = iterId},
        rhs = CEVar {id = tensorCountId}},
      body = [copyDataToCpuIfInvalidStmt, freeGpuDataStmt, iterIncrementStmt]} in
    [iterInitStmt, loopStmt]

  -- Adds code for initialization of tensor data within wrapper functions.
  sem addWrapperTensorCode (ccEnv : CompileCEnv) (tensorCountId : Name) =
  | CuTTop (tt & {attrs = [], top = CTFun t}) ->
    let tensorDataAllocSizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = tensorCountId},
      rhs = CESizeOfType {ty = CTyVar {id = _tensorDataTypeId}}} in
    let tensorDataAllocStmt = CSExpr {expr = CEApp {
      fun = _cudaMallocManaged,
      args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = _tensorDataId}},
        tensorDataAllocSizeExpr]}} in
    let tensorInitStmts =
      foldl
        (lam acc : [CExpr]. lam param : (CType, Name).
          concat acc (mapTensors ccEnv tensorInitWrapperCode param))
        [] t.params in
    let tensorFreeStmts = tensorFreeCode tensorCountId in
    let tensorDataFreeStmt = CSExpr {expr = CEApp {
      fun = _cudaFree, args = [CEVar {id = _tensorDataId}]}} in
    let body = join [
      [tensorDataAllocStmt], tensorInitStmts, t.body, tensorFreeStmts,
      [tensorDataFreeStmt]] in
    CuTTop {tt with top = CTFun {t with body = body}}
  | t -> t
end

-- Produces the top-level definitions of the global data needed to keep track
-- of tensor allocations.
lang CudaTensorGlobalDefinitions = CudaAst
  sem generateGlobalTensorTops =
  | () ->
    let tensorCountId = nameSym "tensor_count" in
    let tensorCountTop = CuTTop {
      attrs = [],
      top = CTDef {ty = CTyInt64 (), id = Some tensorCountId, init = None ()}} in
    let stateEnumId = nameSym "tensor_state" in
    let stateEnumTop = CuTTop {
      attrs = [], 
      top = CTDef {
        ty = CTyEnum {id = Some stateEnumId, mem = Some _tensorStateNames},
        id = None (), init = None ()}} in
    let stateEnumType = CTyEnum {id = Some stateEnumId, mem = None ()} in
    let tensorDataStructType = CTyStruct {
      id = Some _tensorDataTypeId,
      mem = Some ([
        (CTyPtr {ty = CTyVoid ()}, Some _tensorCpuKey),
        (CTyPtr {ty = CTyVoid ()}, Some _tensorGpuKey),
        (CTyInt64 (), Some _tensorSizeKey),
        (stateEnumType, Some _tensorStateKey)])} in
    let tensorDataStructTop = CuTTop {
      attrs = [],
      top = CTDef {
        ty = tensorDataStructType, id = None (), init = None ()}} in
    let dataDefTop = CuTTop {
      attrs = [CuAManaged ()],
      top = CTDef {
        ty = CTyPtr {ty = CTyVar {id = _tensorDataTypeId}},
        id = Some _tensorDataId, init = None ()}} in
    ( tensorCountId
    , [tensorCountTop, stateEnumTop, tensorDataStructTop, dataDefTop])
end

lang CudaTensorStatusUpdate = CudaAst
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
      let setStatusStmt = lam statusKey.
        CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEMember {
            lhs = CEBinOp {
              op = COSubScript (),
              lhs = CEVar {id = _tensorDataId},
              rhs = CEMember {lhs = tensorExpr, id = _tensorIdKey}},
            id = _tensorStateKey},
          rhs = CEVar {id = statusKey}}}
      in
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
      let statusUpdateMacroStmt = CSIfMacro {
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
            thn = [setStatusStmt _tensorStateCpuInvalid],
            els = []}],
        els = [setStatusStmt _tensorStateGpuInvalid]} in
      [stmt, statusUpdateMacroStmt]
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
lang CudaTensorReplaceMemoryOperations = CudaAst
  sem _tensorKeyAccess (key : Name) =
  | cexpr ->
    CEMember {
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorDataId},
        rhs = CEMember {lhs = cexpr, id = _tensorIdKey}},
      id = key}

  sem replaceTensorMemoryOperationStmt (acc : [CStmt]) =
  | CSTensorDataCopyCpu t ->
    let cpuData = _tensorKeyAccess _tensorCpuKey t.src in
    let gpuData = _tensorKeyAccess _tensorGpuKey t.src in
    let sizeData = _tensorKeyAccess _tensorSizeKey t.src in
    let status = _tensorKeyAccess _tensorStateKey t.src in
    let assignStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = t.dst,
      rhs = t.src}} in
    let copyCpuToGpuStmt = CSExpr {expr = CEApp {
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
        rhs = CEVar {id = _tensorStateGpuInvalid}},
      thn = [],
      els = []} in
    let setDstDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = t.dst, id = _tensorDataKey},
      rhs = CECast {ty = t.dataTy, rhs = cpuData}}} in
    concat acc [assignStmt, copyIfInvalidStmt, setDstDataStmt]
  | CSTensorDataCopyGpu t ->
    let cpuData = _tensorKeyAccess _tensorCpuKey t.src in
    let gpuData = _tensorKeyAccess _tensorGpuKey t.src in
    let sizeData = _tensorKeyAccess _tensorSizeKey t.src in
    let status = _tensorKeyAccess _tensorStateKey t.src in
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
    concat acc [assignStmt, allocIfNullStmt, copyIfInvalidStmt, setDstDataStmt]
  | CSIf t ->
    snoc acc
      (CSIf {{t with thn = foldl replaceTensorMemoryOperationStmt [] t.thn}
                with els = foldl replaceTensorMemoryOperationStmt [] t.els})
  | CSSwitch t ->
    let replaceTensorOpsCase : (Int, [CStmt]) -> (Int, [CStmt]) =
      lam switchCase.
      match switchCase with (i, stmts) in
      (i, foldl replaceTensorMemoryOperationStmt [] stmts) in
    let default = optionMap (foldl replaceTensorMemoryOperationStmt []) t.default in
    snoc acc
      (CSSwitch {{t with body = map replaceTensorOpsCase t.body}
                    with default = default})
  | CSWhile t ->
    snoc acc
      (CSWhile {t with body = foldl replaceTensorMemoryOperationStmt [] t.body})
  | CSComp t ->
    snoc acc
      (CSComp {t with stmts = foldl replaceTensorMemoryOperationStmt [] t.stmts})
  | stmt -> snoc acc stmt

  sem replaceTensorMemoryOperations =
  | CuTTop (tt & {top = CTFun t}) ->
    let newBody = foldl replaceTensorMemoryOperationStmt [] t.body in
    CuTTop {tt with top = CTFun {t with body = newBody}}
  | t -> t
end

lang CudaTensorMemory =
  CudaTensorGlobalWrapper + CudaTensorGlobalDefinitions +
  CudaTensorStatusUpdate + CudaTensorReplaceMemoryOperations

  sem applyTopTransformations (ccEnv : CompileCEnv) (tensorCountId : Name) =
  | cudaTop ->
    let cudaTop = addWrapperTensorCode ccEnv tensorCountId cudaTop in
    let cudaTop = updateStatusAfterTensorSet cudaTop in
    replaceTensorMemoryOperations cudaTop

  sem addCudaTensorMemoryManagement (ccEnv : CompileCEnv) =
  | tops ->
    match generateGlobalTensorTops () with (tensorCountId, globalInitTops) in
    let tops = map (applyTopTransformations ccEnv tensorCountId) tops in
    (tensorCountId, concat globalInitTops tops)
end
