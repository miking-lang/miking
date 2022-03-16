-- CUDA management of tensor memory. The data of tensors 

include "cuda/ast.mc"
include "cuda/compile.mc"

let _tensorStateOk = nameSym "STATE_OK"
let _tensorStateCpuInvalid = nameSym "STATE_CPU_INVALID"
let _tensorStateGpuInvalid = nameSym "STATE_GPU_INVALID"
let _tensorStateNames = [_tensorStateOk, _tensorStateCpuInvalid, _tensorStateGpuInvalid]

let _tensorCpuDataKey = nameSym "tensor_cpu_data"
let _tensorGpuDataKey = nameSym "tensor_gpu_data"
let _tensorSizeDataKey = nameSym "tensor_data_size"
let _tensorStatusKey = nameSym "tensor_status"

lang CudaTensorMemoryBase = CudaCompile
  sem countTensorParams (ccEnv : CompileCEnv) (acc : Int) =
  | ty & (CTyVar t) ->
    let mexprType = TyCon {ident = t.id, info = NoInfo ()} in
    let mty = _unwrapType ccEnv.typeEnv mexprType in
    match mty with TyTensor _ then addi acc 1
    else match mty with TyRecord t then
      mapFoldWithKey
        (lam acc. lam. lam ty.
          let cty = compileType ccEnv ty in
          countTensorParams ccEnv acc cty)
        acc t.fields
    else acc
  | ty -> sfoldCTypeCType (countTensorParams ccEnv) acc ty
end

-- Produces additional code to insert at the beginning and end of each wrapper
-- function, for managing the memory of tensors.
lang CudaTensorGlobalWrapper = CudaTensorMemoryBase
  sem tensorInitWrapperCode (elemTy : CType) =
  | tensorExpr ->
    let indexExpr = CEMember {lhs = tensorExpr, id = _tensorIdKey} in
    let cpuDataInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorCpuDataKey},
        rhs = indexExpr},
      rhs = CEMember {lhs = tensorExpr, id = _tensorDataKey}}} in
    let gpuDataInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorGpuDataKey},
        rhs = indexExpr},
      rhs = CEVar {id = nameNoSym "NULL"}}} in
    let sizeExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = _tensorSizeDataKey},
      rhs = indexExpr} in
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
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorStatusKey},
        rhs = indexExpr},
      rhs = CEVar {id = _tensorStateGpuInvalid}}} in
    join [[cpuDataInitStmt, gpuDataInitStmt], sizeDataInitStmts, [statusInitStmt]]

  sem mapTensors (ccEnv : CompileCEnv) (tensorCallFn : CType -> CExpr -> [CStmt]) =
  | (CTyVar {id = tyId}, id) ->
    let idExpr = CEVar {id = id} in
    recursive let work = lam ty : Type.
      match ty with TyTensor {ty = elemTy} then
        let cElemTy = compileType ccEnv elemTy in
        tensorCallFn cElemTy idExpr
      else match ty with TyRecord t then
        mapFoldWithKey
          (lam acc : [CStmt]. lam. lam fieldTy : Type.
            concat acc (work fieldTy))
          [] t.fields
      else []
    in
    let lookupType = TyCon {ident = tyId, info = NoInfo ()} in
    work (_unwrapType ccEnv.typeEnv lookupType)
  | x -> []

  -- Adds code for initialization and destruction of tensor memory management
  -- within wrapper functions.
  sem addWrapperTensorCode (ccEnv : CompileCEnv) =
  | CuTTop (tt & {attrs = [], top = CTFun t}) ->
    let tensorInitStmts =
      foldl
        (lam acc : [CExpr]. lam param : (CType, Name).
          concat acc (mapTensors ccEnv tensorInitWrapperCode param))
        [] t.params in
    let ntensors =
      foldl
        (lam acc. lam param : (Name, Type). (countTensorParams ccEnv) acc param.0)
        0 t.params in
    let body = join [tensorInitStmts, t.body] in
    CuTTop {tt with top = CTFun {t with body = body}}
  | t -> t
end

-- Produces the top-level definitions of the global data needed to keep track
-- of tensor allocations.
lang CudaTensorGlobalDefinitions = CudaTensorMemoryBase
  sem generateGlobalTensorTops =
  | n ->
    let arrayType = lam elemTy.
      CTyArray {ty = elemTy, size = Some (CEInt {i = n})} in
    let cudaTopDef = lam defData : (Name, CType).
      match defData with (id, ty) in
      CuTTop {
        attrs = [CuAManaged ()],
        top = CTDef {ty = arrayType ty, id = Some id, init = None ()}} in
    let stateEnumId = nameSym "tensor_state" in
    let stateEnumDef = CuTTop {
      attrs = [], 
      top = CTDef {
        ty = CTyEnum {id = Some stateEnumId, mem = Some _tensorStateNames},
        id = None (), init = None ()}} in
    let arrayDefData = [
      (_tensorCpuDataKey, CTyPtr {ty = CTyVoid ()}),
      (_tensorGpuDataKey, CTyPtr {ty = CTyVoid ()}),
      (_tensorSizeDataKey, CTyInt64 ()),
      (_tensorStatusKey, CTyEnum {id = Some stateEnumId, mem = None ()})] in
    let defTops = map cudaTopDef arrayDefData in
    cons stateEnumDef defTops
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
      let setStatusStmt = lam statusKey.
        CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEBinOp {
            op = COSubScript (),
            lhs = CEVar {id = _tensorStatusKey},
            rhs = CEMember {lhs = tensorExpr, id = _tensorIdKey}},
          rhs = CEVar {id = statusKey}}}
      in
      let cudaArchVar = CEVar {id = nameNoSym "__CUDA_ARCH__"} in
      let statusUpdateMacroStmt = CSIfMacro {
        cond = CEBinOp {
          op = COAnd (),
          lhs = CEApp {fun = nameNoSym "defined", args = [cudaArchVar]},
          rhs = CEBinOp {
            op = COGt (),
            lhs = cudaArchVar,
            rhs = CEInt {i = 0}}},
        thn = [setStatusStmt _tensorStateCpuInvalid],
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
lang CudaTensorReplaceMemoryOperations = CudaTensorMemoryBase
  sem _tensorKeyAccess (key : Name) =
  | cexpr ->
    CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = key},
      rhs = CEMember {lhs = cexpr, id = _tensorIdKey}}

  sem replaceTensorMemoryOperationStmt =
  | CSTensorDataCopyCpu t ->
    let cpuData = _tensorKeyAccess _tensorCpuDataKey t.src in
    let gpuData = _tensorKeyAccess _tensorGpuDataKey t.src in
    let sizeData = _tensorKeyAccess _tensorSizeDataKey t.src in
    let status = _tensorKeyAccess _tensorStatusKey t.src in
    let assignStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = t.dstId},
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
      lhs = CEMember {lhs = CEVar {id = t.dstId}, id = _tensorDataKey},
      rhs = CECast {ty = t.dataTy, rhs = cpuData}}} in
    [assignStmt, copyIfInvalidStmt, setDstDataStmt]
  | CSTensorDataCopyGpu t ->
    let cpuData = _tensorKeyAccess _tensorCpuDataKey t.src in
    let gpuData = _tensorKeyAccess _tensorGpuDataKey t.src in
    let sizeData = _tensorKeyAccess _tensorSizeDataKey t.src in
    let status = _tensorKeyAccess _tensorStatusKey t.src in
    let null = CEVar {id = nameNoSym "NULL"} in
    let assignStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = t.dstId},
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
      lhs = CEMember {lhs = CEVar {id = t.dstId}, id = _tensorDataKey},
      rhs = CECast {ty = t.dataTy, rhs = gpuData}}} in
    [assignStmt, allocIfNullStmt, copyIfInvalidStmt, setDstDataStmt]
  | CSTensorDataFreeGpu t ->
    let null = CEVar {id = nameNoSym "NULL"} in
    let cpuData = _tensorKeyAccess _tensorCpuDataKey t.arg in
    let gpuData = _tensorKeyAccess _tensorGpuDataKey t.arg in
    let sizeData = _tensorKeyAccess _tensorSizeDataKey t.arg in
    let status = _tensorKeyAccess _tensorStatusKey t.arg in
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
    let setToNullStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = gpuData,
      rhs = null}} in
    let freeGpuDataStmt = CSIf {
      cond = gpuData,
      thn = [cudaFreeStmt, setToNullStmt],
      els = []} in
    [copyDataToCpuIfInvalidStmt, freeGpuDataStmt]
  | stmt -> [stmt]

  sem replaceTensorMemoryOperations =
  | CuTTop (tt & {top = CTFun t}) ->
    let newBody = join (map replaceTensorMemoryOperationStmt t.body) in
    CuTTop {tt with top = CTFun {t with body = newBody}}
  | t -> t
end

lang CudaTensorMemory =
  CudaTensorGlobalWrapper + CudaTensorGlobalDefinitions +
  CudaTensorStatusUpdate + CudaTensorReplaceMemoryOperations

  -- Finds the maximum number of tensor parameters among all wrapper functions.
  sem findMaxNumTensorParams (ccEnv : CompileCEnv) (acc : Int) =
  -- NOTE(larshum, 2022-03-15): The only CUDA functions that have no explicit
  -- attributes are wrappers.
  | CuTTop {attrs = [], top = CTFun t} ->
    -- NOTE(larshum, 2022-03-15): We have to look through the type because
    -- tensors wrapped in records must also be counted.
    let tensorParams =
      foldl
        (lam acc. lam param : (CType, Name). countTensorParams ccEnv acc param.0)
        0 t.params in
    if gti tensorParams acc then tensorParams else acc
  | t -> acc

  sem applyTopTransformations (ccEnv : CompileCEnv) =
  | cudaTop ->
    let cudaTop = addWrapperTensorCode ccEnv cudaTop in
    let cudaTop = updateStatusAfterTensorSet cudaTop in
    replaceTensorMemoryOperations cudaTop

  sem addCudaTensorMemoryManagement (ccEnv : CompileCEnv) =
  | tops ->
    let maxNumTensorParams = foldl (findMaxNumTensorParams ccEnv) 0 tops in
    let globalInitTops = generateGlobalTensorTops maxNumTensorParams in
    let tops = map (applyTopTransformations ccEnv) tops in
    concat globalInitTops tops
end
