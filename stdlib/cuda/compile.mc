include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/pmexpr-ast.mc"
include "pmexpr/utils.mc"

let _cudaMalloc = nameNoSym "cudaMalloc"
let _cudaMemcpy = nameNoSym "cudaMemcpy"
let _cudaMemcpyDeviceToHost = nameNoSym "cudaMemcpyDeviceToHost"
let _cudaMemcpyHostToDevice = nameNoSym "cudaMemcpyHostToDevice"
let _cudaFree = nameNoSym "cudaFree"
let _malloc = nameNoSym "malloc"
let _free = nameNoSym "free"

let cudaIncludes = concat cIncludes []

lang CudaCompile = MExprCCompileAlloc + CudaPMExprAst + CudaAst
  sem _getSequenceElemType (env : CompileCEnv) =
  | ty ->
    -- TODO(larshum, 2022-02-08): Assumes 1d sequence
    match _unwrapType env.typeEnv ty with TySeq {ty = ty} then
      compileType env ty
    else infoErrorExit (infoTy ty) "Could not unwrap sequence type"

  sem _getStructDataElemType (env : CompileCEnv) =
  | cty ->
    recursive let findTypeId : CType -> Name = lam ty.
      match ty with CTyPtr t then findTypeId t
      else match ty with CTyVar {id = id} then id
      else error "Expected struct type"
    in
    let typeId = findTypeId cty in
    _getSequenceElemType env (TyCon {ident = typeId, info = NoInfo ()})

  sem _compileCopy (env : CompileCEnv) (dstId : Name) (arg : CExpr) (ty : CType) =
  | Cpu _ -> _compileCopyToCpu env dstId arg ty
  | Gpu _ -> _compileCopyToGpu env dstId arg ty

  sem _compileCopyToCpu (env : CompileCEnv) (dstId : Name) (arg : CExpr) =
  | ty & (TyCon _) ->
    let mexprType = _unwrapType env.typeEnv ty in
    match mexprType with TySeq {ty = elemType} then
      let seqType = compileType env mexprType in
      let copySeqStmt = CSExpr {expr = CEApp {
        fun = _cudaMemcpy, args = [
          CEUnOp {op = COAddrOf (), arg = CEVar {id = dstId}}, arg,
          CESizeOfType {ty = seqType}, CEVar {id = _cudaMemcpyDeviceToHost}]}} in
      let elemType = compileType env elemType in
      let sizeExpr = CEBinOp {
        op = COMul (),
        lhs = CEMember {lhs = CEVar {id = dstId}, id = _seqLenKey},
        rhs = CESizeOfType {ty = elemType}} in
      let tempType = CTyPtr {ty = elemType} in
      let tempId = nameSym "t" in
      let tempAllocStmt = CSDef {
        ty = CTyPtr {ty = elemType}, id = Some tempId,
        init = Some (CIExpr {expr = CECast {
          ty = tempType,
          rhs = CEApp {
            fun = _malloc,
            args = [sizeExpr]}}})} in
      let copyDataStmt = CSExpr {expr = CEApp {
        fun = _cudaMemcpy,
        args = [
          CEVar {id = tempId},
          CEMember {lhs = CEVar {id = dstId}, id = _seqKey},
          sizeExpr, CEVar {id = _cudaMemcpyDeviceToHost}]}} in
      let outTmpStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = CEVar {id = dstId}, id = _seqKey},
        rhs = CEVar {id = tempId}}} in
      [copySeqStmt, tempAllocStmt, copyDataStmt, outTmpStmt]
    else match mexprType with TyTensor {ty = elemType} then
      -- NOTE(larshum, 2022-03-16): Tensor memory operations are handled at a
      -- later stage in the compiler.
      let tensorDataType = CTyPtr {ty = compileType env elemType} in
      [CSTensorDataCopyCpu {src = arg, dstId = dstId, dataTy = tensorDataType}]
    else error "Not implemented yet"
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Copying GPU -> CPU not implemented for type " tystr)

  sem _compileCopyToGpu (env : CompileCEnv) (dstId : Name) (arg : CExpr) =
  | ty & (TyCon _) ->
    let mexprType = _unwrapType env.typeEnv ty in
    match mexprType with TySeq {ty = elemType} then
      let seqType = compileType env mexprType in
      let elemType = compileType env elemType in
      let tempId = nameSym "t" in
      let tempSeqDeclStmt = CSDef {ty = seqType, id = Some tempId, init = None ()} in
      let tempSetLenStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = CEVar {id = tempId}, id = _seqLenKey},
        rhs = CEMember {lhs = arg, id = _seqLenKey}}} in
      let sizeExpr = CEBinOp {
        op = COMul (),
        lhs = CEMember {lhs = CEVar {id = tempId}, id = _seqLenKey},
        rhs = CESizeOfType {ty = elemType}} in
      let cudaMallocDataStmt = CSExpr {expr = CEApp {
        fun = _cudaMalloc,
        args = [
          CEUnOp {op = COAddrOf (),
                  arg = CEMember {lhs = CEVar {id = tempId}, id = _seqKey}},
          sizeExpr]}} in
      let cudaMemcpyDataStmt = CSExpr {expr = CEApp {
        fun = _cudaMemcpy,
        args = [
          CEMember {lhs = CEVar {id = tempId}, id = _seqKey},
          CEMember {lhs = arg, id = _seqKey},
          sizeExpr, CEVar {id = _cudaMemcpyHostToDevice}]}} in
      let cudaMallocSeqStmt = CSExpr {expr = CEApp {
        fun = _cudaMalloc,
        args = [
          CEUnOp {op = COAddrOf (), arg = CEVar {id = dstId}},
          CESizeOfType {ty = seqType}]}} in
      let cudaMemcpySeqStmt = CSExpr {expr = CEApp {
        fun = _cudaMemcpy,
        args = [
          CEVar {id = dstId},
          CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}},
          CESizeOfType {ty = seqType},
          CEVar {id = _cudaMemcpyHostToDevice}]}} in
      [ tempSeqDeclStmt, tempSetLenStmt, cudaMallocDataStmt, cudaMemcpyDataStmt
      , cudaMallocSeqStmt, cudaMemcpySeqStmt ]
    else match mexprType with TyTensor {ty = elemType} then
      -- NOTE(larshum, 2022-03-16): Tensor memory operations are handled at a
      -- later stage in the compiler.
      let tensorDataType = CTyPtr {ty = compileType env elemType} in
      [CSTensorDataCopyGpu {src = arg, dstId = dstId, dataTy = tensorDataType}]
    else error "Unsupported type for copying"
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Copying CPU -> GPU not implemented for type " tystr)

  sem _compileFree (env : CompileCEnv) (arg : CExpr) (t : CExpr) =
  | Cpu _ -> _compileFreeCpu env arg t
  | Gpu _ -> _compileFreeGpu env arg t

  sem _compileFreeCpu (env : CompileCEnv) (arg : CExpr) =
  | TmFree (t & {tyArg = TyCon _}) ->
    let mexprType = _unwrapType env.typeEnv t.tyArg in
    match mexprType with TySeq _ then
      [CSExpr {expr = CEApp {
        fun = _free,
        args = [CEMember {lhs = CEVar {id = t.arg}, id = _seqKey}]}}]
    else match mexprType with TyTensor {ty = elemType} then
      []
    else error "Unsupported type for freeing CPU memory"
  | TmFree _ -> []

  sem _compileFreeGpu (env : CompileCEnv) (arg : CExpr) =
  | TmFree (t & {tyArg = TyCon _}) ->
    let mexprType = _unwrapType env.typeEnv t.tyArg in
    match mexprType with TySeq _ then
      let ty = compileType env mexprType in
      let tempId = nameSym "t" in
      let temp = CEVar {id = tempId} in
      let tempDeclStmt = CSDef {ty = ty, id = Some tempId, init = None ()} in
      let cudaMemcpySeqStmt = CSExpr {expr = CEApp {
        fun = _cudaMemcpy,
        args = [
          CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}}, arg,
          CESizeOfType {ty = ty},
          CEVar {id = _cudaMemcpyDeviceToHost}]}} in
      let cudaDataExpr =
        match t.tyArg with TySeq _ then CEMember {lhs = temp, id = _seqKey}
        else CEMember {lhs = temp, id = _tensorDataKey} in
      let cudaFreeGpuDataStmt = CSExpr {expr = CEApp {
        fun = _cudaFree, args = [cudaDataExpr]}} in
      let cudaFreeGpuSeqStmt = CSExpr {expr = CEApp {
        fun = _cudaFree, args = [arg]}} in
      [tempDeclStmt, cudaMemcpySeqStmt, cudaFreeGpuDataStmt, cudaFreeGpuSeqStmt]
    else match mexprType with TyTensor _ then
      -- NOTE(larshum, 2022-03-16): Tensor memory operations are handled at a
      -- later stage in the compiler.
      [CSTensorDataFreeGpu {arg = arg}]
    else error "Unsupported type for freeing GPU memory"
  | TmFree _ -> []

  sem compileExpr (env : CompileCEnv) =
  | TmSeqMap t ->
    CESeqMap {
      f = compileExpr env t.f, s = compileExpr env t.s,
      sTy = compileType env (tyTm t.s), ty = compileType env t.ty}
  | TmSeqFoldl t ->
    CESeqFoldl {
      f = compileExpr env t.f, acc = compileExpr env t.acc,
      s = compileExpr env t.s, sTy = compileType env (tyTm t.s),
      ty = compileType env t.ty}
  | TmTensorSliceExn t ->
    CETensorSliceExn {
      t = compileExpr env t.t, slice = compileExpr env t.slice,
      ty = compileType env t.ty}
  | TmTensorSubExn t ->
    CETensorSubExn {
      t = compileExpr env t.t, ofs = compileExpr env t.ofs,
      len = compileExpr env t.len, ty = compileType env t.ty}
  | TmMapKernel t ->
    -- TODO(larshum, 2022-02-08): Add a way to control the value of the
    -- 'opsPerThread' argument from the CUDA PMExpr AST.
    CEMapKernel {
      f = compileExpr env t.f, s = compileExpr env t.s,
      sTy = compileType env (tyTm t.s), ty = compileType env t.ty,
      opsPerThread = 10}
  | TmReduceKernel t -> error "not implemented yet"
  | op & (TmLoop t | TmParallelLoop t | TmLoopKernel t) ->
    let argTypes =
      match t.f with TmVar _ then []
      else match t.f with TmApp _ then
        match collectAppArguments t.f with (_, args) in
        map (lam arg. compileType env (tyTm arg)) args
      else
        infoErrorExit t.info "Unsupported function type"
    in
    -- NOTE(larshum, 2022-03-08): Parallel loops that were not promoted to a
    -- kernel are compiled to sequential loops.
    match op with TmLoopKernel _ then
      CELoopKernel {
        n = compileExpr env t.n, f = compileExpr env t.f, argTypes = argTypes,
        opsPerThread = 10}
    else
      CESeqLoop {
        n = compileExpr env t.n, f = compileExpr env t.f, argTypes = argTypes}

  sem compileStmt (env : CompileCEnv) (res : Result) =
  | t & (TmCopy {arg = arg, toMem = toMem, ty = ty}) ->
    let arg = CEVar {id = arg} in
    match res with RReturn _ then
      match ty with TyRecord {labels = []} then (env, [])
      else
        let dstId = nameSym "temp" in
        let copyStmts = _compileCopy env dstId arg ty toMem in
        (env, snoc copyStmts (CSRet {val = Some (CEVar {id = dstId})}))
    else match res with RNone _ then (env, [])
    else match res with RIdent dstId in
      (env, _compileCopy env dstId arg ty toMem)
  | t & (TmFree {arg = arg, mem = mem}) ->
    let arg = CEVar {id = arg} in
    (env, _compileFree env arg t mem)

end
