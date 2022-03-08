include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/pmexpr-ast.mc"

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

  sem _compileCopyToCpu (env : CompileCEnv) (dstId : Name) (arg : CExpr) =
  | TmCopy t ->
    let seqType = compileType env t.ty in
    let copySeqStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy, args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = dstId}}, arg,
        CESizeOfType {ty = seqType}, CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let elemType = _getSequenceElemType env t.ty in
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

  sem _compileCopyToGpu (env : CompileCEnv) (dstId : Name) (arg : CExpr) =
  | TmCopy t ->
    let seqType = compileType env t.ty in
    let elemType = _getSequenceElemType env t.ty in
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

  sem _compileFreeCpu (env : CompileCEnv) (arg : CExpr) =
  | TmFree t ->
    [CSExpr {expr = CEApp {
      fun = _free,
      args = [CEMember {lhs = CEVar {id = t.arg}, id = _seqKey}]}}]

  sem _compileFreeGpu (env : CompileCEnv) (arg : CExpr) =
  | TmFree t ->
    let seqType = compileType env t.tyArg in
    let tempId = nameSym "t" in
    let tempDeclStmt = CSDef {ty = seqType, id = Some tempId, init = None ()} in
    let cudaMemcpySeqStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}}, arg,
        CESizeOfType {ty = seqType},
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let cudaFreeGpuDataStmt = CSExpr {expr = CEApp {
      fun = _cudaFree,
      args = [CEMember {lhs = CEVar {id = tempId}, id = _seqKey}]}} in
    let cudaFreeGpuSeqStmt = CSExpr {expr = CEApp {
      fun = _cudaFree, args = [arg]}} in
    [tempDeclStmt, cudaMemcpySeqStmt, cudaFreeGpuDataStmt, cudaFreeGpuSeqStmt]

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
  | TmLoop t
  | TmParallelLoop t ->
    -- NOTE(larshum, 2022-03-08): Parallel loops that were not promoted to a
    -- kernel are compiled to sequential loops.
    CESeqLoop {n = compileExpr env t.n, f = compileExpr env t.f}
  | TmLoopKernel t ->
    CELoopKernel {
      n = compileExpr env t.n, f = compileExpr env t.f, opsPerThread = 10}

  sem compileStmt (env : CompileCEnv) (res : Result) =
  | TmCopy t ->
    -- NOTE(larshum, 2022-02-07): This must always be an identifier, since the
    -- result of a copy is always stored in a named variable.
    match res with RIdent dstId in
    let arg = compileExpr env t.arg in
    match t.toMem with Cpu _ then
      (env, _compileCopyToCpu env dstId arg (TmCopy t))
    else match t.toMem with Gpu _ then
      (env, _compileCopyToGpu env dstId arg (TmCopy t))
    else never
  | TmFree t ->
    let arg = CEVar {id = t.arg} in
    match t.mem with Cpu _ then
      (env, _compileFreeCpu env arg (TmFree t))
    else match t.mem with Gpu _ then
      (env, _compileFreeGpu env arg (TmFree t))
    else never

end
