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

lang CudaCompile = MExprCCompileAlloc + CudaPMExprAst + CudaAst
  sem _getSequenceElemType (env : CompileCEnv) =
  | ty ->
    -- TODO(larshum, 2022-02-08): Assumes 1d sequence
    match _unwrapType env.typeEnv ty with TySeq {ty = ty} then
      compileType env ty
    else infoErrorExit (infoTy ty) "Could not unwrap sequence type"

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

  sem compileOp (t: Expr) (args: [CExpr]) =
  | CMap _ ->
    CEMap {f = get args 0, s = get args 1}

  -- TODO(larshum, 2022-02-08): Support composite types other than 1d sequences.
  sem compileStmt (env : CompileCEnv) (res : Result) =
  | TmMapKernel t ->
    match res with RIdent id then
      -- TODO(larshum, 2022-02-08): Add a way to control the value of the
      -- 'opsPerElem' argument from the CUDA PMExpr AST.
      let kernelExpr = CEMapKernel {
        f = compileExpr env t.f, s = compileExpr env t.s,
        sTy = compileType env (tyTm t.s), retTy = compileType env t.ty,
        opsPerElem = 10} in
      let assignExpr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = id},
        rhs = kernelExpr} in
      (env, [CSExpr {expr = assignExpr}])
    else error "Internal compiler error: invalid map kernel call"
  | TmReduceKernel t -> error "not implemented yet"
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
