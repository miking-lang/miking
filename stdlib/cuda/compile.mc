include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/pmexpr-ast.mc"
include "pmexpr/utils.mc"

let _cudaMalloc = nameNoSym "cudaMalloc"
let _cudaMallocManaged = nameNoSym "cudaMallocManaged"
let _cudaMemcpy = nameNoSym "cudaMemcpy"
let _cudaMemcpyDeviceToHost = nameNoSym "cudaMemcpyDeviceToHost"
let _cudaMemcpyHostToDevice = nameNoSym "cudaMemcpyHostToDevice"
let _cudaFree = nameNoSym "cudaFree"
let _malloc = nameNoSym "malloc"
let _free = nameNoSym "free"

let cudaIncludes = concat cIncludes []

lang CudaCompileCopy = MExprCCompileAlloc + CudaPMExprAst + CudaAst
  sem _compileCopy (env : CompileCEnv) (dst : CExpr) (arg : CExpr) (ty : CType) =
  | Cpu _ -> _compileCopyToCpu env dst arg ty
  | Gpu _ -> _compileCopyToGpu env dst arg ty

  sem _compileCopyToCpu (env : CompileCEnv) (dst : CExpr) (arg : CExpr) =
  | ty & (TySeq {ty = elemType}) ->
    let conType = TyCon {ident = _lookupTypeName env.typeEnv ty, info = infoTy ty} in
    let seqType = compileType env conType in
    let setSeqLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = dst, id = _seqLenKey},
      rhs = CEMember {lhs = arg, id = _seqLenKey}}} in
    let cElemType = compileType env elemType in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEMember {lhs = dst, id = _seqLenKey},
      rhs = CESizeOfType {ty = cElemType}} in
    let allocSeqDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = dst, id = _seqKey},
      rhs = CECast {
        ty = CTyPtr {ty = cElemType},
        rhs = CEApp {
          fun = _malloc, args = [sizeExpr]}}}} in
    let copySeqDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        CEMember {lhs = dst, id = _seqKey},
        CEMember {lhs = arg, id = _seqKey},
        sizeExpr,
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in

    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let innerDstId = nameSym "t" in
    let innerDst = CEVar {id = innerDstId} in
    let innerDstInitStmt = CSDef {
      ty = cElemType, id = Some innerDstId, init = None ()} in
    let srcExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEMember {lhs = dst, id = _seqKey},
      rhs = iter} in
    let elemType = _unwrapType env.typeEnv elemType in
    let copyInnerStmts = _compileCopyToCpu env innerDst srcExpr elemType in
    let assignInnerStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = srcExpr, rhs = innerDst}} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let copyInnerLoop = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = iter,
        rhs = CEMember {lhs = dst, id = _seqLenKey}},
      body = join [ [innerDstInitStmt], copyInnerStmts
                  , [assignInnerStmt, iterIncrementStmt] ]} in

    [ setSeqLenStmt, allocSeqDataStmt, copySeqDataStmt, iterInitStmt
    , copyInnerLoop ]
  | TyTensor {ty = elemType} ->
    -- NOTE(larshum, 2022-03-16): Tensor memory operations are handled at a
    -- later stage in the compiler.
    let tensorDataType = CTyPtr {ty = compileType env elemType} in
    [CSTensorDataCopyCpu {src = arg, dst = dst, dataTy = tensorDataType}]
  | TyInt _ | TyChar _ | TyFloat _ | TyBool _ ->
    [CSExpr {expr = CEBinOp {op = COAssign (), lhs = dst, rhs = arg}}]
  | TyRecord t ->
    mapFoldWithKey
      (lam acc : [CStmt]. lam key : SID. lam ty : Type.
        let ty = _unwrapType env.typeEnv ty in
        let fieldId = nameNoSym (sidToString key) in
        let dstField = CEMember {lhs = dst, id = fieldId} in
        let argField = CEMember {lhs = arg, id = fieldId} in
        concat acc (_compileCopyToCpu env dstField argField ty))
      [] t.fields
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Copying GPU -> CPU not implemented for type " tystr)

  sem _compileCopyToGpu (env : CompileCEnv) (dst : CExpr) (arg : CExpr) =
  | ty & (TySeq {ty = elemType}) ->
    let conType = TyCon {ident = _lookupTypeName env.typeEnv ty, info = infoTy ty} in
    let seqType = compileType env conType in
    let cElemType = compileType env elemType in
    let setSeqLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = dst, id = _seqLenKey},
      rhs = CEMember {lhs = arg, id = _seqLenKey}}} in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEMember {lhs = dst, id = _seqLenKey},
      rhs = CESizeOfType {ty = cElemType}} in

    let tempDataId = nameSym "t" in
    let tempData = CEVar {id = tempDataId} in
    let allocTempDataStmt = CSDef {
      ty = CTyPtr {ty = cElemType}, id = Some tempDataId,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = cElemType},
        rhs = CEApp {fun = _malloc, args = [sizeExpr]}}})} in
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let innerDst = CEBinOp {op = COSubScript (), lhs = tempData, rhs = iter} in
    let innerArg = CEBinOp {
      op = COSubScript (),
      lhs = CEMember {lhs = arg, id = _seqKey},
      rhs = iter} in
    let elemType = _unwrapType env.typeEnv elemType in
    let copyInnerStmts = _compileCopyToGpu env innerDst innerArg elemType in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let copyInnerLoop = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = iter,
        rhs = CEMember {lhs = dst, id = _seqLenKey}},
      body = snoc copyInnerStmts iterIncrementStmt} in

    let allocSeqDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMalloc,
      args = [
        CEUnOp {op = COAddrOf (), arg = CEMember {lhs = dst, id = _seqKey}},
        sizeExpr]}} in
    let copySeqDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        CEMember {lhs = dst, id = _seqKey},
        tempData, sizeExpr,
        CEVar {id = _cudaMemcpyHostToDevice}]}} in
    let freeTempDataStmt = CSExpr {expr = CEApp {
      fun = _free, args = [tempData]}} in
    [ setSeqLenStmt, allocTempDataStmt, iterInitStmt, copyInnerLoop
    , allocSeqDataStmt , copySeqDataStmt , freeTempDataStmt ]
  | TyTensor {ty = elemType} ->
    -- NOTE(larshum, 2022-03-16): Tensor memory operations are handled at a
    -- later stage in the compiler.
    let tensorDataType = CTyPtr {ty = compileType env elemType} in
    [CSTensorDataCopyGpu {src = arg, dst = dst, dataTy = tensorDataType}]
  | TyRecord t ->
    mapFoldWithKey
      (lam acc : [CStmt]. lam key : SID. lam ty : Type.
        let ty = _unwrapType env.typeEnv ty in
        let fieldId = nameNoSym (sidToString key) in
        let dstField = CEMember {lhs = dst, id = fieldId} in
        let argField = CEMember {lhs = arg, id = fieldId} in
        concat acc (_compileCopyToGpu env dstField argField ty))
      [] t.fields
  | TyInt _ | TyFloat _ | TyChar _ | TyBool _ ->
    [CSExpr {expr = CEBinOp { op = COAssign (), lhs = dst, rhs = arg}}]
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Copying CPU -> GPU not implemented for type " tystr)
end

lang CudaCompileFree = MExprCCompileAlloc + CudaPMExprAst + CudaAst
  sem _compileFree (env : CompileCEnv) (arg : CExpr) (tyArg : Type) =
  | Cpu _ -> _compileFreeCpu env arg tyArg
  | Gpu _ -> _compileFreeGpu env arg tyArg

  sem _compileFreeCpu (env : CompileCEnv) (arg : CExpr) =
  | TySeq {ty = elemType} ->
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let innerArg = CEBinOp {
      op = COSubScript (),
      lhs = CEMember {lhs = arg, id = _seqKey},
      rhs = iter} in
    let elemType = _unwrapType env.typeEnv elemType in
    let freeInnerStmts = _compileFreeCpu env innerArg elemType in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let lenExpr = CEMember {lhs = arg, id = _seqLenKey} in
    let freeInnerLoopStmt = CSWhile {
      cond = CEBinOp {op = COLt (), lhs = iter, rhs = lenExpr},
      body = snoc freeInnerStmts iterIncrementStmt} in
    let freeSeqStmt = CSExpr {expr = CEApp {
      fun = _free,
      args = [CEMember {lhs = arg, id = _seqKey}]}} in
    [iterInitStmt, freeInnerLoopStmt, freeSeqStmt]
  | TyTensor _ | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> []
  | TyRecord t ->
    mapFoldWithKey
      (lam acc : [CStmt]. lam key : SID. lam ty : Type.
        let ty = _unwrapType env.typeEnv ty in
        let fieldId = nameNoSym (sidToString key) in
        let fieldArg = CEMember {lhs = arg, id = fieldId} in
        concat acc (_compileFreeCpu env fieldArg ty))
      [] t.fields
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    let infostr = info2str (infoTy ty) in
    error (join [infostr, "Freeing CPU memory not implemented for type ", tystr])

  sem _compileFreeGpu (env : CompileCEnv) (arg : CExpr) =
  | ty & (TySeq {ty = elemType}) ->
    let conType = TyCon {ident = _lookupTypeName env.typeEnv ty, info = infoTy ty} in
    let seqType = compileType env conType in
    let cElemType = compileType env elemType in

    let tempId = nameSym "t" in
    let temp = CEVar {id = tempId} in
    let lengthExpr = CEMember {lhs = arg, id = _seqLenKey} in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = lengthExpr,
      rhs = CESizeOfType {ty = cElemType}} in
    let tempDefStmt = CSDef {
      ty = CTyPtr {ty = cElemType}, id = Some tempId,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = cElemType},
        rhs = CEApp {fun = _malloc, args = [sizeExpr]}}})} in
    let copyDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        temp,
        CEMember {lhs = arg, id = _seqKey},
        sizeExpr,
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let innerArg = CEBinOp {op = COSubScript (), lhs = temp, rhs = iter} in
    let elemType = _unwrapType env.typeEnv elemType in
    let freeInnerStmts = _compileFreeGpu env innerArg elemType in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let freeLoopStmt = CSWhile {
      cond = CEBinOp {op = COLt (), lhs = iter, rhs = lengthExpr},
      body = snoc freeInnerStmts iterIncrementStmt} in
    let freeGpuDataStmt = CSExpr {expr = CEApp {
      fun = _cudaFree,
      args = [CEMember {lhs = arg, id = _seqKey}]}} in
    let freeTempStmt = CSExpr {expr = CEApp {fun = _free, args = [temp]}} in
    [ tempDefStmt, copyDataStmt, iterInitStmt, freeLoopStmt, freeGpuDataStmt
    , freeTempStmt ]
  | TyRecord t ->
    mapFoldWithKey
      (lam acc : [CStmt]. lam key : SID. lam ty : Type.
        let ty = _unwrapType env.typeEnv ty in
        let fieldId = nameNoSym (sidToString key) in
        let fieldArg = CEMember {lhs = arg, id = fieldId} in
        concat acc (_compileFreeGpu env fieldArg ty))
      [] t.fields
  | TyTensor _ | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> []
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Freeing GPU memory not implemented for type " tystr)
end

lang CudaCompile = CudaCompileCopy + CudaCompileFree
  sem _getLoopFunctionArgTypes (env : CompileCEnv) =
  | TmVar _ -> []
  | t & (TmApp _) ->
    match collectAppArguments t with (_, args) in
    map (lam arg. compileType env (tyTm arg)) args
  | t -> infoErrorExit (infoTm t) "Unsupported function type"

  sem compileExpr (env : CompileCEnv) =
  | TmSeqMap t -> infoErrorExit t.info "Maps are not supported"
  | TmSeqFoldl t ->
    CESeqFoldl {
      f = compileExpr env t.f, acc = compileExpr env t.acc,
      s = compileExpr env t.s, sTy = compileType env (tyTm t.s),
      ty = compileType env t.ty}
  | TmParallelReduce t ->
    -- NOTE(larshum, 2022-03-22): Parallel reductions that are not promoted to
    -- a kernel are compiled to sequential folds.
    CESeqFoldl {
      f = compileExpr env t.f, acc = compileExpr env t.ne,
      s = compileExpr env t.as, sTy = compileType env (tyTm t.as),
      ty = compileType env t.ty}
  | TmTensorSliceExn t ->
    CETensorSliceExn {
      t = compileExpr env t.t, slice = compileExpr env t.slice,
      ty = compileType env t.ty}
  | TmTensorSubExn t ->
    CETensorSubExn {
      t = compileExpr env t.t, ofs = compileExpr env t.ofs,
      len = compileExpr env t.len, ty = compileType env t.ty}
  | TmMapKernel t -> infoErrorExit t.info "Maps are not supported"
  | TmReduceKernel t -> error "not implemented yet"
  | TmLoop t | TmParallelLoop t ->
    -- NOTE(larshum, 2022-03-08): Parallel loops that were not promoted to a
    -- kernel are compiled to sequential loops.
    let argTypes = _getLoopFunctionArgTypes env t.f in
    CESeqLoop {
      n = compileExpr env t.n, f = compileExpr env t.f, argTypes = argTypes}
  | TmLoopAcc t ->
    let argTypes = _getLoopFunctionArgTypes env t.f in
    CESeqLoopAcc {
      ne = compileExpr env t.ne, n = compileExpr env t.n,
      f = compileExpr env t.f, neTy = compileType env (tyTm t.ne),
      argTypes = argTypes}
  | TmLoopKernel t ->
    let argTypes = _getLoopFunctionArgTypes env t.f in
    CELoopKernel {
      n = compileExpr env t.n, f = compileExpr env t.f, argTypes = argTypes,
      opsPerThread = 10}

  sem compileStmt (env : CompileCEnv) (res : Result) =
  | TmCopy {arg = arg, toMem = toMem, ty = ty} ->
    let arg = CEVar {id = arg} in
    match res with RReturn _ then
      match ty with TyRecord {labels = []} then (env, [])
      else
        let dstId = nameSym "temp" in
        let dst = CEVar {id = dstId} in
        let defStmt = CSDef {
          ty = compileType env ty, id = Some dstId, init = None ()} in
        let ty = _unwrapType env.typeEnv ty in
        let copyStmts = _compileCopy env dst arg ty toMem in
        (env, join [[defStmt], copyStmts, [CSRet {val = Some dst}]])
    else match res with RNone _ then (env, [])
    else match res with RIdent dstId in
      let dst = CEVar {id = dstId} in
      let ty = _unwrapType env.typeEnv ty in
      (env, _compileCopy env dst arg ty toMem)
  | TmFree {arg = arg, tyArg = tyArg, mem = mem} ->
    let arg = CEVar {id = arg} in
    let tyArg = _unwrapType env.typeEnv tyArg in
    (env, _compileFree env arg tyArg mem)

end
