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
let _cudaDeviceSynchronize = nameNoSym "cudaDeviceSynchronize"
let _malloc = nameNoSym "malloc"
let _free = nameNoSym "free"

let cudaIncludes = concat cIncludes []

lang CudaCompileBase = MExprCCompileAlloc + CudaPMExprAst + CudaAst
  sem _stripPointer =
  | CTyPtr {ty = ty} -> ty
  | _ -> error "_stripPointer called with non-pointer type argument"

  sem _accessMember : CType -> CExpr -> Name -> CExpr
  sem _accessMember lhsType lhs =
  | id ->
    match lhsType with CTyPtr _ then
      CEArrow {lhs = lhs, id = id}
    else CEMember {lhs = lhs, id = id}
end

lang CudaCompileCopy = CudaCompileBase
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
  | TyRecord t ->
    mapFoldWithKey
      (lam acc : [CStmt]. lam key : SID. lam ty : Type.
        let ty = _unwrapType env.typeEnv ty in
        let fieldId = nameNoSym (sidToString key) in
        let dstField = CEMember {lhs = dst, id = fieldId} in
        let argField = CEMember {lhs = arg, id = fieldId} in
        concat acc (_compileCopyToCpu env dstField argField ty))
      [] t.fields
  | ty & (TyVariant t) ->
    let conType = TyCon {ident = _lookupTypeName env.typeEnv ty, info = infoTy ty} in
    let variantType = compileType env conType in
    let copyVariantStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        dst, arg,
        CESizeOfType {ty = variantType},
        _cudaMemcpyDeviceToHost]}} in
    let cnt = ref 0 in
    let copyInnerStmts =
      mapFoldWithKey
        (lam acc : [CStmt]. lam constrId : Name. lam constrTy : Type.
          let dstConstr = CEArrow {lhs = dst, id = constrId} in
          let innerArg = CEArrow {lhs = arg, id = constrId} in
          let constrTy = _unwrapType env.typeEnv constrTy in
          let copyInnerStmts = _compileCopyToCpu env dstConstr innerArg constrTy in
          let count = deref cnt in
          (modref cnt (addi count 1));
          [ CSIf {
              cond = CEBinOp {
                op = COEq (),
                lhs = CEArrow {lhs = arg, id = _constrKey},
                rhs = CEInt {i = count}},
              thn = copyInnerStmts,
              els = acc} ])
        [] t.constrs in
    snoc copyVariantStmt copyInnerStmts
  | TyInt _ | TyChar _ | TyFloat _ | TyBool _ | TyTensor _ ->
    [CSExpr {expr = CEBinOp {op = COAssign (), lhs = dst, rhs = arg}}]
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
  | TyRecord t ->
    mapFoldWithKey
      (lam acc : [CStmt]. lam key : SID. lam ty : Type.
        let ty = _unwrapType env.typeEnv ty in
        let fieldId = nameNoSym (sidToString key) in
        let dstField = CEMember {lhs = dst, id = fieldId} in
        let argField = CEMember {lhs = arg, id = fieldId} in
        concat acc (_compileCopyToGpu env dstField argField ty))
      [] t.fields
  | ty & (TyVariant t) ->
    let conType = TyCon {ident = _lookupTypeName env.typeEnv ty, info = infoTy ty} in
    let variantType = compileType env conType in
    let tempId = nameSym "t" in
    let temp = CEVar {id = tempId} in
    let sizeExpr = CESizeOfType {ty = _stripPointer variantType} in
    let tempAllocStmt = CSDef {
      ty = variantType, id = Some tempId,
      init = Some (CIExpr {expr = CECast {
        ty = variantType,
        rhs = CEApp {fun = _malloc, args = [sizeExpr]}}})} in
    let setTempConstrStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = temp, id = _constrKey},
      rhs = CEArrow {lhs = arg, id = _constrKey}}} in

    let cnt = ref 0 in
    let innerCopyStmts =
      mapFoldWithKey
        (lam acc : [CStmt]. lam constrId : Name. lam constrTy : Type.
          let innerDst = CEArrow {lhs = temp, id = constrId} in
          let innerArg = CEArrow {lhs = arg, id = constrId} in
          let constrTy = _unwrapType env.typeEnv constrTy in
          let freeInnerStmts = _compileCopyToGpu env innerDst innerArg constrTy in
          let count = deref cnt in
          (modref cnt (addi count 1));
          [ CSIf {
              cond = CEBinOp {
                op = COEq (),
                lhs = CEArrow {lhs = arg, id = _constrKey},
                rhs = CEInt {i = count}},
              thn = freeInnerStmts,
              els = acc} ])
        [] t.constrs in

    let allocGpuStmt = CSExpr {expr = CEApp {
      fun = _cudaMalloc,
      args = [CEUnOp {op = COAddrOf (), arg = dst}, sizeExpr]}} in
    let copyGpuStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        dst, temp, sizeExpr,
        CEVar {id = _cudaMemcpyHostToDevice}]}} in
    let freeTempStmt = CSExpr {expr = CEApp {fun = _free, args = [temp]}} in
    join [
      [tempAllocStmt, setTempConstrStmt], innerCopyStmts,
      [allocGpuStmt, copyGpuStmt, freeTempStmt]]
  | TyInt _ | TyFloat _ | TyChar _ | TyBool _ | TyTensor _ ->
    [CSExpr {expr = CEBinOp { op = COAssign (), lhs = dst, rhs = arg}}]
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Copying CPU -> GPU not implemented for type " tystr)
end

lang CudaCompileFree = CudaCompileBase
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
  | TyRecord t ->
    mapFoldWithKey
      (lam acc : [CStmt]. lam key : SID. lam ty : Type.
        let ty = _unwrapType env.typeEnv ty in
        let fieldId = nameNoSym (sidToString key) in
        let fieldArg = CEMember {lhs = arg, id = fieldId} in
        concat acc (_compileFreeCpu env fieldArg ty))
      [] t.fields
  | TyVariant t ->
    let cnt = ref 0 in
    let freeInnerStmts =
      mapFoldWithKey
        (lam acc : [CStmt]. lam constrId : Name. lam constrTy : Type.
          let innerArg = CEArrow {lhs = arg, id = constrId} in
          let constrTy = _unwrapType env.typeEnv constrTy in
          let freeInnerStmts = _compileFreeCpu env innerArg constrTy in
          let count = deref cnt in
          (modref cnt (addi count 1));
          [ CSIf {
              cond = CEBinOp {
                op = COEq (),
                lhs = CEArrow {lhs = arg, id = _constrKey},
                rhs = CEInt {i = count}},
              thn = freeInnerStmts,
              els = acc} ])
        [] t.constrs in
    let freeVariantStmt = CSExpr {expr = CEApp {fun = _free, args = [arg]}} in
    snoc freeInnerStmts freeVariantStmt
  | TyTensor _ | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> []
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Freeing CPU memory not implemented for type " tystr)

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
  | ty & (TyVariant t) ->
    let cnt = ref 0 in
    let conType = TyCon {ident = _lookupTypeName env.typeEnv ty, info = infoTy ty} in
    let variantType = compileType env conType in
    let tempId = nameSym "t" in
    let temp = CEVar {id = tempId} in
    let sizeExpr = CESizeOfType {ty = _stripPointer variantType} in
    let allocTempStmt = CSDef {
      ty = variantType, id = Some tempId,
      init = Some (CIExpr {expr = CECast {
        ty = variantType,
        rhs = CEApp {fun = _malloc, args = [sizeExpr]}}})} in
    let memcpyStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        temp, arg, sizeExpr,
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let freeInnerStmts =
      mapFoldWithKey
        (lam acc : [CStmt]. lam constrId : Name. lam constrTy : Type.
          let innerArg = CEArrow {lhs = temp, id = constrId} in
          let constrTy = _unwrapType env.typeEnv constrTy in
          let freeInnerStmts = _compileFreeGpu env innerArg constrTy in
          let count = deref cnt in
          (modref cnt (addi count 1));
          [ CSIf {
              cond = CEBinOp {
                op = COEq (),
                lhs = CEArrow {lhs = temp, id = _constrKey},
                rhs = CEInt {i = count}},
              thn = freeInnerStmts,
              els = acc} ])
        [] t.constrs in
    let freeVariantStmt = CSExpr {expr = CEApp {fun = _cudaFree, args = [arg]}} in
    let freeTempStmt = CSExpr {expr = CEApp {
      fun = nameNoSym "free", args = [temp]}} in
    join [
      [allocTempStmt, memcpyStmt], freeInnerStmts
    , [freeVariantStmt, freeTempStmt]]
  | TyTensor _ | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> []
  | ty ->
    use MExprPrettyPrint in
    let tystr = type2str ty in
    error (concat "Freeing GPU memory not implemented for type " tystr)
end

lang CudaCompile = CudaCompileCopy + CudaCompileFree
  sem _getFunctionArgTypes (env : CompileCEnv) =
  | TmVar _ -> []
  | t & (TmApp _) ->
    match collectAppArguments t with (_, args) in
    map (lam arg. compileType env (tyTm arg)) args
  | t -> infoErrorExit (infoTm t) "Unsupported function type"

  sem compileExpr (env : CompileCEnv) =
  | TmSeqMap t -> infoErrorExit t.info "Maps are not supported"
  | TmSeqFoldl t ->
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqFoldl {
      f = compileExpr env t.f, acc = compileExpr env t.acc,
      s = compileExpr env t.s, sTy = compileType env (tyTm t.s),
      argTypes = argTypes, ty = compileType env t.ty}
  | TmParallelReduce t ->
    -- NOTE(larshum, 2022-03-22): Parallel reductions that are not promoted to
    -- a kernel are compiled to sequential folds.
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqFoldl {
      f = compileExpr env t.f, acc = compileExpr env t.ne,
      s = compileExpr env t.as, sTy = compileType env (tyTm t.as),
      argTypes = argTypes, ty = compileType env t.ty}
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
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqLoop {
      n = compileExpr env t.n, f = compileExpr env t.f, argTypes = argTypes}
  | TmLoopAcc t ->
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqLoopAcc {
      ne = compileExpr env t.ne, n = compileExpr env t.n,
      f = compileExpr env t.f, neTy = compileType env (tyTm t.ne),
      argTypes = argTypes}
  | TmLoopKernel t ->
    let argTypes = _getFunctionArgTypes env t.f in
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
