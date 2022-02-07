include "c/compile.mc"
include "cuda/ast.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "pmexpr/wrapper.mc"

lang CudaCWrapperBase = PMExprCWrapper + CudaAst + MExprAst
  syn TargetWrapperEnv =
  | CudaTargetEnv {
      -- Contains an expression for the size of the return expression, in
      -- number of elements.
      returnSize : CExpr,

      -- Contains a mapping from the gpu identifiers, which refer to pointers
      -- containing the data, to the identifiers containing the sequence
      -- structs that are to be passed to the CUDA kernel.
      seqVariables : Map Name Name,

      -- A reversed type environment, produced from type lifting, which allows
      -- looking up the name that a type has been replaced with.
      revTypeEnv : Map Type Name}

  sem getCudaCType =
  | TyInt _ | TyChar _ -> CTyInt64 ()
  | TyFloat _ -> CTyDouble ()
  | TySeq t -> CTyPtr {ty = getCudaCElementType (getCudaCType t.ty)}

  sem getCudaCElementType =
  | CTyPtr t -> getCudaCElementType t.ty
  | ty -> ty

  sem _allocSeqOnGpu (env : CWrapperEnv) (arg : ArgData) =
  | sizeExpr ->
    match env.targetEnv with CudaTargetEnv t in
    let gpuIdent = arg.gpuIdent in
    let intermId = nameSym "cuda_tmp" in
    let seqType =
      match mapLookup arg.ty t.revTypeEnv with Some seqId then
        CTyVar {id = seqId}
      else error (concat "Could not find sequence type for argument"
                         (nameGetStr arg.ident)) in
    let declIntermediateStmt = CSDef {
      ty = seqType,
      id = Some intermId,
      init = None ()} in
    let intermediateSetLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = intermId}, id = _seqLenKey},
      rhs = sizeExpr}} in
    let intermediateSetSeqStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = intermId}, id = _seqKey},
      rhs = CEVar {id = gpuIdent}}} in
    let cudaSeqId = nameSym "cuda_tmp" in
    let declSeqPtrStmt = CSDef {
      ty = CTyPtr {ty = seqType},
      id = Some cudaSeqId,
      init = None ()} in
    let seqPtrAllocStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaMalloc",
      args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = cudaSeqId}},
        CESizeOfType {ty = seqType}]}} in
    let seqPtrCopyStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaMemcpy",
      args = [
        CEVar {id = cudaSeqId},
        CEUnOp {op = COAddrOf (), arg = CEVar {id = intermId}},
        CESizeOfType {ty = seqType},
        CEVar {id = _getIdentExn "cudaMemcpyHostToDevice"}]}} in
    let env = {env with targetEnv =
      CudaTargetEnv {t with seqVariables = mapInsert gpuIdent cudaSeqId t.seqVariables}} in
    ( env
    , [ declIntermediateStmt, intermediateSetLenStmt, intermediateSetSeqStmt
      , declSeqPtrStmt, seqPtrAllocStmt, seqPtrCopyStmt ] )
end

lang CToCudaWrapper = CudaCWrapperBase
  sem _generateCToCudaWrapperInner (env : CWrapperEnv) (arg : ArgData) =
  | TyInt _ | TyChar _ | TyFloat _ ->
    let cvar : (Name, CType) = head arg.cTempVars in
    ({arg with gpuIdent = cvar.0}, [])
  | TySeq _ ->
    let cvars = arg.cTempVars in
    -- TODO(larshum, 2022-01-18): Add support for marshalling records.
    let cvar : (Name, CType) = head cvars in
    let elemType = getCudaCElementType cvar.1 in
    let numDims = length arg.dimIdents in
    let gpuIdent = nameSym "cuda_tmp" in
    let declStmt = CSDef {
      ty = cvar.1,
      id = Some gpuIdent,
      init = None ()} in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = arg.sizeIdent},
      rhs = CESizeOfType {ty = elemType}} in
    let allocStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaMalloc",
      args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = gpuIdent}},
        sizeExpr]}} in
    let copyStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaMemcpy",
      args = [
        CEVar {id = gpuIdent},
        CEVar {id = cvar.0},
        sizeExpr,
        CEVar {id = _getIdentExn "cudaMemcpyHostToDevice"}]}} in
    let arg = {arg with gpuIdent = gpuIdent} in
    match _allocSeqOnGpu env arg sizeExpr with (env, stmts) in
    let freeCTempStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "free", args = [CEVar {id = cvar.0}]}} in
    (env, arg, join [[declStmt, allocStmt, copyStmt], stmts, [freeCTempStmt]])

  sem _generateCToCudaWrapperArg (acc : (CWrapperEnv, [CStmt])) =
  | arg ->
    match acc with (env, accStmts) in
    let arg : ArgData = arg in
    match _generateCToCudaWrapperInner env arg arg.ty with (env, arg, stmts) in
    ((env, concat accStmts stmts), arg)

  sem generateCToTargetWrapper /- CWrapperEnv -> (CWrapperEnv, [CStmt]) -/ =
  | env ->
    let env : CWrapperEnv = env in
    match mapAccumL _generateCToCudaWrapperArg (env, []) env.arguments
    with ((env, cudaCopyStmts), args) in
    let env : CWrapperEnv = env in
    ({env with arguments = args}, cudaCopyStmts)
end

lang CudaCallWrapper = CudaCWrapperBase
  sem generateTargetCall /- CWrapperEnv -> (CWrapperEnv, [CStmt]) -/ =
  | env ->
    -- TODO(larshum, 2022-01-19): Compute the size of the output prior to
    -- running the wrapper, and set it during the initialization. For now, we
    -- hard-code the size to the size of the first argument (as we only support
    -- maps).
    let env : CWrapperEnv = env in
    match env.targetEnv with CudaTargetEnv tenv in
    let returnSize =
      let fstArg : ArgData = head env.arguments in
      CEVar {id = fstArg.sizeIdent} in
    let env = {env with targetEnv = CudaTargetEnv {tenv with returnSize = returnSize}} in

    let return : ArgData = env.return in
    let returnType = return.ty in

    -- Pre-allocate CUDA return value
    let elemTy = getCudaCElementType (getCudaCType returnType) in
    let cudaResultIdent = nameSym "cuda_out" in
    let cudaResultDeclStmt = CSDef {
      ty = getCudaCType returnType,
      id = Some cudaResultIdent,
      init = None ()} in
    let cudaResultAllocStmt =
      match returnType with TySeq _ then
        [CSExpr {expr = CEApp {
          fun = _getIdentExn "cudaMalloc",
          args = [
            CEUnOp {op = COAddrOf (), arg = CEVar {id = cudaResultIdent}},
            CEBinOp {
              op = COMul (),
              lhs = returnSize,
              rhs = CESizeOfType {ty = elemTy}}]}}]
      else [] in
    let return = {return with gpuIdent = cudaResultIdent} in
    match _allocSeqOnGpu env return returnSize with (env, gpuAllocStmts) in
    let env : CWrapperEnv = env in
    match env.targetEnv with CudaTargetEnv tenv in

    -- TODO(larshum, 2022-01-19): Assumes that the function identifier, and the
    -- identifier after prepending 'cuda_', are both globally unique.
    let functionStr =
      use MExprIdentifierPrettyPrint in
      match pprintVarName pprintEnvEmpty env.functionIdent with (_, id) in
      id in
    let funcStr = concat "cuda_" functionStr in

    -- Make call to CUDA kernel and synchronize
    -- int tpb = 512;
    let tpbId = nameSym "tpb" in
    let tpbDef = CSDef {
      ty = CTyInt64 (),
      id = Some tpbId,
      init = Some (CIExpr {expr = CEInt {i = 512}})} in
    -- int nblocks = (tpb + size - 1) / tpb;
    let nblocksId = nameSym "nblocks" in
    let nblocksDef = CSDef {
      ty = CTyInt64 (),
      id = Some nblocksId,
      init = Some (CIExpr {expr = CEBinOp {
        op = CODiv (),
        lhs = CEBinOp {
          op = COSub (),
          lhs = CEBinOp {
            op = COAdd (),
            lhs = returnSize,
            rhs = CEVar {id = tpbId}},
          rhs = CEInt {i = 1}},
        rhs = CEVar {id = tpbId}}})} in
    let args =
      map
        (lam arg : ArgData.
          match arg.ty with TySeq _ then
            -- NOTE(larshum, 2022-01-19): For sequences, we use the allocated
            -- sequence struct instead of the data pointer.
            match mapLookup arg.gpuIdent tenv.seqVariables with Some seqId then
              CEVar {id = seqId}
            else error "Sequence identifier without allocated sequence struct"
          else CEUnOp {op = CODeref (), arg = CEVar {id = arg.gpuIdent}})
        (cons return env.arguments) in
    let i1 = CEInt {i = 1} in
    let cudaCallStmt =
      CSExpr {expr = CEKernelApp {
        fun = funcStr,
        gridSize = CEVar {id = nblocksId},
        blockSize = CEVar {id = tpbId},
        args = args}} in
    let cudaSyncStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaDeviceSynchronize", args = []}} in
    
    -- TODO(larshum, 2022-01-18): Add code for catching and printing errors
    -- from CUDA.

    -- Free CUDA input values.
    let freeSeqVarStmts =
      map
        (lam seqVarId : Name.
          CSExpr {expr = CEApp {
            fun = _getIdentExn "cudaFree",
            args = [CEVar {id = seqVarId}]}})
        (mapValues tenv.seqVariables) in
    let freeArgStmts =
      join
        (map
          (lam arg : ArgData.
            match arg.ty with TySeq _ then
              [CSExpr {expr = CEApp {
                fun = _getIdentExn "cudaFree",
                args = [CEVar {id = arg.gpuIdent}]}}]
            else [])
          env.arguments) in
    
    let stmts =
      join [
        [cudaResultDeclStmt],
        cudaResultAllocStmt,
        gpuAllocStmts,
        [tpbDef, nblocksDef, cudaCallStmt, cudaSyncStmt],
        freeSeqVarStmts, freeArgStmts] in
    ({env with return = return}, stmts)
end

lang CudaToCWrapper = CudaCWrapperBase
  sem _generateCudaToCWrapperInner (cudaEnv : TargetEnv) (return : ArgData) =
  | ty & (TyInt _ | TyChar _ | TyFloat _) ->
    -- NOTE(larshum, 2022-01-19): The function below may result in a type
    -- variable containing the name for 'int64_t', which is kind of
    -- inconsistent in a CUDA AST which also includes this as a dedicated type
    -- in the AST. But for now, we have no easy way of overloading its
    -- definition (it is defined in PMExpr, where we should not depend on the
    -- CUDA AST).
    let ctype = head (mexprToCTypes ty) in
    let cIdent = return.gpuIdent in
    let return = {return with cTempVars = [(cIdent, ctype)]} in
    (return, [])
  | ty & (TySeq _) ->
    match cudaEnv with CudaTargetEnv cudaEnv in
    let ctype = head (mexprToCTypes ty) in
    let cIdent = nameSym "c_tmp" in

    -- TODO(larshum, 2022-01-19): Support result with more than one dimension.
    let sizeIdent = nameSym "n" in
    let sizeInitStmt = CSDef {
      ty = CTyInt64 (), id = Some sizeIdent,
      init = Some (CIExpr {expr = cudaEnv.returnSize})} in
    let dimIdents = [sizeIdent] in

    -- Preallocate C memory
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = sizeIdent},
      rhs = CESizeOfType {ty = ctype}} in
    let preallocStmt = CSDef {
      ty = ctype,
      id = Some cIdent,
      init = Some (CIExpr {expr = CECast {
        ty = ctype,
        rhs = CEApp {
          fun = _getIdentExn "malloc",
          args = [sizeExpr]}}})} in

    -- Copy from CUDA to C
    let copyCudaToCStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaMemcpy",
      args = [
        CEVar {id = cIdent},
        CEVar {id = return.gpuIdent},
        sizeExpr,
        CEVar {id = _getIdentExn "cudaMemcpyDeviceToHost"}]}} in

    -- Free CUDA memory
    let freeCudaStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaFree",
      args = [CEVar {id = return.gpuIdent}]}} in

    let return = {{{return with cTempVars = [(cIdent, ctype)]}
                           with dimIdents = dimIdents}
                           with sizeIdent = sizeIdent} in
    (return, [sizeInitStmt, preallocStmt, copyCudaToCStmt, freeCudaStmt])

  sem generateTargetToCWrapper /- : CWrapperEnv -> (CWrapperEnv, [CStmt]) -/ =
  | env ->
    let env : CWrapperEnv = env in
    match _generateCudaToCWrapperInner env.targetEnv env.return env.return.ty
    with (return, copyStmts) in
    ({env with return = return}, copyStmts)
end

lang CudaCWrapper = CToCudaWrapper + CudaCallWrapper + CudaToCWrapper + Cmp
  -- Generates the initial wrapper environment
  sem generateInitWrapperEnv =
  | typeEnv /- : [(Name, Type)] -/ ->
    let revTypeEnv =
      mapFromSeq cmpType
        (map
          (lam nt : (Name, Type).
            match nt with (id, ty) in
            (ty, id))
          typeEnv) in
    let targetEnv = CudaTargetEnv {
      returnSize = CEInt {i = 0},
      seqVariables = mapEmpty nameCmp,
      revTypeEnv = revTypeEnv} in
    let env : CWrapperEnv = _emptyWrapperEnv () in
    {env with targetEnv = targetEnv}

  -- Defines the target-specific generation of wrapper code.
  sem generateWrapperCode (accelerated : Map Name AccelerateData) =
  | typeEnv /- : [(Name, Type)] -/ ->
    let env = generateInitWrapperEnv typeEnv in
    match generateWrapperCodeH env accelerated with (env, entryPointWrappers) in
    CuPProg {
      includes = [
        "<stddef.h>",
        "<stdlib.h>",
        "<stdio.h>",
        "\"caml/alloc.h\"",
        "\"caml/memory.h\"",
        "\"caml/mlvalues.h\""
      ],
      tops =
        map
          (lam top : CTop. CuTTop {attrs = [CuAExternC ()], top = top})
          entryPointWrappers}
end
