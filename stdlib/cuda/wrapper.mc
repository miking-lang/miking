include "c/compile.mc"
include "cuda/ast.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "pmexpr/wrapper.mc"

lang CudaCWrapperBase = PMExprCWrapper + CudaAst + MExprAst + MExprCCompile
  syn TargetWrapperEnv =
  | CudaTargetEnv {
      -- Provides a mapping from the name of the C wrapper function to a CUDA
      -- wrapper function which handles interaction with CUDA kernels. Note
      -- that the name of the C wrapper function must be globally unique as it
      -- will be called from the OCaml code, while that of the CUDA wrapper
      -- does not, since it is called from a function stored in the same file.
      wrapperMap : Map Name Name,
      
      -- Reversed type environment from type lifting. Enables looking up the
      -- name of the replacement of a lifted type.
      revTypeEnv : Map Type Name,

      -- C compiler environment, used to compile MExpr types to the C
      -- equivalents.
      compileCEnv : CompileCEnv}

  sem getCudaType (env : TargetWrapperEnv) =
  | TySeq t ->
    match env with CudaTargetEnv cenv in
    match mapLookup (TySeq t) cenv.revTypeEnv with Some seqId then
      CTyVar {id = seqId}
    else error ""
  | ty ->
    match env with CudaTargetEnv cenv in
    compileType cenv.compileCEnv ty
end

-- Translate the general C representation to one that is specific to CUDA. This
-- includes wrapping sequences in structs containing their length.
lang CToCudaWrapper = CudaCWrapperBase
  sem _generateCToCudaWrapperInner (env : CWrapperEnv) (argument : ArgData) =
  | TyInt _ | TyChar _ | TyFloat _ ->
    let cvar : (Name, CType) = head argument.cTempVars in
    ({argument with gpuIdent = cvar.0}, [])
  | ty & TySeq _ ->
    match env.targetEnv with CudaTargetEnv cenv in
    let cvars = argument.cTempVars in
    let cvar : (Name, CType) = head cvars in
    let cudaType = getCudaType env.targetEnv ty in
    let gpuIdent = nameSym "cuda_tmp" in
    let declStmt = CSDef {ty = cudaType, id = Some gpuIdent, init = None ()} in
    -- TODO(larshum, 2022-02-08): Support multi-dimensional sequences.
    let setLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _seqLenKey},
      rhs = CEVar {id = argument.sizeIdent}}} in
    let setSeqStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _seqKey},
      rhs = CEVar {id = cvar.0}}} in
    ({argument with gpuIdent = gpuIdent}, [declStmt, setLenStmt, setSeqStmt])

  sem generateCToCudaWrapperArg (env : CWrapperEnv) (accStmts : [CStmt]) =
  | arg ->
    let arg : ArgData = arg in
    match _generateCToCudaWrapperInner env arg arg.ty with (arg, stmts) in
    (concat accStmts stmts, arg)

  sem generateCToCudaWrapper =
  | env ->
    let env : CWrapperEnv = env in
    match mapAccumL (generateCToCudaWrapperArg env) [] env.arguments
    with (cudaCopyStmts, args) in
    ({env with arguments = args}, cudaCopyStmts)
end

lang CudaCallWrapper = CudaCWrapperBase
  sem generateCudaWrapperCall =
  | env ->
    let env : CWrapperEnv = env in
    match env.targetEnv with CudaTargetEnv tenv in

    -- Declare pointer to return value
    let return : ArgData = env.return in
    let returnType = return.ty in
    let cudaType = getCudaType env.targetEnv returnType in
    let cudaResultIdent = nameSym "cuda_out" in
    let returnDecl = CSDef {
      ty = cudaType, id = Some cudaResultIdent, init = None ()} in

    let cudaWrapperId =
      match mapLookup env.functionIdent tenv.wrapperMap with Some id then id
      else error "Internal compiler error: No function defined for wrapper map" in
    let args : [CExpr] =
      map
        (lam arg : ArgData.
          let var = CEVar {id = arg.gpuIdent} in
          match arg.ty with TySeq _ then var
          else CEUnOp {op = CODeref (), arg = var}) env.arguments in
    let cudaWrapperCallStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = cudaResultIdent},
      rhs = CEApp {fun = cudaWrapperId, args = args}}} in

    -- Deallocate argument parameters
    let deallocStmts =
      join (map
        (lam arg : ArgData.
          match arg.ty with TySeq _ then
            let cvar : (Name, CType) = head arg.cTempVars in
            [CSExpr {expr = CEApp {fun = _getIdentExn "free",
                                   args = [CEVar {id = cvar.0}]}}]
          else []) env.arguments) in

    let return = {return with gpuIdent = cudaResultIdent} in

    let stmts = concat [returnDecl, cudaWrapperCallStmt] deallocStmts in
    ({env with return = return}, stmts)
end

lang CudaToCWrapper = CudaCWrapperBase
  sem _generateCudaToCWrapperInner (env : CWrapperEnv) (return : ArgData) =
  | ty & (TyInt _ | TyChar _ | TyFloat _) ->
    match env.targetEnv with CudaTargetEnv tenv in
    let ctype = getCudaType env.targetEnv ty in
    let cIdent = return.gpuIdent in
    let return = {return with cTempVars = [(cIdent, ctype)]} in 
    (return, [])
  | ty & TySeq _ ->
    let fieldAccess = lam key.
      CEMember {lhs = CEVar {id = return.gpuIdent}, id = key} in
    match env.targetEnv with CudaTargetEnv tenv in
    let ctype = head (mexprToCTypes ty) in
    let cIdent = nameSym "c_tmp" in
    let sizeIdent = nameSym "d" in
    let getLenStmt =
      CSDef {
        ty = CTyInt64 (), id = Some sizeIdent,
        init = Some (CIExpr {expr = fieldAccess _seqLenKey})} in
    let getSeqStmt =
      CSDef {
        ty = ctype, id = Some cIdent,
        init = Some (CIExpr {expr = fieldAccess _seqKey})} in

    let return = {{{return with cTempVars = [(cIdent, ctype)]}
                           with dimIdents = [sizeIdent]}
                           with sizeIdent = sizeIdent} in
    (return, [getLenStmt, getSeqStmt])

  sem generateCudaToCWrapper =
  | env ->
    let env : CWrapperEnv = env in
    match _generateCudaToCWrapperInner env env.return env.return.ty
    with (return, copyStmts) in
    ({env with return = return}, copyStmts)
end

lang CudaCWrapper = CToCudaWrapper + CudaCallWrapper + CudaToCWrapper + Cmp
  -- Generates the initial wrapper environment
  sem generateInitWrapperEnv (wrapperMap : Map Name Name) =
  | compileCEnv ->
    let compileCEnv : CompileCEnv = compileCEnv in
    let tupleSwap = lam t : (a, b). match t with (x, y) in (y, x) in
    let revTypeEnv = mapFromSeq cmpType (map tupleSwap compileCEnv.typeEnv) in
    let targetEnv = CudaTargetEnv {
      wrapperMap = wrapperMap, compileCEnv = compileCEnv,
      revTypeEnv = revTypeEnv} in
    let env : CWrapperEnv = _emptyWrapperEnv () in
    {env with targetEnv = targetEnv}

  sem generateMarshallingCode =
  | env ->
    match generateOCamlToCWrapper env with (env, stmt1) in
    match generateCToCudaWrapper env with (env, stmt2) in
    match generateCudaWrapperCall env with (env, stmt3) in
    match generateCudaToCWrapper env with (env, stmt4) in
    match generateCToOCamlWrapper env with (env, stmt5) in
    (env, join [stmt1, stmt2, stmt3, stmt4, stmt5])

  -- Defines the target-specific generation of wrapper code.
  sem generateWrapperCode (accelerated : Map Name AccelerateData)
                          (wrapperMap : Map Name Name) =
  | compileCEnv ->
    let env = generateInitWrapperEnv wrapperMap compileCEnv in
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
          (lam top : CTop. CuTTop {templates = [], attrs = [CuAExternC ()], top = top})
          entryPointWrappers}
end
