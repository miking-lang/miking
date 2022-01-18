include "cuda/ast.mc"
include "pmexpr/wrapper.mc"

lang CudaCWrapperBase = PMExprCWrapper + CudaAst
end

lang CToCudaWrapper = CudaCWrapperBase
  sem _generateCToCudaWrapperInner (arg : ArgData) =
  | TyInt _ | TyChar _ | TyFloat _ ->
    let cvar : (Name, CType) = head arg.cTempVars in
    ({arg with gpuIdent = cvar.0}, [])
  | TySeq _ ->
    let cvars = arg.cTempVars in
    -- TODO(larshum, 2022-01-18): Add support for marshalling records.
    let cvar : (Name, CType) = head cvars in


  sem _generatecToCudaWrapperArg (accStmts : [CStmt]) =
  | arg ->
    let arg : ArgData = arg in
    match _generateCToCudaWrapperInner arg arg.ty with (arg, stmts) in
    (concat accStmts stmts, arg)

  sem generateCToTargetWrapper /- CWrapperEnv -> (CWrapperEnv, [CStmt]) -/ =
  | env ->
    let env : CWrapperEnv = env in
    match mapAccumL _generateCToCudaWrapperArg [] env.arguments
    with (cudaCopyStmts, args) in
    ({env with arguments = args}, cudaCopyStmts)
end

lang CudaCallWrapper = CudaCWrapperBase
  sem generateTargetCall /- CWrapperEnv -> (CWrapperEnv, [CStmt]) -/ =
  | env ->
    let env : CWrapperEnv = env in
    let return = env.return in
    let returnType = return.ty in

    -- Define return size and store in variable
    

    -- Declare and allocate CUDA return value
    let cudaResultStmt = CSDef {
      
    } in

    -- Call CUDA kernel and synchronize afterwards
    let args =
      map
        (lam arg : ArgData.
          match arg.ty with TySeq _ then
            CEVar {id = arg.gpuIdent}
          else CEUnOp {op = CODeref (), arg = CEVar {id = arg.gpuIdent}})
        env.arguments in
    let i1 = CEInt {i = 1} in
    let cudaCallStmt =
      CSExpr {expr = CEKernelApp {
        fun = env.functionIdent,
        gridSize = (, i1, i1),
        blockSize = (i1, i1, i1),
        sharedMem = CEInt {i = 0},
        args = args}} in
    let cudaSyncStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "cudaDeviceSynchronize", args = []}} in
    
    -- TODO(larshum, 2022-01-18): Add code for catching and printing errors
    -- from CUDA.

    -- Free CUDA input values.
    let freeStmts =
      join
        (map
          (lam arg : ArgData.
            match arg.ty with TySeq _ then
              [CSExpr {expr = CEApp {
                fun = _getIdentExn "cudaFree", args = [arg.gpuIdent]}}]
            else [])
          env.arguments) in
    
    let return = {return with gpuIdent = futResultIdent} in
    let stmts =
      concat
        [cudaCallStmt, cudaSyncStmt]
        freeStmts in
    ({env with return = return}, stmts)
end

lang CudaToCWrapper = CudaCWrapperBase
  sem generateTargetToCWrapper /- : CWrapperEnv -> (CWrapperEnv, [CStmt]) -/ =
end

lang CudaCWrapper = CToCudaWrapper + CudaCallWrapper + CudaToCWrapper
  -- Generates the initial wrapper
  sem generateInitWrapperEnv =

  -- Defines the target-specific generation of wrapper code.
  sem generateWrapperCode =
end
