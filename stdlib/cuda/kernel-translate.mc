-- Translates C top-level definitions to the CUDA specific representation of
-- tops. This includes the addition of CUDA attributes, and providing distinct
-- names for the CUDA wrapper functions, which handle interaction with CUDA
-- kernels. It also involves updating GPU variables to be pointers, rather than
-- being allocated on the (CPU) stack.

include "name.mc"
include "set.mc"
include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/compile.mc"
include "cuda/pmexpr-compile.mc"
include "cuda/intrinsics/foldl.mc"
include "cuda/intrinsics/loop-acc.mc"
include "cuda/intrinsics/loop-kernel.mc"
include "cuda/intrinsics/loop.mc"
include "cuda/intrinsics/tensor-slice.mc"
include "cuda/intrinsics/tensor-sub.mc"

-- Translates non-kernel intrinsics, which could run either in CPU or GPU code,
-- to looping constructs.
lang CudaCpuTranslate =
  CudaFoldlIntrinsic + CudaTensorSliceIntrinsic + CudaTensorSubIntrinsic +
  CudaLoopIntrinsic + CudaLoopAccIntrinsic

  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | (CESeqFoldl _ | CETensorSliceExn _ | CETensorSubExn _ | CESeqLoopAcc _) & t ->
    generateCudaIntrinsicCall ccEnv acc outExpr t

  sem generateIntrinsicExprNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | (CESeqLoop _) & t ->
    generateCudaIntrinsicCallNoRet ccEnv acc t
end

-- Translates kernel expressions to GPU kernel calls.
lang CudaGpuTranslate =
  CudaLoopKernelIntrinsic

  -- NOTE(larshum, 2022-03-22): At the moment, no kernels returning a value are
  -- supported.
  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  /-| t ->
    match generateCudaKernelCall ccEnv outExpr t with (kernelTop, kernelCall) in
    let acc = cons kernelTop acc in
    (acc, kernelCall)-/

  sem generateIntrinsicExprNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | (CELoopKernel _) & t ->
    match generateCudaKernelCallNoRet ccEnv t with (kernelTop, kernelCall) in
    let acc = cons kernelTop acc in
    (acc, kernelCall)
end

lang CudaKernelTranslate = CudaPMExprCompile + CudaCpuTranslate + CudaGpuTranslate
  sem generateIntrinsics : Map Name Name -> CompileCEnv -> [CTop] -> [CuTop]
  sem generateIntrinsics wrapperMap ccEnv =
  | tops -> join (map (generateIntrinsicsTop wrapperMap ccEnv) tops)

  sem generateIntrinsicsTop : Map Name Name -> CompileCEnv -> CuTop -> [CuTop]
  sem generateIntrinsicsTop wrapperMap ccEnv =
  | CuTTop (cuTop & {top = CTFun t}) ->
    match mapAccumL (generateIntrinsicStmt ccEnv t.ret) [] t.body with (tops, body) in
    let cudaTop =
      match mapLookup t.id wrapperMap with Some cudaWrapperId then
        let newTop = CTFun {{t with id = cudaWrapperId}
                               with body = body} in
        CuTTop {cuTop with top = newTop}
      else CuTTop {cuTop with top = CTFun {t with body = body}}
    in
    snoc tops cudaTop
  | t -> [t]

  sem generateIntrinsicStmt : CompileCEnv -> CType -> [CuTop] -> CStmt
                           -> ([CuTop], CStmt)
  sem generateIntrinsicStmt ccEnv ty acc =
  | CSExpr {expr = t} ->
    generateIntrinsicExprNoRet ccEnv acc t
  | CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}} ->
    generateIntrinsicExpr ccEnv acc outExpr t
  | CSRet {val = Some t} ->
    let tempId = nameSym "t" in
    let temp = CEVar {id = tempId} in
    let tempDecl = CSDef {ty = ty, id = Some tempId, init = None ()} in
    match generateIntrinsicExpr ccEnv acc temp t with (acc, stmt) in
    let tempReturn = CSRet {val = Some temp} in
    (acc, CSComp {stmts = [tempDecl, stmt, tempReturn]})
  | stmt -> smapAccumLCStmtCStmt (generateIntrinsicStmt ccEnv ty) acc stmt

  -- Generates an statement for the contained intrinsic, which potentially
  -- replaces the original assignment statement.
  sem generateIntrinsicExpr : CompileCEnv -> [CuTop] -> CExpr -> CStmt
                           -> ([CuTop], CStmt)
  sem generateIntrinsicExpr ccEnv acc outExpr =
  | t -> (acc, CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}})

  -- As above, but for intrinsics that do not return values.
  sem generateIntrinsicExprNoRet : CompileCEnv -> [CuTop] -> CStmt
                                -> ([CuTop], CStmt)
  sem generateIntrinsicExprNoRet ccEnv acc =
  | t -> (acc, CSExpr {expr = t})

  sem translateCTopsToCuda : FunctionEnv -> [CTop] -> [CuTop]
  sem translateCTopsToCuda functionEnv =
  | tops -> map (translateCTopToCuda functionEnv) tops

  -- Wraps the C top-level terms in the CUDA version of a top-level term, which
  -- includes a sequence of attributes that can be attached.
  sem translateCTopToCuda : FunctionEnv -> CTop -> CuTop
  sem translateCTopToCuda env =
  | CTFun t ->
    let attrs = getCudaFunctionAttributes t.id env in
    CuTTop {attrs = attrs, top = CTFun t}
  | top -> CuTTop {attrs = [], top = top}

  sem getCudaFunctionAttributes : Name -> FunctionEnv -> [CudaAttribute]
  sem getCudaFunctionAttributes id =
  | env ->
    match mapLookup id env with Some units then
      match units with Cpu _ then [CuAHost ()]
      else match units with Gpu _ then [CuADevice ()]
      else match units with Both _ then [CuAHost (), CuADevice ()]
      else []
    else [CuAHost (), CuADevice ()]

  sem translateCudaTops : FunctionEnv -> Map Name AccelerateData -> CompileCEnv
                       -> [CTop] -> (Map Name Name, [CuTop])
  sem translateCudaTops functionEnv accelerateData ccEnv =
  | tops ->
    let tops = translateCTopsToCuda functionEnv tops in
    let wrapperMap =
      mapMapWithKey (lam. lam. nameSym "cuda_wrap") accelerateData in
    (wrapperMap, generateIntrinsics wrapperMap ccEnv tops)
end
