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
include "cuda/intrinsics/loop-kernel.mc"
include "cuda/intrinsics/loop.mc"
include "cuda/intrinsics/map-kernel.mc"
include "cuda/intrinsics/map.mc"
include "cuda/intrinsics/tensor-slice.mc"
include "cuda/intrinsics/tensor-sub.mc"

-- Translates non-kernel intrinsics, which could run either in CPU or GPU code,
-- to looping constructs.
lang CudaCpuTranslate =
  CudaMapIntrinsic + CudaFoldlIntrinsic + CudaTensorSliceIntrinsic +
  CudaTensorSubIntrinsic + CudaLoopIntrinsic

  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | (CESeqMap _ | CESeqFoldl _ | CETensorSliceExn _ | CETensorSubExn _) & t ->
    generateCudaIntrinsicCall ccEnv acc outExpr t

  sem generateIntrinsicExprNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | (CESeqLoop _) & t ->
    generateCudaIntrinsicCallNoRet ccEnv acc t
end

-- Translates kernel expressions to GPU kernel calls.
lang CudaGpuTranslate =
  CudaMapKernelIntrinsic + CudaLoopKernelIntrinsic

  -- NOTE(larshum, 2022-02-08): We assume that the expression for the function
  -- f is a variable containing an identifier. This will not work for closures
  -- or for functions that take additional variables, including those that
  -- capture variables (due to lambda lifting).
  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | (CEMapKernel _) & t ->
    match generateCudaKernelCall ccEnv outExpr t with (kernelTop, kernelCall) in
    let acc = cons kernelTop acc in
    (acc, kernelCall)

  sem generateIntrinsicExprNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | (CELoopKernel _) & t ->
    match generateCudaKernelCallNoRet ccEnv t with (kernelTop, kernelCall) in
    let acc = cons kernelTop acc in
    (acc, kernelCall)
end

lang CudaKernelTranslate = CudaPMExprCompile + CudaCpuTranslate + CudaGpuTranslate
  sem translateCudaTops (accelerateData : Map Name AccelerateData)
                        (marked : Set Name)
                        (ccEnv : CompileCEnv) =
  | tops -> generateIntrinsics accelerateData marked ccEnv tops

  sem generateIntrinsics (accelerateData : Map Name AccelerateData)
                         (marked : Set Name)
                         (ccEnv : CompileCEnv) =
  | tops ->
    let wrapperMap : Map Name Name =
      mapMapWithKey (lam key. lam. nameSym "cuda_wrap") accelerateData in
    let tops = map (generateIntrinsicsTop wrapperMap marked ccEnv) tops in
    (wrapperMap, join tops)

  sem generateIntrinsicsTop (wrapperMap : Map Name Name)
                            (marked : Set Name)
                            (ccEnv : CompileCEnv) =
  | CuTTop (cuTop & {top = CTFun t}) ->
    match mapAccumL (generateIntrinsicStmt ccEnv) [] t.body with (tops, body) in
    match mapLookup t.id wrapperMap with Some cudaWrapperId then
      let newTop = CTFun {{t with id = cudaWrapperId}
                             with body = body} in
      let cudaTop = CuTTop {{cuTop with attrs = []} with top = newTop} in
      snoc tops cudaTop
    else
      -- NOTE(larshum, 2022-03-16): Functions that were marked contain no
      -- kernel calls, so they can run on either CPU (host) or GPU (device).
      -- Functions containing kernel calls must run on the host, so we
      -- explicitly annotate them that way to distinguish them from wrapper
      -- functions (annotating only with host is equivalent to no annotation,
      -- but we use the annotation to distinguish between them).
      let attrs =
        if setMem t.id marked then [CuAHost (), CuADevice ()]
        else [CuAHost ()] in
      let cudaTop = CuTTop {{cuTop with attrs = attrs}
                                   with top = CTFun {t with body = body}} in
      snoc tops cudaTop
  | t -> [t]

  sem generateIntrinsicStmt (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | CSExpr {expr = t} ->
    generateIntrinsicExprNoRet ccEnv acc t
  | CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}} ->
    generateIntrinsicExpr ccEnv acc outExpr t
  | stmt -> (acc, stmt)

  -- Generates an statement for the contained intrinsic, which potentially
  -- replaces the original assignment statement.
  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | t -> (acc, CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}})

  -- As above, but for intrinsics that do not return values.
  sem generateIntrinsicExprNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | t -> (acc, CSExpr {expr = t})
end
