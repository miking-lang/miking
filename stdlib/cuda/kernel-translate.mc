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
include "cuda/intrinsics/loop-foldl.mc"
include "cuda/intrinsics/map-kernel.mc"
include "cuda/intrinsics/map.mc"
include "cuda/intrinsics/tensor-slice.mc"
include "cuda/intrinsics/tensor-sub.mc"

-- Translates non-kernel intrinsics, which could run either in CPU or GPU code,
-- to looping constructs.
lang CudaCpuTranslate =
  CudaMapIntrinsic + CudaFoldlIntrinsic + CudaTensorSliceIntrinsic +
  CudaTensorSubIntrinsic + CudaLoopIntrinsic + CudaLoopFoldlIntrinsic

  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | (CESeqFoldl _ | CETensorSliceExn _ | CETensorSubExn _ | CESeqLoopFoldl _) & t ->
    generateCudaIntrinsicCall ccEnv acc outExpr t

  sem generateIntrinsicExprNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | (CESeqLoop _) & t ->
    generateCudaIntrinsicCallNoRet ccEnv acc t
end

-- Translates kernel expressions to GPU kernel calls.
lang CudaGpuTranslate =
  CudaMapKernelIntrinsic + CudaLoopKernelIntrinsic

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
  sem translateCudaTops (accelerateData : Map Name AccelerateData)
                        (ccEnv : CompileCEnv) =
  | tops ->
    let tops = map translateTopToCudaFormat tops in
    let wrapperMap =
      mapMapWithKey (lam key. lam. nameSym "cuda_wrap") accelerateData in
    (wrapperMap, generateIntrinsics wrapperMap ccEnv tops)

  sem generateIntrinsics (wrapperMap : Map Name Name)
                         (ccEnv : CompileCEnv) =
  | tops -> join (map (generateIntrinsicsTop wrapperMap ccEnv) tops)

  sem generateIntrinsicsTop (wrapperMap : Map Name Name)
                            (ccEnv : CompileCEnv) =
  | CuTTop (cuTop & {top = CTFun t}) ->
    match mapAccumL (generateIntrinsicStmt ccEnv t.ret) [] t.body with (tops, body) in
    match mapLookup t.id wrapperMap with Some cudaWrapperId then
      let newTop = CTFun {{t with id = cudaWrapperId}
                             with body = body} in
      let cudaTop = CuTTop {{cuTop with attrs = []} with top = newTop} in
      snoc tops cudaTop
    else
      -- NOTE(larshum, 2022-03-16): Functions that contain a kernel call must
      -- not be defined on the device (GPU). We give them an explicit host
      -- attribute to be able to distinguish them from wrapper functions (the
      -- host attribute is implicit if no other attributes are added).
      let attrs =
        if containsKernelCall body then [CuAHost ()]
        else [CuAHost (), CuADevice ()] in
      let cudaTop = CuTTop {{cuTop with attrs = attrs}
                                   with top = CTFun {t with body = body}} in
      snoc tops cudaTop
  | t -> [t]

  sem containsKernelCall =
  | stmts -> foldl containsKernelCallH false stmts

  sem containsKernelCallH (acc : Bool) =
  | CSExpr {expr = CEKernelApp _} -> true
  | CSComp {stmts = stmts} ->
    if acc then acc else foldl containsKernelCallH acc stmts
  | stmt -> acc

  sem generateIntrinsicStmt (ccEnv : CompileCEnv) (ty : CType) (acc : [CuTop]) =
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
  | stmt -> (acc, stmt)

  -- Generates an statement for the contained intrinsic, which potentially
  -- replaces the original assignment statement.
  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | t -> (acc, CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}})

  -- As above, but for intrinsics that do not return values.
  sem generateIntrinsicExprNoRet (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | t -> (acc, CSExpr {expr = t})

  -- Wraps the C top-level terms in the CUDA version of a top-level term, which
  -- includes a sequence of attributes that can be attached.
  sem translateTopToCudaFormat =
  | CTTyDef t -> CuTTop {attrs = [], top = CTTyDef t}
  | CTDef t -> CuTTop {attrs = [CuAHost (), CuADevice ()], top = CTDef t}
  | CTFun t -> CuTTop {attrs = [], top = CTFun t}
end
