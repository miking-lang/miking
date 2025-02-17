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
include "pmexpr/extract.mc"

lang CudaTranslate = CudaAst
  sem generateIntrinsicExpr : CompileCEnv -> [CuTop] -> CExpr -> CExpr
                           -> ([CuTop], CStmt)

  sem generateIntrinsicExprNoRet : CompileCEnv -> [CuTop] -> CExpr
                                -> ([CuTop], CStmt)
end

-- Translates non-kernel intrinsics, which could run either in CPU or GPU code,
-- to looping constructs.
lang CudaCpuTranslate =
  CudaTranslate + CudaFoldlIntrinsic + CudaTensorSliceIntrinsic +
  CudaTensorSubIntrinsic + CudaLoopIntrinsic + CudaLoopAccIntrinsic

  sem generateIntrinsicExpr : CompileCEnv -> [CuTop] -> CExpr -> CExpr
                           -> ([CuTop], CStmt)
  sem generateIntrinsicExpr ccEnv acc outExpr =
  | (CESeqFoldl _ | CETensorSliceExn _ | CETensorSubExn _ | CESeqLoopAcc _) & t ->
    generateCudaIntrinsicCall ccEnv acc outExpr t

  sem generateIntrinsicExprNoRet : CompileCEnv -> [CuTop] -> CExpr
                                -> ([CuTop], CStmt)
  sem generateIntrinsicExprNoRet ccEnv acc =
  | (CESeqLoop _) & t ->
    generateCudaIntrinsicCallNoRet ccEnv acc t
end

-- Translates kernel expressions to GPU kernel calls.
lang CudaGpuTranslate =
  CudaTranslate + CudaLoopKernelIntrinsic

  -- NOTE(larshum, 2022-03-22): At the moment, no kernels returning a value are
  -- supported.
  sem generateIntrinsicExpr : CompileCEnv -> [CuTop] -> CExpr -> CExpr
                           -> ([CuTop], CStmt)
  /-| t ->
    match generateCudaKernelCall ccEnv outExpr t with (kernelTop, kernelCall) in
    let acc = cons kernelTop acc in
    (acc, kernelCall)-/

  sem generateIntrinsicExprNoRet : CompileCEnv -> [CuTop] -> CExpr -> ([CuTop], CStmt)
  sem generateIntrinsicExprNoRet ccEnv acc =
  | (CELoopKernel _) & t ->
    match generateCudaKernelCallNoRet ccEnv t with (kernelTop, kernelCall) in
    let acc = cons kernelTop acc in
    (acc, kernelCall)
end

lang CudaKernelTranslate = CudaPMExprCompile + CudaCpuTranslate +
                           CudaGpuTranslate + PMExprExtractAccelerate

  sem translateCudaTops : Map Name AccelerateData -> CompileCEnv -> [CTop]
                       -> (Map Name Name, [CuTop])
  sem translateCudaTops accelerateData ccEnv =
  | tops ->
    let tops = map translateTopToCudaFormat tops in
    let wrapperMap =
      mapMapWithKey (lam key. lam. nameSym "cuda_wrap") accelerateData in
    (wrapperMap, generateIntrinsics wrapperMap ccEnv tops)

  sem generateIntrinsics : Map Name Name -> CompileCEnv -> [CuTop] -> [CuTop]
  sem generateIntrinsics wrapperMap ccEnv =
  | tops -> join (map (generateIntrinsicsTop wrapperMap ccEnv) tops)

  sem generateIntrinsicsTop : Map Name Name -> CompileCEnv -> CuTop -> [CuTop]
  sem generateIntrinsicsTop wrapperMap ccEnv =
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

  sem containsKernelCall : [CStmt] -> Bool
  sem containsKernelCall =
  | stmts -> foldl containsKernelCallH false stmts

  sem containsKernelCallH : Bool -> CStmt -> Bool
  sem containsKernelCallH acc =
  | CSExpr {expr = CEKernelApp _} -> true
  | stmt -> sfold_CStmt_CStmt containsKernelCallH acc stmt

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
  sem generateIntrinsicExpr : CompileCEnv -> [CuTop] -> CExpr -> CExpr
                           -> ([CuTop], CStmt)
  sem generateIntrinsicExpr ccEnv acc outExpr =
  | t -> (acc, CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}})

  -- As above, but for intrinsics that do not return values.
  sem generateIntrinsicExprNoRet : CompileCEnv -> [CuTop] -> CExpr
                                -> ([CuTop], CStmt)
  sem generateIntrinsicExprNoRet ccEnv acc =
  | t -> (acc, CSExpr {expr = t})

  -- Wraps the C top-level terms in the CUDA version of a top-level term, which
  -- includes a sequence of attributes that can be attached.
  sem translateTopToCudaFormat : CTop -> CuTop
  sem translateTopToCudaFormat =
  | top -> CuTTop {attrs = [], top = top}
end
