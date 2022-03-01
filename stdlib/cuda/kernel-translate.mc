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
include "cuda/memory.mc"
include "cuda/intrinsics/foldl.mc"
include "cuda/kernels/map.mc"

-- Translates non-kernel intrinsics, which could run either in CPU or GPU code,
-- to looping constructs.
lang CudaCpuTranslate =
  CudaAst + MExprCCompile + CudaFoldlIntrinsic

  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | t & (CEFoldl _) -> generateCudaIntrinsicCall acc outExpr t
end

-- Translates kernel expressions to GPU kernel calls.
lang CudaGpuTranslate =
  CudaAst + CudaMemoryManagement + CudaMapKernel + MExprCCompile

  -- NOTE(larshum, 2022-02-08): We assume that the expression for the function
  -- f is a variable containing an identifier. This will not work for closures
  -- or for functions that take additional variables, including those that
  -- capture variables (due to lambda lifting).
  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | t & (CEMapKernel _) ->
    match generateCudaKernelCall ccEnv outExpr t with (kernelTop, kernelCall) in
    let acc = cons kernelTop acc in
    (acc, kernelCall)
end

lang CudaKernelTranslate = CudaCpuTranslate + CudaGpuTranslate
  sem translateCudaTops (cudaMemEnv : Map Name AllocEnv)
                        (ccEnv : CompileCEnv) =
  | tops ->
    let emptyEnv = mapEmpty nameCmp in
    let tops = map (translateTopToCudaFormat cudaMemEnv) tops in
    generateIntrinsics cudaMemEnv ccEnv tops

  sem generateIntrinsics (cudaMemEnv : Map Name AllocEnv)
                      (ccEnv : CompileCEnv) =
  | tops ->
    match mapAccumL (generateIntrinsicsTop cudaMemEnv ccEnv)
                    (mapEmpty nameCmp) tops
    with (wrapperMap, tops) in
    (wrapperMap, join tops)

  sem generateIntrinsicsTop (cudaMemEnv : Map Name AllocEnv)
                         (ccEnv : CompileCEnv)
                         (wrapperMap : Map Name Name) =
  | CuTTop (cuTop & {top = CTFun t}) ->
    match mapAccumL (generateIntrinsicStmt ccEnv) [] t.body with (tops, body) in
    match mapLookup t.id cudaMemEnv with Some _ then
      let cudaWrapperId = nameSym "cuda_wrap" in
      let wrapperMap = mapInsert t.id cudaWrapperId wrapperMap in
      let newTop = CTFun {{t with id = cudaWrapperId}
                             with body = body} in
      let cudaTop = CuTTop {cuTop with top = newTop} in
      (wrapperMap, snoc tops cudaTop)
    else
      let cudaTop = CuTTop {cuTop with top = CTFun {t with body = body}} in
      (wrapperMap, snoc tops cudaTop)
  | t -> (wrapperMap, [t])

  sem generateIntrinsicStmt (ccEnv : CompileCEnv) (acc : [CuTop]) =
  | CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}} ->
    generateIntrinsicExpr ccEnv acc outExpr t
  | stmt -> (acc, stmt)

  -- Generates an statement for the contained intrinsic, which potentially
  -- replaces the original assignment statement.
  sem generateIntrinsicExpr (ccEnv : CompileCEnv) (acc : [CuTop]) (outExpr : CExpr) =
  | t -> (acc, CSExpr {expr = CEBinOp {op = COAssign (), lhs = outExpr, rhs = t}})

  -- Updates the tops to use pointers to GPU-allocated variables inside the
  -- CUDA wrapper functions, since these cannot be stored on the stack. This
  -- does not include e.g. integer and float literals, since these are not
  -- considered to be "allocated".
  sem translateTopToCudaFormat (cudaMemEnv : Map Name AllocEnv) =
  | CTTyDef t -> CuTTop {templates = [], attrs = [], top = CTTyDef t}
  | CTDef t -> CuTTop {templates = [], attrs = [CuAHost (), CuADevice ()], top = CTDef t}
  | CTFun t ->
    match mapLookup t.id cudaMemEnv with Some allocEnv then
      let body = map (usePointerToGpuVariablesStmt allocEnv) t.body in
      let cTop = CTFun {t with body = body} in
      CuTTop {templates = [], attrs = [], top = cTop}
    else
      let attrs = [CuAHost (), CuADevice ()] in
      CuTTop {templates = [], attrs = attrs, top = CTFun t}

  sem usePointerToGpuVariablesStmt (env : AllocEnv) =
  | CSDef (t & {id = Some id}) ->
    match allocEnvLookup id env with Some (Gpu _) then
      CSDef {t with ty = CTyPtr {ty = t.ty}}
    else CSDef t
  | stmt -> stmt
end
