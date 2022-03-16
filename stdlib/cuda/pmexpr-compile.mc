-- Translates a PMExpr AST to a CUDA PMExpr AST which includes explicit GPU
-- kernel calls and memory management operations.
--
-- In this version, a parallel operation is translated to a CUDA kernel when
-- it is used in a function that is never used in another parallel operation.
-- This is conservative, but guarantees that we never end up with nested
-- kernels.

include "cuda/pmexpr-ast.mc"
include "pmexpr/utils.mc"

lang CudaPMExprKernelCalls = CudaPMExprAst
  sem generateKernelApplications =
  | t ->
    let marked = markNonKernelFunctions t in
    (marked, promoteKernels marked t)
    
  -- Produces a set of identifiers corresponding to the functions that are used
  -- directly or indirectly by a parallel operation. Parallel keywords within
  -- such functions are not promoted to kernels.
  sem markNonKernelFunctions =
  | t -> markNonKernelFunctionsH (setEmpty nameCmp) t

  sem markNonKernelFunctionsH (functions : Set Name) =
  | TmLet t ->
    let functions = markNonKernelFunctionsH functions t.inexpr in
    if setMem t.ident functions then markFunctionsBody functions t.body
    else functions
  | TmRecLets t ->
    let markFunctionsBinding = lam functions. lam bind : RecLetBinding.
      markFunctionsBody functions bind.body
    in
    let functions = markNonKernelFunctionsH functions t.inexpr in
    -- NOTE(larshum, 2022-03-15): For simplicity, all functions in a recursive
    -- binding are marked for now.
    if any (lam bind : RecLetBinding. setMem bind.ident functions) t.bindings then
      foldl markFunctionsBinding functions t.bindings
    else functions
  | TmType t -> markNonKernelFunctionsH functions t.inexpr
  | TmConDef t -> markNonKernelFunctionsH functions t.inexpr
  | TmUtest t -> markNonKernelFunctionsH functions t.next
  | TmExt t -> markNonKernelFunctionsH functions t.inexpr
  | t -> functions

  -- Adds all function identifiers used in a parallel operation to the set of
  -- marked functions.
  sem markFunctionsBody (marked : Set Name) =
  | TmSeqMap t -> markFunctionsBodyH marked t.f
  | TmParallelReduce t -> markFunctionsBodyH marked t.f
  | TmParallelLoop t -> markFunctionsBodyH marked t.f
  | t -> sfold_Expr_Expr markFunctionsBody marked t

  sem markFunctionsBodyH (marked : Set Name) =
  | TmVar t ->
    match t.ty with TyArrow _ then setInsert marked t.ident
    else marked
  | t -> sfold_Expr_Expr markFunctionsBodyH marked t

  -- Promotes parallel operations used in functions that have not been marked
  -- to kernel operations.
  sem promoteKernels (marked : Set Name) =
  | TmLet t ->
    let inexpr = promoteKernels marked t.inexpr in
    if setMem t.ident marked then TmLet {t with inexpr = inexpr}
    else
      let body = promoteKernelsBody t.body in
      TmLet {{t with body = body} with inexpr = inexpr}
  | TmRecLets t ->
    let promoteKernelBinding = lam binding : RecLetBinding.
      if setMem binding.ident marked then binding
      else {binding with body = promoteKernelsBody binding.body}
    in
    let inexpr = promoteKernels marked t.inexpr in
    let bindings = map promoteKernelBinding t.bindings in
    TmRecLets {{t with inexpr = inexpr} with bindings = bindings}
  | TmType t -> TmType {t with inexpr = promoteKernels marked t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = promoteKernels marked t.inexpr}
  | TmUtest t -> TmUtest {t with next = promoteKernels marked t.next}
  | TmExt t -> TmExt {t with inexpr = promoteKernels marked t.inexpr}
  | t -> t

  sem promoteKernelsBody =
  | TmSeqMap {f = f, s = s, ty = ty, info = info} ->
    TmMapKernel {f = f, s = s, ty = ty, info = info}
  | TmParallelReduce {f = f, ne = ne, as = as, ty = ty, info = info} ->
    -- TODO(larshum, 2022-03-14): Add code for determining whether a parallel
    -- reduce is commutative or not. Perhaps we should have a separate PMExpr
    -- node for commutative operations?
    TmReduceKernel {f = f, ne = ne, s = as, commutative = false, ty = ty, info = info}
  | TmParallelLoop {n = n, f = f, ty = ty, info = info} ->
    TmLoopKernel {n = n, f = f ,ty = ty, info = info}
  | t -> smap_Expr_Expr promoteKernelsBody t
end

lang CudaPMExprMemoryManagement = CudaPMExprAst + PMExprVariableSub
  type AllocEnv = Map Name AllocMem

  sem allocEnvEmpty =
  | () -> mapEmpty nameCmp

  sem allocEnvInsert (id : Name) (mem : AllocMem) =
  | env -> mapInsert id mem env

  sem allocEnvLookup (id : Name) =
  | env -> mapLookup id env

  sem allocEnvRemove (id : Name) =
  | env -> mapRemove id env

  sem cudaMemMgrError =
  | info ->
    infoErrorExit info "Internal compiler error: CUDA sequence memory management"

  sem addMemoryOperations =
  | body ->
    let env = allocEnvEmpty () in
    match addMemoryAllocations env body with (env, body) in
    match addFreeOperations env body with (_, body) in
    (env, body)

  sem addMemoryAllocations (env : AllocEnv) =
  | TmVar t ->
    match allocEnvLookup t.ident env with Some (Cpu _) then
      (env, TmVar t)
    else
      let cpuId = nameSetNewSym t.ident in
      let retExpr = TmVar {t with ident = cpuId} in
      let varAlloc = TmLet {
        ident = cpuId, tyBody = t.ty,
        body = TmCopy {arg = t.ident, toMem = Cpu (), ty = t.ty, info = t.info},
        inexpr = retExpr, ty = t.ty, info = t.info} in
      (env, varAlloc)
  | TmLam t ->
    let env = allocEnvInsert t.ident (Cpu ()) env in
    match addMemoryAllocations env t.body with (env, body) in
    (env, TmLam {t with body = body})
  | TmLet t ->
    match addMemoryAllocations env t.inexpr with (env, inexpr) in
    (env, TmLet {t with inexpr = inexpr})
  | TmLet (t & {body = !(TmSeq _ | TmRecord _)}) ->
    let toMem = if isKernel t.body then Gpu () else Cpu () in
    let env = allocEnvInsert t.ident toMem env in
    let vars = collectVarsInExpr env (mapEmpty nameCmp) t.body in
    let subMap =
      mapFoldWithKey
        (lam subMap : [Map Name (Info -> Expr)]. lam id : Name.
         lam memTy : (AllocMem, Type).
          match memTy with (mem, ty) in
          match ty with TyTensor _ | TySeq _ then
            if eqMem mem toMem then subMap
            else
              let altId = nameSetNewSym id in
              let exprFun = lam info.
                TmVar {ident = altId, ty = ty, info = info, frozen = false} in
              mapInsert id exprFun subMap
          else subMap)
        (mapEmpty nameCmp) vars in
    let env =
      mapFoldWithKey
        (lam acc : AllocEnv. lam. lam exprF : Info -> Expr.
          let expr = exprF (NoInfo ()) in
          match expr with TmVar vt then
            allocEnvInsert vt.ident toMem acc
          else cudaMemMgrError t.info)
        env subMap in
    match addMemoryAllocations env t.inexpr with (env, inexpr) in
    let letExpr = TmLet {{t with body = substituteVariables subMap t.body}
                            with inexpr = inexpr} in
    let letExpr =
      mapFoldWithKey
        (lam acc : Expr. lam id : Name. lam exprF : Info -> Expr.
          let expr = exprF (infoTm acc) in
          match expr with TmVar vt then
            let copyExpr = TmCopy {
              arg = id, toMem = toMem, ty = tyTm expr, info = infoTm expr} in
            TmLet {
              ident = vt.ident, tyBody = tyTm copyExpr, body = copyExpr,
              inexpr = acc, ty = tyTm acc, info = infoTm acc}
          else cudaMemMgrError t.info)
        letExpr subMap in
    (env, letExpr)
  | t -> smapAccumL_Expr_Expr addMemoryAllocations env t

  sem addFreeOperations (env : AllocEnv) =
  | TmVar t -> (allocEnvRemove t.ident env, TmVar t)
  | TmLam t ->
    let env = allocEnvRemove t.ident env in
    match addFreeOperations env t.body with (env, body) in
    (env, TmLam {t with body = body})
  | TmLet t ->
    let vars = collectVarsInExpr env (mapEmpty nameCmp) t.body in
    match addFreeOperations env t.inexpr with (env, inexpr) in
    match
      mapFoldWithKey
        (lam acc : (AllocEnv, [Expr]). lam id : Name. lam memTy : (AllocMem, Type).
          match memTy with (mem, ty) in
          match ty with TyTensor _ | TySeq _ then
            match acc with (env, freeLets) in
            match allocEnvLookup id env with Some _ then
              let unitTy = tyWithInfo t.info tyunit_ in
              let freeExpr = TmFree {
                arg = id, tyArg = ty, mem = mem, ty = unitTy, info = t.info} in
              let freeLet = TmLet {
                ident = nameNoSym "", tyBody = tyTm inexpr, body = freeExpr,
                inexpr = unit_, ty = t.ty, info = t.info} in
              (env, snoc freeLets freeLet)
            else acc
          else acc)
        (env, [])
        vars
    with (env, freeLets) in
    (env, bindall_ (join [
      [TmLet {t with inexpr = unit_}],
      freeLets,
      [inexpr]]))
  | t -> smapAccumL_Expr_Expr addFreeOperations env t

  sem insertMemoryOperations (env : AllocEnv) =
  | TmLet t ->
    match addMemoryOperations t.body with (env1, body) in
    let env = mapUnion env env1 in
    match insertMemoryOperations env t.inexpr with (env, inexpr) in
    (env, TmLet {{t with body = body} with inexpr = inexpr})
  | TmRecLets t ->
    let insertMemoryOperationsBinding = lam env : AllocEnv. lam bind : RecLetBinding.
      match addMemoryOperations bind.body with (env, body) in
      (env, {bind with body = body})
    in
    match mapAccumL insertMemoryOperationsBinding env t.bindings
    with (env, bindings) in
    match insertMemoryOperations env t.inexpr with (env, inexpr) in
    (env, TmRecLets {{t with bindings = bindings} with inexpr = inexpr})
  | TmType t ->
    match insertMemoryOperations env t.inexpr with (env, inexpr) in
    (env, TmType {t with inexpr = inexpr})
  | TmConDef t ->
    match insertMemoryOperations env t.inexpr with (env, inexpr) in
    (env, TmConDef {t with inexpr = inexpr})
  | TmUtest t ->
    match insertMemoryOperations env t.next with (env, next) in
    (env, TmUtest {t with next = next})
  | TmExt t ->
    match insertMemoryOperations env t.inexpr with (env, inexpr) in
    (env, TmExt {t with inexpr = inexpr})
  | t -> (env, t)

  sem collectVarsInExpr (env : AllocEnv) (acc : Map Name (AllocMem, Type)) =
  | TmVar t ->
    match allocEnvLookup t.ident env with Some mem then
      mapInsert t.ident (mem, t.ty) acc
    else acc
  | t -> sfold_Expr_Expr (collectVarsInExpr env) acc t
end

lang CudaPMExprCompile = CudaPMExprKernelCalls + CudaPMExprMemoryManagement
  sem toCudaPMExpr =
  | t ->
    match generateKernelApplications t with (marked, t) in
    match insertMemoryOperations (mapEmpty nameCmp) t with (_, t) in
    (marked, t)
end
