-- Translates a PMExpr AST to a CUDA PMExpr AST which includes explicit GPU
-- kernel calls and memory management operations.
--
-- In this version, a parallel operation is translated to a CUDA kernel when
-- it is used in a function that is never used in another parallel operation.
-- This is conservative, but guarantees that we never end up with nested
-- kernels.

include "cuda/pmexpr-ast.mc"
include "cuda/pmexpr-pprint.mc"
include "mexpr/call-graph.mc"
include "pmexpr/utils.mc"

lang CudaPMExprKernelCalls = CudaPMExprAst + MExprCallGraph
  syn ProcessingUnits =
  | Cpu ()
  | Gpu ()
  | Both ()
  | Undef ()

  sem mergeProcessingUnits : ProcessingUnits -> ProcessingUnits -> ProcessingUnits
  sem mergeProcessingUnits lhs =
  | rhs -> mergeProcessingUnitsH (lhs, rhs)

  sem mergeProcessingUnitsH : (ProcessingUnits, ProcessingUnits) -> ProcessingUnits
  sem mergeProcessingUnitsH =
  | (Undef _, pu) | (pu, Undef _) -> pu
  | (Cpu _, Cpu _) -> Cpu ()
  | (Gpu _, Gpu _) -> Gpu ()
  | _ -> Both ()

  type FunctionEnv = Map Name ProcessingUnits

  sem functionEnvLookup : FunctionEnv -> Name -> ProcessingUnits
  sem functionEnvLookup env =
  | id -> optionGetOrElse (lam. Undef ()) (mapLookup id env)

  sem generateKernelApplications : Set Name -> Expr -> (FunctionEnv, Expr)
  sem generateKernelApplications accelerateIds =
  | t ->
    let env = findFunctionProcessingUnits accelerateIds t in
    (env, promoteKernels env t)

  -- Produces a map from function identifiers to the processing units (CPU or
  -- GPU) it may be used on at runtime. Initially, we know that the accelerate
  -- functions may only be used on the CPU.
  sem findFunctionProcessingUnits : Set Name -> Expr -> FunctionEnv
  sem findFunctionProcessingUnits accelerateIds =
  | t ->
    let env = mapMapWithKey (lam id. lam. Cpu ()) accelerateIds in
    findFunctionProcessingUnitsH env t

  sem findFunctionProcessingUnitsH : FunctionEnv -> Expr -> FunctionEnv
  sem findFunctionProcessingUnitsH env =
  | TmLet t ->
    let env = findFunctionProcessingUnitsH env t.inexpr in
    let units = functionEnvLookup env t.ident in
    propagateProcessingUnitsInBody units env t.body
  | TmRecLets t ->
    let bindMap : Map Name RecLetBinding =
      mapFromSeq nameCmp
        (map (lam bind : RecLetBinding. (bind.ident, bind)) t.bindings)
    in
    let findFunctionsBind = lam env. lam bind : RecLetBinding.
      findFunctionProcessingUnitsH env bind.body
    in
    let setFunctionsInComponent = lam env. lam comp.
      let units =
        foldl mergeProcessingUnits (Undef ())
          (map (functionEnvLookup env) comp) in
      foldl (lam env. lam id. mapInsert id units env) env comp
    in
    let propagateBinding = lam env. lam bind : RecLetBinding.
      let units = functionEnvLookup env bind.ident in
      propagateProcessingUnitsInBody units env bind.body
    in
    let env = findFunctionProcessingUnitsH env t.inexpr in
    let env = foldl findFunctionsBind env t.bindings in
    let g : Digraph Name Int = constructCallGraph (TmRecLets t) in
    let sccs = digraphTarjan g in
    let env = foldl setFunctionsInComponent env (reverse sccs) in
    foldl propagateBinding env t.bindings
  | TmType t -> findFunctionProcessingUnitsH env t.inexpr
  | TmConDef t -> findFunctionProcessingUnitsH env t.inexpr
  | TmUtest t -> findFunctionProcessingUnitsH env t.next
  | TmExt t -> findFunctionProcessingUnitsH env t.inexpr
  | _ -> env

  sem propagateProcessingUnitsInBody : ProcessingUnits -> FunctionEnv -> Expr
                                    -> FunctionEnv
  sem propagateProcessingUnitsInBody units env =
  | TmVar (t & {ty = TyArrow _}) ->
    mapInsertWith mergeProcessingUnits t.ident units env
  | TmParallelLoop t ->
    let env = propagateProcessingUnitsInBody units env t.n in
    propagateProcessingUnitsInBody (Gpu ()) env t.f
  | t -> sfold_Expr_Expr (propagateProcessingUnitsInBody units) env t

  -- Promotes parallel keywords in CPU-exclusive functions to their
  -- corresponding kernel operation.
  sem promoteKernels : FunctionEnv -> Expr -> Expr
  sem promoteKernels env =
  | TmLet t ->
    let inexpr = promoteKernels env t.inexpr in
    match mapLookup t.ident env with Some (Cpu _) then
      TmLet {{t with body = promoteKernelsBody t.body}
                with inexpr = inexpr}
    else TmLet {t with inexpr = inexpr}
  | TmRecLets t ->
    let promoteBinding = lam bind : RecLetBinding.
      match mapLookup bind.ident env with Some (Cpu _) then
        {bind with body = promoteKernelsBody bind.body}
      else bind
    in
    let inexpr = promoteKernels env t.inexpr in
    let bindings = map promoteBinding t.bindings in
    TmRecLets {{t with bindings = bindings} with inexpr = inexpr}
  | TmType t -> TmType {t with inexpr = promoteKernels env t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = promoteKernels env t.inexpr}
  | TmUtest t -> TmUtest {t with next = promoteKernels env t.next}
  | TmExt t -> TmExt {t with inexpr = promoteKernels env t.inexpr}
  | t -> t

  sem promoteKernelsBody =
  | TmParallelLoop t ->
    TmLoopKernel {n = t.n, f = t.f, ty = t.ty, info = t.info}
  | t -> smap_Expr_Expr promoteKernelsBody t
end

lang CudaPMExprCompile = CudaPMExprKernelCalls
  sem toCudaPMExpr : Map Name AccelerateData -> Expr -> (FunctionEnv, Expr)
  sem toCudaPMExpr accelerateData =
  | t ->
    let accelerateIds = mapMapWithKey (lam. lam. ()) accelerateData in
    generateKernelApplications accelerateIds t
end
