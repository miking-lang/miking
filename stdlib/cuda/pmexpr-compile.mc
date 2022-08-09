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
  sem generateKernelApplications =
  | t ->
    let marked = markNonKernelFunctions t in
    promoteKernels marked t

  -- Produces a set of identifiers corresponding to the functions that are used
  -- directly or indirectly by a parallel operation. Parallel keywords within
  -- such functions are not promoted to kernels.
  sem markNonKernelFunctions =
  | t -> markNonKernelFunctionsH (setEmpty nameCmp) t

  sem markNonKernelFunctionsH (marked : Set Name) =
  | TmLet t ->
    let marked = markNonKernelFunctionsH marked t.inexpr in
    if setMem t.ident marked then
      markInBody marked t.body
    else markInUnmarkedBody marked t.body
  | TmRecLets t ->
    let bindMap : Map Name Expr =
      mapFromSeq nameCmp
        (map
          (lam bind : RecLetBinding. (bind.ident, bind.body))
          t.bindings) in
    let markFunctionsInComponent = lam marked. lam comp.
      if any (lam e. setMem e marked) comp then
        foldl
          (lam marked. lam bindId.
            -- NOTE(larshum, 2022-08-09): The call graph construction includes
            -- nested functions. We are only interested in marking the bindings
            -- themselves, so we do nothing if it's not a binding.
            match mapLookup bindId bindMap with Some bindBody then
              markInBody marked bindBody
            else marked)
          marked comp
      else marked
    in
    let marked = markNonKernelFunctionsH marked t.inexpr in
    let g : Digraph Name Int = constructCallGraph (TmRecLets t) in
    let sccs = digraphTarjan g in
    foldl markFunctionsInComponent marked (reverse sccs)
  | TmType t -> markNonKernelFunctionsH marked t.inexpr
  | TmConDef t -> markNonKernelFunctionsH marked t.inexpr
  | TmUtest t -> markNonKernelFunctionsH marked t.next
  | TmExt t -> markNonKernelFunctionsH marked t.inexpr
  | t -> marked

  sem markInUnmarkedBody (marked : Set Name) =
  | TmParallelLoop t -> markInBody marked t.f
  | t -> sfold_Expr_Expr markInUnmarkedBody marked t

  sem markInBody (marked : Set Name) =
  | TmVar (t & {ty = TyArrow _}) -> setInsert t.ident marked
  | t -> sfold_Expr_Expr markInBody marked t

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

  -- TODO(larshum, 2022-03-22): Add support for sequence map and reduce
  -- kernels.
  sem promoteKernelsBody =
  | TmParallelLoop {n = n, f = f, ty = ty, info = info} ->
    TmLoopKernel {n = n, f = f, ty = ty, info = info}
  | t -> smap_Expr_Expr promoteKernelsBody t
end

lang CudaPMExprCompile = CudaPMExprKernelCalls
  sem toCudaPMExpr =
  | t -> generateKernelApplications t
end
