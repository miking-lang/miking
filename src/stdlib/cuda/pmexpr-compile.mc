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
  | TmDecl (x & {decl = DeclLet t}) ->
    let marked = markNonKernelFunctionsH marked x.inexpr in
    if setMem t.ident marked then
      markInBody marked t.body
    else markInUnmarkedBody marked t.body
  | tm & TmDecl (x & {decl = DeclRecLets t}) ->
    let bindMap : Map Name Expr =
      mapFromSeq nameCmp
        (map
          (lam bind : DeclLetRecord. (bind.ident, bind.body))
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
    let marked = markNonKernelFunctionsH marked x.inexpr in
    let g : Digraph Name Int = constructCallGraph tm in
    let sccs = digraphTarjan g in
    foldl markFunctionsInComponent marked (reverse sccs)
  | TmDecl x -> markNonKernelFunctionsH marked x.inexpr
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
  | TmDecl (x & {decl = DeclLet t}) ->
    let inexpr = promoteKernels marked x.inexpr in
    if setMem t.ident marked then TmDecl {x with inexpr = inexpr}
    else
      let body = promoteKernelsBody t.body in
      TmDecl {x with decl = DeclLet {t with body = body}, inexpr = inexpr}
  | TmDecl (x & {decl = DeclRecLets t}) ->
    let promoteKernelBinding = lam binding : DeclLetRecord.
      if setMem binding.ident marked then binding
      else {binding with body = promoteKernelsBody binding.body}
    in
    let inexpr = promoteKernels marked x.inexpr in
    let bindings = map promoteKernelBinding t.bindings in
    TmDecl {x with decl = DeclRecLets {t with bindings = bindings}, inexpr = inexpr}
  | TmDecl x -> TmDecl {x with inexpr = promoteKernels marked x.inexpr}
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
