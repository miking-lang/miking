include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/pmexpr-ast.mc"
include "pmexpr/utils.mc"

let _cudaMalloc = nameNoSym "cudaMalloc"
let _cudaMallocManaged = nameNoSym "cudaMallocManaged"
let _cudaMemcpy = nameNoSym "cudaMemcpy"
let _cudaMemcpyDeviceToHost = nameNoSym "cudaMemcpyDeviceToHost"
let _cudaMemcpyHostToDevice = nameNoSym "cudaMemcpyHostToDevice"
let _cudaFree = nameNoSym "cudaFree"
let _cudaDeviceSynchronize = nameNoSym "cudaDeviceSynchronize"
let _malloc = nameNoSym "malloc"
let _free = nameNoSym "free"

let _CUDA_UTILS_CHECK_CUDA_ERROR = nameNoSym "CUDA_UTILS_CHECK_CUDA_ERROR"
let _CUDA_UTILS_COPY_OCAML_CUDA = nameNoSym "cuda_utils_copyOCamlToCuda"
let _CUDA_UTILS_COPY_CUDA_OCAML = nameNoSym "cuda_utils_copyCudaToOCaml"

let cudaIncludes = concat cIncludes []

lang CudaCompile = MExprCCompileAlloc + CudaPMExprAst + CudaAst
  sem _stripPointer =
  | CTyPtr {ty = ty} -> ty
  | _ -> error "_stripPointer called with non-pointer type argument"

  sem _accessMember : CType -> CExpr -> Name -> CExpr
  sem _accessMember lhsType lhs =
  | id ->
    match lhsType with CTyPtr _ then
      CEArrow {lhs = lhs, id = id}
    else CEMember {lhs = lhs, id = id}

  sem _getFunctionArgTypes (env : CompileCEnv) =
  | TmVar _ -> []
  | t & (TmApp _) ->
    match collectAppArguments t with (_, args) in
    map (lam arg. compileType env (tyTm arg)) args
  | t -> errorSingle [infoTm t] "Unsupported function type"

  sem compileExpr (env : CompileCEnv) =
  | TmSeqMap t -> errorSingle [t.info] "Maps are not supported"
  | TmSeqFoldl t ->
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqFoldl {
      f = compileExpr env t.f, acc = compileExpr env t.acc,
      s = compileExpr env t.s, sTy = compileType env (tyTm t.s),
      argTypes = argTypes, ty = compileType env t.ty}
  | TmParallelReduce t ->
    -- NOTE(larshum, 2022-03-22): Parallel reductions that are not promoted to
    -- a kernel are compiled to sequential folds.
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqFoldl {
      f = compileExpr env t.f, acc = compileExpr env t.ne,
      s = compileExpr env t.as, sTy = compileType env (tyTm t.as),
      argTypes = argTypes, ty = compileType env t.ty}
  | TmTensorSliceExn t ->
    CETensorSliceExn {
      t = compileExpr env t.t, slice = compileExpr env t.slice,
      ty = compileType env t.ty}
  | TmTensorSubExn t ->
    CETensorSubExn {
      t = compileExpr env t.t, ofs = compileExpr env t.ofs,
      len = compileExpr env t.len, ty = compileType env t.ty}
  | TmMapKernel t -> errorSingle [t.info] "Maps are not supported"
  | TmReduceKernel t -> errorSingle [t.info] "not implemented yet"
  | TmLoop t | TmParallelLoop t ->
    -- NOTE(larshum, 2022-03-08): Parallel loops that were not promoted to a
    -- kernel are compiled to sequential loops.
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqLoop {
      n = compileExpr env t.n, f = compileExpr env t.f, argTypes = argTypes}
  | TmLoopAcc t ->
    let argTypes = _getFunctionArgTypes env t.f in
    CESeqLoopAcc {
      ne = compileExpr env t.ne, n = compileExpr env t.n,
      f = compileExpr env t.f, neTy = compileType env (tyTm t.ne),
      argTypes = argTypes}
  | TmLoopKernel t ->
    let argTypes = _getFunctionArgTypes env t.f in
    CELoopKernel {
      n = compileExpr env t.n, f = compileExpr env t.f, argTypes = argTypes,
      opsPerThread = 10}
  | TmPrintFloat t ->
    CEApp {
      fun = _printf, args = [
        CEString { s = "%f" },
        compileExpr env t.e]}
end
