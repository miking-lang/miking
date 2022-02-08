include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/pmexpr-ast.mc"

let _cudaMalloc = nameNoSym "cudaMalloc"
let _cudaMemcpy = nameNoSym "cudaMemcpy"
let _cudaFree = nameNoSym "cudaFree"
let _malloc = nameNoSym "malloc"
let _free = nameNoSym "free"

lang CudaCompile = MExprCCompileAlloc + CudaPMExprAst + CudaAst
  sem compileOp (t: Expr) (args: [CExpr]) =
  | CMap _ ->
    CEMap {f = get args 0, s = get args 1}

  sem compileStmt (env : CompileCEnv) (res : Result) =
  | TmMapKernel t -> (env, [])
  | TmReduceKernel t -> (env, [])
  | TmCopy t ->
    -- NOTE(larshum, 2022-02-07): This must always be an identifier, since the
    -- result of a copy is always stored in a named variable.
    match res with RIdent dstId in
    let arg = compileExpr env t.arg in
    -- TODO(larshum, 2022-02-07): Generate copying code...
    match t.toMem with Cpu _ then
      (env, [])
    else match t.toMem with Gpu _ then
      (env, [])
    else never
  | TmFree t ->
    let arg = CEVar {id = t.arg} in
    match t.mem with Cpu _ then
      (env, [CSExpr {expr = CEApp {fun = _free, args = [arg]}}])
    else match t.mem with Gpu _ then
      (env, [CSExpr {expr = CEApp {fun = _cudaFree, args = [arg]}}])
    else never
end
