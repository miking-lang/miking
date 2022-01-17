include "c/ast.mc"
include "c/pprint.mc"
include "cuda/ast.mc"

lang CudaPrettyPrint = CPrettyPrint + CProgPrettyPrint + CudaAst
  sem _printCudaDim =
  | DimX _ -> "x"
  | DimY _ -> "y"
  | DimZ _ -> "z"

  sem printCExpr (env: PprintEnv) =
  | CEMap {f = f, s = s} ->
    match printCExpr env f with (env, f) in
    match printCExpr env s with (env, s) in
    (env, join ["map(", f, ", ", s, ")"])
  | CEThreadIdx {dim = dim} -> (env, concat "threadIdx." (_printCudaDim dim))
  | CEBlockIdx {dim = dim} -> (env, concat "blockIdx." (_printCudaDim dim))
  | CEBlockDim {dim = dim} -> (env, concat "blockDim." (_printCudaDim dim))
  | CEKernelApp t ->
    let _printInitList = lam env : PprintEnv. lam indices : (CExpr, CExpr, CExpr).
      match printCExpr env indices.0 with (env, x) in
      match printCExpr env indices.1 with (env, y) in
      match printCExpr env indices.2 with (env, z) in
      (env, join ["{", x, ", ", y, ", ", z, "}"]) in
    match pprintEnvGetStr env t.fun with (env, fun) in
    match mapAccumL printCExpr env t.args with (env, args) in
    match _printInitList env t.gridSize with (env, gridDims) in
    match _printInitList env t.blockSize with (env, blockDims) in
    match printCExpr env t.sharedMem with (env, sharedMem) in
    (env, join [fun, "<<<", gridDims, ", ", blockDims, ", ", sharedMem, ">>>(",
                strJoin ", " args, ")"])

  sem printCTop (indent : Int) (env : PprintEnv) =
  | CTGlobalAttr {top = top} ->
    match printCTop indent env top with (env, top) in
    (env, concat "__global__ " top)
  | CTDeviceAttr {top = top} ->
    match printCTop indent env top with (env, top) in
    (env, concat "__device__ " top)
end

mexpr

use CudaPrettyPrint in

let cint_ = lam i. CEInt {i = i} in

let t = CEKernelApp {
  fun = nameNoSym "kernel", gridSize = (cint_ 1, cint_ 2, cint_ 3),
  blockSize = (cint_ 4, cint_ 5, cint_ 6), sharedMem = cint_ 0, args = []} in
match printCExpr pprintEnvEmpty t with (_, str) in
utest str with "kernel<<<{1, 2, 3}, {4, 5, 6}, 0>>>()" in

let t = CTFun {
  ret = CTyInt (), id = nameNoSym "kernel", params = [],
  body = [
    CSDef { ty = CTyInt (), id = Some (nameNoSym "idx")
          , init = Some (CIExpr {expr = CEBinOp {
              op = COAdd (), lhs = CEThreadIdx {dim = DimX ()},
              rhs = CEBinOp {
                op = COMul (),
                lhs = CEBlockIdx {dim = DimX ()},
                rhs = CEBlockDim {dim = DimX ()}}}})},
    CSRet {val = Some (CEVar {id = nameNoSym "idx"})}]} in
match printCTop 0 pprintEnvEmpty (CTGlobalAttr {top = t}) with (_, str) in
utest str with
"__global__ int kernel() {
  int idx = (threadIdx.x + (blockIdx.x * blockDim.x));
  return idx;
}" in

match printCTop 0 pprintEnvEmpty (CTDeviceAttr {top = t}) with (_, str) in
utest str with
"__device__ int kernel() {
  int idx = (threadIdx.x + (blockIdx.x * blockDim.x));
  return idx;
}" in

()
