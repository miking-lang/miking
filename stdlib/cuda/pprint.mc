include "c/ast.mc"
include "c/pprint.mc"
include "cuda/ast.mc"

-- TODO(larshum, 2022-01-18): Define list of CUDA-specific keywords.
let cudaKeywords = concat cKeywords []

lang CudaPrettyPrint = CPrettyPrint + CudaAst
  sem _printCudaDim =
  | CuDX _ -> "x"
  | CuDY _ -> "y"
  | CuDZ _ -> "z"

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

  sem printCudaAttribute (env : PprintEnv) =
  | CuAHost _ -> (env, "__host__")
  | CuADevice _ -> (env, "__device__")
  | CuAGlobal _ -> (env, "__global__")

  sem printCudaTop (indent : Int) (env : PprintEnv) =
  | CuTTop {attrs = attrs, top = top} ->
    match mapAccumL printCudaAttribute env attrs with (env, attrs) in
    let attrs = if null attrs then "" else concat (strJoin " " attrs) " " in
    match printCTop indent env top with (env, top) in
    (env, join [attrs, top])

  sem printCudaProg (nameInit : [Name]) =
  | CuPProg {includes = includes, tops = tops} ->
    let indent = 0 in
    let includes = map (lam inc. join ["#include ", inc]) includes in
    let addName = lam env. lam name.
      match pprintAddStr env name with Some env then env
      else error (join ["Duplicate name in printCProg: ", nameGetStr name]) in
    let env = foldl addName pprintEnvEmpty (map nameNoSym cudaKeywords) in
    let env = foldl addName env nameInit in
    match mapAccumL (printCudaTop indent) env tops with (env, tops) in
    strJoin (pprintNewline indent) (join [includes, tops])
end

mexpr

use CudaPrettyPrint in

let printExpr : CExpr -> String = lam expr.
  match printCExpr pprintEnvEmpty expr with (_, str) in str
in

let t = CEThreadIdx {dim = CuDX ()} in
utest printExpr t with "threadIdx.x" in

let t = CEBlockIdx {dim = CuDY ()} in
utest printExpr t with "blockIdx.y" in

let t = CEBlockDim {dim = CuDZ ()} in
utest printExpr t with "blockDim.z" in

let t = CEMap {f = CEVar {id = nameNoSym "f"}, s = CEVar {id = nameNoSym "s"}} in
utest printExpr t with "map(f, s)" in

let cint_ = lam i. CEInt {i = i} in
let kernelApp = lam args : [CExpr].
  CEKernelApp {
    fun = nameNoSym "kernel",
    gridSize = (cint_ 4, cint_ 2, cint_ 7),
    blockSize = (cint_ 3, cint_ 5, cint_ 6),
    sharedMem = cint_ 12,
    args = args} in
let kernelStr : String -> String = lam str.
  concat "kernel<<<{4, 2, 7}, {3, 5, 6}, 12>>>" str
in
utest printExpr (kernelApp []) with kernelStr "()" in
utest printExpr (kernelApp [cint_ 1]) with kernelStr "(1)" in
utest printExpr (kernelApp [cint_ 1, cint_ 2]) with kernelStr "(1, 2)" in

let printCuTop = lam cudaTop : CuTop.
  match printCudaTop 0 pprintEnvEmpty cudaTop with (_, str) in str
in
let topDef = CTDef {ty = CTyInt {}, id = Some (nameNoSym "x"), init = None ()} in
let cuTop = lam attrs : [CudaAttribute].
  CuTTop {attrs = attrs, top = topDef}
in
utest printCuTop (cuTop []) with "int x;" in
utest printCuTop (cuTop [CuAHost ()]) with "__host__ int x;" in
utest printCuTop (cuTop [CuADevice (), CuAHost ()])
with "__device__ __host__ int x;" in
utest printCuTop (cuTop [CuAGlobal ()]) with "__global__ int x;" in

let prog = CuPProg {
  includes = ["<string.h>"],
  tops = [cuTop [CuADevice ()]]} in
utest printCudaProg [] prog with
"#include <string.h>
__device__ int x;" in

()
