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

  sem printCType : String -> PprintEnv -> CType -> (PprintEnv, String)
  sem printCType decl env =
  | CTyConst {ty = ty} ->
    match printCType decl env ty with (env, ty) in
    (env, _joinSpace "const" ty)

  sem printCExpr (env : PprintEnv) =
  | CESeqMap {f = f, s = s} ->
    match printCExpr env f with (env, f) in
    match printCExpr env s with (env, s) in
    (env, join ["seqMap(", f, ", ", s, ")"])
  | CESeqFoldl {f = f, acc = acc, s = s} ->
    match printCExpr env f with (env, f) in
    match printCExpr env acc with (env, acc) in
    match printCExpr env s with (env, s) in
    (env, join ["seqFoldl(", f, ", ", acc, ", ", s, ")"])
  | CESeqLoop {n = n, f = f} ->
    match printCExpr env n with (env, n) in
    match printCExpr env f with (env, f) in
    (env, join ["seqLoop(", n, ", ", f, ")"])
  | CESeqLoopAcc {ne = ne, n = n, f = f} ->
    match printCExpr env ne with (env, ne) in
    match printCExpr env n with (env, n) in
    match printCExpr env f with (env, f) in
    (env, join ["seqLoopFoldl(", ne, ", ", n, ", ", f, ")"])
  | CETensorSliceExn {t = t, slice = slice} ->
    match printCExpr env t with (env, t) in
    match printCExpr env slice with (env, slice) in
    (env, join ["tensorSliceExn(", t, ", ", slice, ")"])
  | CETensorSubExn {t = t, ofs = ofs, len = len} ->
    match printCExpr env t with (env, t) in
    match printCExpr env ofs with (env, ofs) in
    match printCExpr env len with (env, len) in
    (env, join ["tensorSubExn(", t, ", ", ofs, ", ", len, ")"])
  | CEThreadIdx {dim = dim} -> (env, concat "threadIdx." (_printCudaDim dim))
  | CEBlockIdx {dim = dim} -> (env, concat "blockIdx." (_printCudaDim dim))
  | CEBlockDim {dim = dim} -> (env, concat "blockDim." (_printCudaDim dim))
  | CEGridDim {dim = dim} -> (env, concat "gridDim." (_printCudaDim dim))
  | CEMapKernel {f = f, s = s, opsPerThread = opsPerThread} ->
    match printCExpr env f with (env, f) in
    match printCExpr env s with (env, s) in
    let ops = int2string opsPerThread in
    (env, join ["CEMapKernel(", f, ", ", s, ")[opsPerThread=", ops, "]"])
  | CELoopKernel {n = n, f = f, opsPerThread = opsPerThread} ->
    match printCExpr env n with (env, n) in
    match printCExpr env f with (env, f) in
    let ops = int2string opsPerThread in
    (env, join ["CELoopKernel(", n, ", ", f, ")[opsPerThread=", ops, "]"])
  | CEKernelApp t ->
    match cPprintEnvGetStr env t.fun with (env, fun) in
    match mapAccumL printCExpr env t.args with (env, args) in
    match printCExpr env t.gridSize with (env, gridSize) in
    match printCExpr env t.blockSize with (env, blockSize) in
    (env, join [fun, "<<<", gridSize, ", ", blockSize, ">>>(",
                strJoin ", " args, ")"])

  sem printCStmt (indent : Int) (env : PprintEnv) =
  | CSIfMacro {cond = cond, thn = thn, els = els} ->
    let i = indent in
    match printCExpr env cond with (env, cond) in
    match printCStmts i env thn with (env, thn) in
    match printCStmts i env els with (env, els) in
    (env, join [
      "#if (", cond, ")", pprintNewline i, thn, pprintNewline i,
      "#else", pprintNewline i, els, pprintNewline i, "#endif"])

  sem printCudaAttribute (env : PprintEnv) =
  | CuAHost _ -> (env, "__host__")
  | CuADevice _ -> (env, "__device__")
  | CuAGlobal _ -> (env, "__global__")
  | CuAExternC _ -> (env, "extern \"C\"")
  | CuAManaged _ -> (env, "__managed__")

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

let printType : CType -> String = lam ty.
  match printCType "" pprintEnvEmpty ty with (_, str) in str
in

let printExpr : CExpr -> String = lam expr.
  match printCExpr pprintEnvEmpty expr with (_, str) in str
in

let t = CEThreadIdx {dim = CuDX ()} in
utest printExpr t with "threadIdx.x" in

let t = CEBlockIdx {dim = CuDY ()} in
utest printExpr t with "blockIdx.y" in

let t = CEBlockDim {dim = CuDZ ()} in
utest printExpr t with "blockDim.z" in

let t = CEGridDim {dim = CuDX ()} in
utest printExpr t with "gridDim.x" in

let ty = CTyConst {ty = CTyInt ()} in
utest printType ty with "const int" in

let cint_ = lam i. CEInt {i = i} in
let kernelApp = lam args : [CExpr].
  CEKernelApp {
    fun = nameNoSym "kernel",
    gridSize = cint_ 7,
    blockSize = cint_ 5,
    args = args} in
let kernelStr : String -> String = lam str.
  concat "kernel<<<7, 5>>>" str
in
utest printExpr (kernelApp []) with kernelStr "()" in
utest printExpr (kernelApp [cint_ 1]) with kernelStr "(1)" in
utest printExpr (kernelApp [cint_ 1, cint_ 2]) with kernelStr "(1, 2)" in

let printCStmt = lam stmt : CStmt.
  match printCStmt 0 pprintEnvEmpty stmt with (_, str) in str
in

let y = nameNoSym "y" in
let ifMacroStmt = CSIfMacro {
  cond = CEApp {
    fun = nameNoSym "defined", args = [CEVar {id = nameNoSym "x"}]},
  thn = [CSDef {ty = CTyInt (), id = Some y, init = Some (CIExpr {expr = CEInt {i = 1}})}],
  els = [CSDef {ty = CTyInt (), id = Some y, init = Some (CIExpr {expr = CEInt {i = 2}})}]} in
utest printCStmt ifMacroStmt with strJoin "\n" [
  "#if (defined(x))",
  "int y = 1;",
  "#else",
  "int y = 2;",
  "#endif"
] using eqString in

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
utest printCuTop (cuTop [CuAManaged ()]) with "__managed__ int x;" in

let prog = CuPProg {
  includes = ["<string.h>"],
  tops = [cuTop [CuADevice ()]]} in
utest printCudaProg [] prog with
"#include <string.h>
__device__ int x;" in

()
