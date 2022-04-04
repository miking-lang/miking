include "cuda/pmexpr-ast.mc"
include "pmexpr/pprint.mc"

lang CudaPMExprPrettyPrint = PMExprPrettyPrint + CudaPMExprAst
  sem isAtomic =
  | TmSeqMap _ -> false
  | TmSeqFoldl _ -> false
  | TmTensorSliceExn _ -> false
  | TmTensorSubExn _ -> false
  | TmMapKernel _ -> false
  | TmReduceKernel _ -> false
  | TmLoopKernel _ -> false
  | TmCopy _ -> false
  | TmFree _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmSeqMap t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.f, t.s] with (env, args) in
    (env, join ["seqMap", pprintNewline indent, args])
  | TmSeqFoldl t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.f, t.acc, t.s] with (env, args) in
    (env, join ["seqFoldl", pprintNewline indent, args])
  | TmTensorSliceExn t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.t, t.slice] with (env, args) in
    (env, join ["tensorSliceExn", pprintNewline indent, args])
  | TmTensorSubExn t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.t, t.ofs, t.len] with (env, args) in
    (env, join ["tensorSubExn", pprintNewline indent, args])
  | TmMapKernel t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.f, t.s] with (env, args) in
    (env, join ["mapKernel", pprintNewline indent, args])
  | TmReduceKernel t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.f, t.ne, t.s] with (env, args) in
    let reduceStr = if t.commutative then "reduceCommKernel" else "reduceKernel" in
    (env, join [reduceStr, pprintNewline indent, args])
  | TmLoopKernel t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.n, t.f] with (env, args) in
    (env, join ["loopKernel", pprintNewline indent, args])
  | TmCopy {arg = arg, toMem = Cpu _} ->
    match pprintVarName env arg with (env, arg) in
    (env, concat "copyCpu " arg)
  | TmCopy {arg = arg, toMem = Gpu _} ->
    match pprintVarName env arg with (env, arg) in
    (env, concat "copyGpu " arg)
  | TmFree {arg = arg, mem = Cpu _} ->
    match pprintVarName env arg with (env, arg) in
    (env, concat "freeCpu " arg)
  | TmFree {arg = arg, mem = Gpu _} ->
    match pprintVarName env arg with (env, arg) in
    (env, concat "freeGpu " arg)
end
