include "mexpr/pprint.mc"
include "pmexpr/ast.mc"

lang PMExprPrettyPrint = MExprPrettyPrint + PMExprAst
  sem isAtomic =
  | TmAccelerate _ -> false
  | TmFlatten _ -> false
  | TmMap2 _ -> false
  | TmParallelReduce _ -> false
  | TmLoop _ -> false
  | TmParallelLoop _ -> false
  | TmParallelSizeCoercion _ -> false
  | TmParallelSizeEquality _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmAccelerate t ->
    match pprintCode indent env t.e with (env, e) in
    (env, join ["accelerate ", e])
  | TmFlatten t ->
    match pprintCode indent env t.e with (env, e) in
    (env, join ["flatten ", e])
  | TmMap2 t ->
    match pprintCode indent env t.f with (env, f) in
    match pprintCode indent env t.as with (env, as) in
    match pprintCode indent env t.bs with (env, bs) in
    (env, join ["map2 ", f, " ", as, " ", bs])
  | TmParallelReduce t ->
    match pprintCode indent env t.f with (env, f) in
    match pprintCode indent env t.ne with (env, ne) in
    match pprintCode indent env t.as with (env, as) in
    (env, join ["parallelReduce ", f, " ", ne, " ", as])
  | TmLoop t ->
    match pprintCode indent env t.n with (env, n) in
    match pprintCode indent env t.f with (env, f) in
    (env, join ["loop ", n, " ", f])
  | TmParallelLoop t ->
    match pprintCode indent env t.n with (env, n) in
    match pprintCode indent env t.f with (env, f) in
    (env, join ["parallelLoop ", n, " ", f])
  | TmParallelSizeCoercion t ->
    match pprintCode indent env t.e with (env, e) in
    match pprintVarName env t.size with (env, size) in
    (env, join ["parallelSizeCoercion ", e, " ", size])
  | TmParallelSizeEquality t ->
    match pprintVarName env t.x1 with (env, x1) in
    let d1 = int2string t.d1 in
    match pprintVarName env t.x2 with (env, x2) in
    let d2 = int2string t.d2 in
    (env, join ["parallelSizeEquality ", x1, " ", d1, " ", x2, " ", d2])
end
