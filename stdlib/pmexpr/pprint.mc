include "mexpr/pprint.mc"
include "pmexpr/ast.mc"

lang PMExprPrettyPrint = MExprPrettyPrint + PMExprAst
  sem isAtomic =
  | TmAccelerate _ -> false
  | TmFlatten _ -> false
  | TmMap2 _ -> false
  | TmParallelReduce _ -> false
  | TmLoop _ -> false
  | TmLoopAcc _ -> false
  | TmParallelLoop _ -> false
  | TmPrintFloat _ -> false
  | TmParallelSizeCoercion _ -> false
  | TmParallelSizeEquality _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmAccelerate t ->
    let indent = pprintIncr indent in
    match printParen indent env t.e with (env, e) in
    (env, join ["accelerate", pprintNewline indent, e])
  | TmFlatten t ->
    let indent = pprintIncr indent in
    match printParen indent env t.e with (env, e) in
    (env, join ["flatten", pprintNewline indent, e])
  | TmMap2 t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.f, t.as, t.bs] with (env, args) in
    (env, join ["map2", pprintNewline indent, args])
  | TmParallelReduce t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.f, t.ne, t.as] with (env, args) in
    (env, join ["parallelReduce", pprintNewline indent, args])
  | TmLoop t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.n, t.f] with (env, args) in
    (env, join ["loop", pprintNewline indent, args])
  | TmLoopAcc t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.ne, t.n, t.f] with (env, args) in
    (env, join ["loopFoldl", pprintNewline indent, args])
  | TmParallelLoop t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.n, t.f] with (env, args) in
    (env, join ["parallelLoop", pprintNewline indent, args])
  | TmPrintFloat t ->
    let indent = pprintIncr indent in
    match printArgs indent env [t.e] with (env, args) in
    (env, join ["printFloat", pprintNewline indent, args])
  | TmParallelSizeCoercion t ->
    let indent = pprintIncr indent in
    match printParen indent env t.e with (env, e) in
    match pprintVarName env t.size with (env, size) in
    (env, join ["parallelSizeCoercion", pprintNewline indent, e,
                pprintNewline indent, size])
  | TmParallelSizeEquality t ->
    let indent = pprintIncr indent in
    match pprintVarName env t.x1 with (env, x1) in
    let d1 = int2string t.d1 in
    match pprintVarName env t.x2 with (env, x2) in
    let d2 = int2string t.d2 in
    (env, join ["parallelSizeEquality", pprintNewline indent, x1,
                pprintNewline indent, d1, pprintNewline indent, x2,
                pprintNewline indent, d2])
end
