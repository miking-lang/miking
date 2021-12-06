include "ast-builder.mc"
include "common.mc"
include "ocaml/pprint.mc"

-- Converts a given float to a string that uses a valid representation in
-- Futhark. This is needed because the 'float2string' intrinsic emits the
-- digits of the faction after the dot if the value is an integer.
let futharkFloat2string = lam f.
  let s = float2string f in
  if eqi (floorfi f) (ceilfi f) then
    snoc s '0'
  else s

utest futharkFloat2string 2.0 with "2.0"
utest futharkFloat2string 3.14 with "3.14"

lang FutharkIdentifierPrettyPrint = IdentifierPrettyPrint
  sem pprintConName (env : PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env, str) then
      let s = escapeConString str in
      (env, s)
    else never

  sem pprintVarName (env : PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env, str) then
      let s = escapeVarString str in
      (env, s)
    else never

  sem pprintLabelString =
  | sid -> escapeLabelString (sidToString sid)
end

lang FutharkConstPrettyPrint = FutharkAst
  sem pprintConst =
  | FCInt t -> join [int2string t.val, "i64"]
  | FCFloat t -> join [futharkFloat2string t.val, "f64"]
  | FCBool t -> if t.val then "true" else "false"
  | FCAdd () -> "(+)"
  | FCSub () -> "(-)"
  | FCMul () -> "(*)"
  | FCDiv () -> "(/)"
  | FCNegi () -> "(i64.neg)"
  | FCNegf () -> "(f64.neg)"
  | FCRem () -> "(%)"
  | FCFloatFloor () -> "f64.floor"
  | FCFloat2Int () -> "i64.f64"
  | FCInt2Float () -> "f64.i64"
  | FCEq () -> "(==)"
  | FCNeq () -> "(!=)"
  | FCGt () -> "(>)"
  | FCLt () -> "(<)"
  | FCGeq () -> "(>=)"
  | FCLeq () -> "(<=)"
  | FCMap () -> "map"
  | FCMap2 () -> "map2"
  | FCReduce () -> "reduce"
  | FCFlatten () -> "flatten"
  | FCIndices () -> "indices"
  | FCIota () -> "iota"
  | FCLength () -> "length"
  | FCReverse () -> "reverse"
  | FCConcat () -> "concat"
  | FCHead () -> "head"
  | FCTail () -> "tail"
  | FCNull () -> "null"
  | FCFoldl () -> "foldl"
  | FCReplicate () -> "replicate"
  | FCTabulate () -> "tabulate"
  | FCCopy () -> "copy"
end

lang FutharkPatPrettyPrint = FutharkAst + PatNamePrettyPrint
  sem pprintPat (indent : Int) (env : PprintEnv) =
  | FPNamed t -> _pprint_patname env t.ident
  | FPInt t -> (env, int2string t.val)
  | FPBool t -> (env, if t.val then "true" else "false")
  | FPRecord t ->
    if mapIsEmpty t.bindings then (env, "{}")
    else match record2tuple t.bindings with Some pats then
      match mapAccumL (lam env. lam e. pprintPat indent env e) env pats
      with (env, tuplePats) then
        let merged =
          match tuplePats with [e]
          then concat e ","
          else strJoin ", " tuplePats in
        (env, join ["(", merged, ")"])
      else never
    else match
      mapMapAccum
        (lam env. lam k. lam v.
           match pprintPat indent env v with (env,str) then
             (env,join [pprintLabelString k, " = ", str])
           else never)
         env t.bindings
    with (env,bindMap) then
      (env,join ["{", strJoin ", " (mapValues bindMap), "}"])
    else never
end

lang FutharkTypeParamPrettyPrint = FutharkAst + FutharkIdentifierPrettyPrint
  sem pprintTypeParam (env : PprintEnv) =
  | FPSize {val = n} ->
    match pprintVarName env n with (env, n) then
      (env, join ["[", n, "]"])
    else never
  | FPType {val = n} ->
    match pprintVarName env n with (env, n) then
      (env, cons '\'' n)
    else never
end

lang FutharkTypePrettyPrint = FutharkAst + FutharkIdentifierPrettyPrint
  sem pprintExpr (indent : Int) (env : PprintEnv) =

  sem pprintType (indent : Int) (env : PprintEnv) =
  | FTyUnknown _ -> (env, "")
  | FTyInt _ -> (env, "i64")
  | FTyFloat _ -> (env, "f64")
  | FTyBool _ -> (env, "bool")
  | FTyIdent {ident = ident} -> pprintVarName env ident
  | FTyArray {elem = elem, dim = dim} ->
    let pprintDim = lam dim.
      optionMapOrElse (lam. (env, "")) (pprintVarName env) dim
    in
    match pprintDim dim with (env, dimStr) then
      match pprintType indent env elem with (env, elem) then
        (env, join ["[", dimStr, "]", elem])
      else never
    else never
  | FTyRecord {fields = fields} ->
    let pprintField = lam env. lam k. lam ty.
      let str = pprintLabelString k in
      match pprintType indent env ty with (env, tyStr) then
        (env, join [str, " : ", tyStr])
      else never
    in
    match mapMapAccum pprintField env fields with (env, fields) then
      (env, join ["{", strJoin "," (mapValues fields), "}"])
    else never
  | FTyArrow {from = from, to = to} ->
    match pprintType indent env from with (env, from) then
      match pprintType indent env to with (env, to) then
        (env, join ["(", from, ") -> (", to, ")"])
      else never
    else never
  | FTyParamsApp {ty = ty, params = params} ->
    -- NOTE(larshum, 2021-05-31): For now we always use implicit parameter
    -- types.
    match pprintType indent env ty with (env, ty) then
      let implicitParams = create (length params) (lam. "[]") in
      (env, join [ty, " ", join implicitParams])
    else never
end

lang FutharkExprPrettyPrint = FutharkAst + FutharkConstPrettyPrint +
                              FutharkPatPrettyPrint + FutharkTypePrettyPrint
  sem isAtomic =
  | FEVar _ -> true
  | FESizeCoercion _ -> true
  | FERecord _ -> true
  | FERecordUpdate _ -> true
  | FERecordProj _ -> false
  | FEArray _ -> true
  | FEArrayAccess _ -> false
  | FEArrayUpdate _ -> false
  | FEArraySlice _ -> false
  | FEConst _ -> true
  | FELam _ -> false
  | FEApp _ -> false
  | FELet _ -> false
  | FEIf _ -> false
  | FEForEach _ -> false
  | FEMatch _ -> false

  sem pprintParen (indent : Int) (env : PprintEnv) =
  | expr ->
    let i = if isAtomic expr then indent else addi 1 indent in
    match pprintExpr i env expr with (env, str) then
      if isAtomic expr then (env, str)
      else (env, join ["(", str, ")"])
    else never

  sem pprintArgs (indent : Int) (env : PprintEnv) =
  | exprs ->
    match mapAccumL (pprintParen indent) env exprs with (env, args) then
      (env, strJoin (pprintNewline indent) args)
    else never

  sem pprintExpr (indent : Int) (env : PprintEnv) =
  | FEVar {ident = ident} -> pprintVarName env ident
  | FESizeCoercion {e = e, ty = ty} ->
    match pprintExpr indent env e with (env, e) in
    match pprintType indent env ty with (env, ty) in
    (env, join [e, " :> ", ty])
  | FESizeEquality _ ->
    -- NOTE(larshum, 2021-11-30): These expressions are processed and
    -- eliminated from the AST at an earlier point. As they have no effect on
    -- the evaluation of the program, they are replaced by empty tuples.
    (env, join ["()"])
  | FERecord {fields = fields} ->
    let pprintField = lam env. lam k. lam v.
      let str = pprintLabelString k in
      match pprintExpr indent env v with (env, expr) then
        (env, join [str, " = ", expr])
      else never
    in
    match mapMapAccum pprintField env fields with (env, fields) then
      (env, join ["{", strJoin "," (mapValues fields), "}"])
    else never
  | FERecordProj {rec = rec, key = key} ->
    match pprintParen indent env rec with (env, rec) then
      let str = pprintLabelString key in
      (env, join [rec, ".", str])
    else never
  | FERecordUpdate {rec = rec, key = key, value = value} ->
    match pprintParen indent env rec with (env, rec) then
      let key = pprintLabelString key in
      match pprintExpr indent env value with (env, value) then
        (env, join [rec, " with ", key, " = ", value])
      else never
    else never
  | FEArray {tms = tms} ->
    match mapAccumL (pprintExpr indent) env tms with (env, tms) then
      (env, join ["[", strJoin "," tms, "]"])
    else never
  | (FEArrayAccess {array = FEArrayAccess _, index = _}) & t ->
    recursive let indicesAndTarget = lam indices. lam e.
      match e with FEArrayAccess t then
        indicesAndTarget (cons t.index indices) t.array
      else (indices, e)
    in
    match indicesAndTarget [] t with (indices, arrayTarget) then
      match pprintExpr indent env arrayTarget with (env, array) then
        match mapAccumL (pprintExpr indent) env indices with (env, indices) then
          (env, join [array, "[", strJoin "," indices, "]"])
        else never
      else never
    else never
  | FEArrayAccess {array = array, index = index} ->
    match pprintExpr indent env array with (env, array) then
      match pprintExpr indent env index with (env, index) then
        (env, join [array, "[", index, "]"])
      else never
    else never
  | FEArrayUpdate {array = array, index = index, value = value} ->
    match pprintExpr indent env array with (env, array) then
      match pprintExpr indent env index with (env, index) then
        match pprintExpr indent env value with (env, value) then
          (env, join [array, " with [", index, "] = ", value])
        else never
      else never
    else never
  | FEArraySlice {array = array, startIdx = startIdx, endIdx = endIdx} ->
    match pprintExpr indent env array with (env, array) then
      match pprintExpr indent env startIdx with (env, startIdx) then
        match pprintExpr indent env endIdx with (env, endIdx) then
          (env, join [array, "[", startIdx, ":", endIdx, "]"])
        else never
      else never
    else never
  | FEConst {val = val} -> (env, pprintConst val)
  | FELam {ident = ident, body = body} ->
    let aindent = pprintIncr indent in
    match pprintVarName env ident with (env, ident) then
      match pprintExpr aindent env body with (env, body) then
        (env, join ["\\", ident, " ->",
                    pprintNewline aindent, body])
      else never
    else never
  | FEApp t ->
    recursive let appseq = lam t.
      match t with FEApp {lhs = lhs, rhs = rhs} then
        snoc (appseq lhs) rhs
      else [t]
    in
    let apps = appseq (FEApp t) in
    match pprintParen indent env (head apps) with (env, fun) then
      let aindent = pprintIncr indent in
      match pprintArgs aindent env (tail apps) with (env, args) then
        (env, join [fun, pprintNewline aindent, args])
      else never
    else never
  | FELet {ident = ident, tyBody = tyBody, body = body, inexpr = inexpr} ->
    let aindent = pprintIncr indent in
    match pprintExpr aindent env body with (env, body) then
      match pprintExpr indent env inexpr with (env, inexpr) then
        match pprintVarName env ident with (env, ident) then
          (env, join ["let ", ident, " =", pprintNewline aindent, body, " in",
                      pprintNewline indent, inexpr])
        else never
      else never
    else never
  | FEIf {cond = cond, thn = thn, els = els} ->
    let aindent = pprintIncr indent in
    match pprintExpr indent env cond with (env, cond) then
      match pprintExpr aindent env thn with (env, thn) then
        match pprintExpr aindent env els with (env, els) then
          (env, join ["if ", cond, " then", pprintNewline aindent, thn,
                      pprintNewline indent, "else", pprintNewline aindent,
                      els])
        else never
      else never
    else never
  | FEForEach {param = param, loopVar = loopVar, seq = seq, body = body} ->
    let aindent = pprintIncr indent in
    match pprintPat indent env param.0 with (env, paramPat) then
      match pprintExpr indent env param.1 with (env, paramExpr) then
        match pprintVarName env loopVar with (env, loopVar) then
          match pprintExpr indent env seq with (env, seq) then
            match pprintExpr aindent env body with (env, body) then
              (env, join ["loop ", paramPat, " = ", paramExpr,
                          " for ", loopVar, " in ", seq, " do",
                          pprintNewline aindent, body])
            else never
          else never
        else never
      else never
    else never
  | FEMatch {target = target, cases = cases} ->
    let aindent = pprintIncr indent in
    let pprintCase = lam env : PprintEnv. lam matchCase : (FutPat, FutExpr).
      match pprintPat indent env matchCase.0 with (env, pat) then
        match pprintExpr aindent env matchCase.1 with (env, expr) then
          (env, join ["case ", pat, " ->", pprintNewline aindent, expr])
        else never
      else never
    in
    match pprintExpr indent env target with (env, target) then
      match mapAccumL pprintCase env cases with (env, cases) then
        (env, join ["match ", target, pprintNewline indent,
                    strJoin (pprintNewline indent) cases])
      else never
    else never
end

lang FutharkPrettyPrint =
  FutharkConstPrettyPrint + FutharkPatPrettyPrint + FutharkTypePrettyPrint +
  FutharkTypeParamPrettyPrint + FutharkExprPrettyPrint

  sem printFutProg =
  | FProg {decls = decls} ->
    let env = pprintEnvEmpty in
    match mapAccumL pprintDecl env decls with (_, decls) then
      strJoin "\n" decls
    else never

  sem pprintDecl (env : PprintEnv) =
  | FDeclFun {ident = ident, entry = entry, typeParams = typeParams,
              params = params, ret = ret, body = body} ->
    let pprintParam = lam env. lam param : (Name, FutType).
      match param with (ident, ty) then
        match pprintVarName env ident with (env, ident) then
          match pprintType 0 env ty with (env, ty) then
            let ty = if eqString ty "" then "" else concat " : " ty in
            (env, join ["(", ident, ty, ")"])
          else never
        else never
      else never
    in
    let entryStr = if entry then "entry" else "let" in
    let bodyIndent = pprintIncr 0 in
    match mapAccumL pprintTypeParam env typeParams with (env, typeParams) then
      match pprintVarName env ident with (env, ident) then
        match mapAccumL pprintParam env params with (env, params) then
          match pprintType 0 env ret with (env, ret) then
            let ret = if eqString ret "" then "" else concat " : " ret in
            match pprintExpr bodyIndent env body with (env, body) then
              (env, join [entryStr, " ", ident,
                          join (map (cons ' ') typeParams),
                          join (map (cons ' ') params), ret, " =",
                          pprintNewline bodyIndent, body])
            else never
          else never
        else never
      else never
    else never
  | FDeclConst {ident = ident, ty = ty, val = val} ->
    let valIndent = pprintIncr 0 in
    match pprintVarName env ident with (env, ident) then
      match pprintType 0 env ty with (env, ty) then
        match pprintExpr valIndent env val with (env, val) then
          (env, join ["let ", ident, " : ", ty, " =",
                      pprintNewline valIndent, val])
        else never
      else never
    else never
  | FDeclType { ident = ident, typeParams = typeParams, ty = ty } ->
    match mapAccumL pprintTypeParam env typeParams with (env, typeParams) then
      match pprintVarName env ident with (env, ident) then
        match pprintType 0 env ty with (env, ty) then
          (env, join ["type ", ident, " ", strJoin " " typeParams, " = ", ty])
        else never
      else never
    else never
end

mexpr

use FutharkPrettyPrint in

let x = nameSym "x" in
let constDecl = FDeclConst {
  ident = x,
  ty = futIntTy_,
  val = futAdd_ (futInt_ 2) (futInt_ 3),
  info = NoInfo ()
} in

let fn = nameSym "recordProj" in
let y = nameSym "y" in
let recordProjDecl = FDeclFun {
  ident = fn,
  entry = false,
  typeParams = [],
  params = [(y, futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)])],
  ret = futIntTy_,
  body = futRecordProj_ (nFutVar_ y) "a",
  info = NoInfo ()
} in

let diffPairs = nameSym "diffPairs" in
let diffPairsA = nameSym "a" in
let diffPairsB = nameSym "b" in
let lamX = nameSym "x" in
let lamY = nameSym "y" in
let diffPairsDecl = FDeclFun {
  ident = diffPairs,
  entry = false,
  typeParams = [],
  params = [
    (diffPairsA, futUnsizedArrayTy_ futIntTy_),
    (diffPairsB, futUnsizedArrayTy_ futIntTy_)
  ],
  ret = futUnsizedArrayTy_ futIntTy_,
  body =
    futMap2_
      (nFutLam_ lamX (nFutLam_ lamY (futSub_ (nFutVar_ lamX) (nFutVar_ lamY))))
      (nFutVar_ diffPairsA)
      (nFutVar_ diffPairsB),
  info = NoInfo ()
} in

let literals = nameSym "literals" in
let literalsDecl = FDeclFun {
  ident = literals,
  entry = false,
  typeParams = [],
  params = [],
  ret = futRecordTy_ [],
  body = futBindall_ [
    uFutLet_ "_int" (futInt_ 4),
    uFutLet_ "_float" (futFloat_ 3.14),
    uFutLet_ "_array" (futArray_ [futInt_ 1, futInt_ 2, futInt_ 0]),
    uFutLet_ "_tuple" (futRecord_ [("0", futInt_ 2), ("1", futInt_ 3)]),
    uFutLet_ "_rec" (futRecord_ [("e", futFloat_ 2.718), ("pi", futFloat_ 3.14)]),
    futUnit_ ()
  ],
  info = NoInfo ()
} in

let arrays = nameSym "arrays" in
let a = nameSym "a" in
let arraysDecl = FDeclFun {
  ident = arrays,
  entry = false,
  typeParams = [],
  params = [],
  ret = futIntTy_,
  body = futBindall_ [
    nuFutLet_ a (futArray_ [futInt_ 1, futInt_ 2, futInt_ 3]),
    futArrayAccess_ (nFutVar_ a) (futInt_ 1)
  ],
  info = NoInfo ()
} in

let get = nameSym "get" in
let a = nameSym "a" in
let n = nameSym "n" in
let seq = nameSym "seq" in
let i = nameSym "i" in
let genericGetDecl = FDeclFun {
  ident = get,
  entry = false,
  typeParams = [FPSize {val = n}, FPType {val = a}],
  params = [(seq, futSizedArrayTy_ (nFutIdentTy_ a) n),
            (i, futIntTy_)],
  ret = nFutIdentTy_ a,
  body = futArrayAccess_ (nFutVar_ seq) (nFutVar_ i),
  info = NoInfo ()
} in

let recordMatch = nameSym "recordMatching" in
let r = nameSym "r" in
let recordMatchDecl = FDeclFun {
  ident = recordMatch,
  entry = false,
  typeParams = [],
  params = [(r, futRecordTy_ [("a", futIntTy_), ("b", futBoolTy_)])],
  ret = futIntTy_,
  body = futMatch_ (nFutVar_ r) [
    (futPrecord_ [("a", futPint_ 4), ("b", futPvarw_ ())], futInt_ 0),
    (futPrecord_ [("a", nFutPvar_ a), ("b", futPbool_ false)], nFutVar_ a),
    (futPrecord_ [("a", nFutPvar_ a), ("b", futPbool_ true)],
      futAdd_ (nFutVar_ a) (futInt_ 1))
  ],
  info = NoInfo ()
} in

let tmp = nameSym "tmp" in
let z = nameSym "z" in
let w = nameSym "w" in
let main = nameSym "main" in
let mainDecl = FDeclFun {
  ident = main,
  entry = true,
  typeParams = [],
  params = [(z, futUnsizedArrayTy_ futIntTy_)],
  ret = futUnsizedArrayTy_ futIntTy_,
  body = futMap_ (nFutLam_ w (futAdd_ (nFutVar_ w) (nFutVar_ x))) (nFutVar_ z),
  info = NoInfo ()} in

let decls = [
  constDecl,
  recordProjDecl,
  diffPairsDecl,
  literalsDecl,
  arraysDecl,
  genericGetDecl,
  recordMatchDecl,
  mainDecl
] in
let prog = FProg {decls = decls} in
-- print (printFutProg prog);
()
