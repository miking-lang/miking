include "ast-builder.mc"
include "common.mc"
include "math.mc"
include "ocaml/pprint.mc"
include "mexpr/record.mc"

let _futReplaceInvalidChar = lam c.
  if isAlphaOrUnderscore c then c
  else if isDigit c then c
  else '_'

let _futEscapeIdentifier = lam str.
  match str with [h] ++ t then
    let h =
      if isAlpha h then [h]
      else if isDigit h then ['v', '_', h]
      else "v_" in
    concat h (map _futReplaceInvalidChar t)
  else "_"

let _futEscapeLabel = lam str.
  match str with [h] ++ t then
    let h =
      if isAlpha h then [h]
      else if isDigit h then [h]
      else "l" in
    concat h (map _futReplaceInvalidChar t)
  else "l"

let futPprintEnvGetStr = lam env. lam id.
  use IdentifierPrettyPrint in
  let id = nameSetStr id (_futEscapeIdentifier (nameGetStr id)) in
  pprintEnvGetStr env id

let futPprintLabelString = lam env. lam sid.
  use IdentifierPrettyPrint in
  let id = nameNoSym (_futEscapeLabel (sidToString sid)) in
  pprintEnvGetStr env id

lang FutharkLiteralSizePrettyPrint = FutharkAst
  sem pprintIntSize : FutIntSize -> String
  sem pprintIntSize =
  | I8 _ -> "i8"
  | I16 _ -> "i16"
  | I32 _ -> "i32"
  | I64 _ -> "i64"
  | U8 _ -> "u8"
  | U16 _ -> "u16"
  | U32 _ -> "u32"
  | U64 _ -> "u64"

  sem pprintFloatSize : FutFloatSize -> String
  sem pprintFloatSize =
  | F32 _ -> "f32"
  | F64 _ -> "f64"
end

lang FutharkConstPrettyPrint = FutharkAst + FutharkLiteralSizePrettyPrint
  -- NOTE(larshum, 2024-01-31): Prints floating-point numbers in a way that is
  -- supported by Futhark. Firstly, we print NaN and infinity as an access into
  -- the appropriate module based on the size of the floating point, as these
  -- are not directly available as literals in Futhark. Secondly, we add a zero
  -- to the end of floating points that are equal to integers due to an
  -- incompatibility between the format used by 'float2string' and the
  -- floating-point format used in Futhark.
  sem futharkFloatToString : Float -> Option FutFloatSize -> String
  sem futharkFloatToString v =
  | sz ->
    let sz = match sz with Some (F32 _) then F32 () else F64 () in
    let szStr = pprintFloatSize sz in
    if neqf v v then
      concat szStr ".nan"
    else if eqf v inf then
      concat szStr ".inf"
    else if eqf v (negf inf) then
      join ["-", szStr, ".inf"]
    else if eqf (subf (int2float (roundfi v)) v) 0.0 then
      join [float2string v, "0", szStr]
    else concat (float2string v) szStr

  sem pprintConst =
  | FCInt t ->
    concat
      (int2string t.val)
      (optionGetOrElse (lam. "") (optionMap pprintIntSize t.sz))
  | FCFloat t ->
    futharkFloatToString t.val t.sz
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
  | FCAnd () -> "(&&)"
  | FCOr () -> "(||)"
  | FCBitAnd () -> "(&)"
  | FCBitOr () -> "(|)"
  | FCBitXor () -> "(^)"
  | FCSrl () -> "(>>)"
  | FCSll () -> "(<<)"
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

lang FutharkPatPrettyPrint = FutharkAst
  sem pprintPatName : PprintEnv -> PatName -> (PprintEnv, String)
  sem pprintPatName env =
  | PName name -> futPprintEnvGetStr env name
  | PWildcard _ -> (env, "_")

  sem pprintPat : Int -> PprintEnv -> FutPat -> (PprintEnv, String)
  sem pprintPat indent env =
  | FPNamed t -> pprintPatName env t.ident
  | FPInt t -> (env, int2string t.val)
  | FPBool t -> (env, if t.val then "true" else "false")
  | FPRecord t ->
    if mapIsEmpty t.bindings then (env, "{}")
    else
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintPat indent env v with (env, str) in
             match futPprintLabelString env k with (env, k) in
             (env, join [k, " = ", str]))
           env t.bindings
      with (env,bindMap) in
      (env,join ["{", strJoin ", " (mapValues bindMap), "}"])
end

lang FutharkTypeParamPrettyPrint = FutharkAst
  sem pprintTypeParam : PprintEnv -> FutTypeParam -> (PprintEnv, String)
  sem pprintTypeParam env =
  | FPSize {val = n} ->
    match futPprintEnvGetStr env n with (env, n) in
    (env, join ["[", n, "]"])
  | FPType {val = n} ->
    match futPprintEnvGetStr env n with (env, n) in
    (env, cons '\'' n)
end

lang FutharkTypePrettyPrint = FutharkLiteralSizePrettyPrint
  sem pprintExpr : Int -> PprintEnv -> FutExpr -> (PprintEnv, String)

  sem pprintArrayDim : PprintEnv -> FutArrayDim -> (PprintEnv, String)
  sem pprintArrayDim env =
  | NamedDim id -> futPprintEnvGetStr env id
  | AbsDim n -> (env, int2string n)

  sem pprintType : Int -> PprintEnv -> FutType -> (PprintEnv, String)
  sem pprintType indent env =
  | FTyUnknown _ -> (env, "")
  | FTyInt t -> (env, pprintIntSize t.sz)
  | FTyFloat t -> (env, pprintFloatSize t.sz)
  | FTyBool _ -> (env, "bool")
  | FTyIdent {ident = ident} -> futPprintEnvGetStr env ident
  | FTyArray {elem = elem, dim = dim} ->
    let pprintDim = lam dim.
      optionMapOrElse (lam. (env, "")) (pprintArrayDim env) dim in
    match pprintDim dim with (env, dimStr) in
    match pprintType indent env elem with (env, elem) in
    (env, join ["[", dimStr, "]", elem])
  | FTyRecord {fields = fields} ->
    let labels = recordOrderedLabels (mapKeys fields) in
    let pprintField = lam env. lam k.
      let ty = mapFindExn k fields in
      match futPprintLabelString env k with (env, str) in
      match pprintType indent env ty with (env, tyStr) in
      (env, join [str, " : ", tyStr])
    in
    match mapAccumL pprintField env labels with (env, fields) in
    (env, join ["{", strJoin "," fields, "}"])
  | FTyProj {target = target, label = label} ->
    match pprintType indent env target with (env, target) in
    match futPprintLabelString env label with (env, label) in
    (env, join [target, ".", label])
  | FTyArrow {from = from, to = to} ->
    match pprintType indent env from with (env, from) in
    match pprintType indent env to with (env, to) in
    (env, join ["(", from, ") -> (", to, ")"])
  | FTyAll {info = info} ->
    errorSingle [info] "Cannot print intermediate TyAll construct"
end

lang FutharkExprPrettyPrint = FutharkAst + FutharkConstPrettyPrint +
                              FutharkPatPrettyPrint + FutharkTypePrettyPrint +
                              PrettyPrint
  sem isAtomic =
  | FEVar _ -> true
  | FEVarExt _ -> true
  | FESizeCoercion _ -> true
  | FEProj _ -> false
  | FERecord _ -> true
  | FERecordUpdate _ -> true
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

  sem pprintParen : Int -> PprintEnv -> FutExpr -> (PprintEnv, String)
  sem pprintParen indent env =
  | expr ->
    let i = if isAtomic expr then indent else addi 1 indent in
    match pprintExpr i env expr with (env, str) in
    if isAtomic expr then (env, str)
    else (env, join ["(", str, ")"])

  sem pprintArgs : Int -> PprintEnv -> [FutExpr] -> (PprintEnv, String)
  sem pprintArgs indent env =
  | exprs ->
    match mapAccumL (pprintParen indent) env exprs with (env, args) in
    (env, strJoin (pprintNewline indent) args)

  sem pprintExpr : Int -> PprintEnv -> FutExpr -> (PprintEnv, String)
  sem pprintExpr indent env =
  | FEVar {ident = ident} -> futPprintEnvGetStr env ident
  | FEVarExt {ident = ident} -> (env, ident)
  | FESizeCoercion {e = e, ty = ty} ->
    match pprintExpr indent env e with (env, e) in
    match pprintType indent env ty with (env, ty) in
    (env, join [e, " :> ", ty])
  | FESizeEquality _ ->
    -- NOTE(larshum, 2021-11-30): These expressions are processed and
    -- eliminated from the AST at an earlier point. As they have no effect on
    -- the evaluation of the program, they are replaced by empty tuples.
    (env, join ["()"])
  | FEProj {target = target, label = label} ->
    match pprintParen indent env target with (env, target) in
    match futPprintLabelString env label with (env, str) in
    (env, join [target, ".", str])
  | FERecord {fields = fields} ->
    let pprintField = lam env. lam k. lam v.
      match futPprintLabelString env k with (env, str) in
      match pprintExpr indent env v with (env, expr) in
      (env, join [str, " = ", expr])
    in
    match mapMapAccum pprintField env fields with (env, fields) in
    (env, join ["{", strJoin "," (mapValues fields), "}"])
  | FERecordUpdate {rec = rec, key = key, value = value} ->
    match pprintParen indent env rec with (env, rec) in
    match futPprintLabelString env key with (env, key) in
    match pprintExpr indent env value with (env, value) in
    (env, join [rec, " with ", key, " = ", value])
  | FEArray {tms = tms} ->
    match mapAccumL (pprintExpr indent) env tms with (env, tms) in
    (env, join ["[", strJoin "," tms, "]"])
  | (FEArrayAccess {array = FEArrayAccess _, index = _}) & t ->
    recursive let indicesAndTarget = lam indices. lam e.
      match e with FEArrayAccess t then
        indicesAndTarget (cons t.index indices) t.array
      else (indices, e)
    in
    match indicesAndTarget [] t with (indices, arrayTarget) in
    match pprintExpr indent env arrayTarget with (env, array) in
    match mapAccumL (pprintExpr indent) env indices with (env, indices) in
    (env, join [array, "[", strJoin "," indices, "]"])
  | FEArrayAccess {array = array, index = index} ->
    match pprintExpr indent env array with (env, array) in
    match pprintExpr indent env index with (env, index) in
    (env, join [array, "[", index, "]"])
  | FEArrayUpdate {array = array, index = index, value = value} ->
    match pprintExpr indent env array with (env, array) in
    match pprintExpr indent env index with (env, index) in
    match pprintExpr indent env value with (env, value) in
    (env, join [array, " with [", index, "] = ", value])
  | FEArraySlice {array = array, startIdx = startIdx, endIdx = endIdx} ->
    match pprintExpr indent env array with (env, array) in
    match pprintExpr indent env startIdx with (env, startIdx) in
    match pprintExpr indent env endIdx with (env, endIdx) in
    (env, join [array, "[", startIdx, ":", endIdx, "]"])
  | FEConst {val = val} -> (env, pprintConst val)
  | FELam {ident = ident, body = body} ->
    let aindent = pprintIncr indent in
    match futPprintEnvGetStr env ident with (env, ident) in
    match pprintExpr aindent env body with (env, body) in
    (env, join ["\\", ident, " ->",
                pprintNewline aindent, body])
  | FEApp t ->
    recursive let appseq = lam t.
      match t with FEApp {lhs = lhs, rhs = rhs} then
        snoc (appseq lhs) rhs
      else [t]
    in
    let apps = appseq (FEApp t) in
    match pprintParen indent env (head apps) with (env, fun) in
    let aindent = pprintIncr indent in
    match pprintArgs aindent env (tail apps) with (env, args) in
    (env, join [fun, pprintNewline aindent, args])
  | FELet {ident = ident, tyBody = tyBody, body = body, inexpr = inexpr} ->
    let aindent = pprintIncr indent in
    match pprintExpr aindent env body with (env, body) in
    match pprintExpr indent env inexpr with (env, inexpr) in
    match futPprintEnvGetStr env ident with (env, ident) in
    (env, join ["let ", ident, " =", pprintNewline aindent, body, " in",
                pprintNewline indent, inexpr])
  | FEIf {cond = cond, thn = thn, els = els} ->
    let aindent = pprintIncr indent in
    match pprintExpr indent env cond with (env, cond) in
    match pprintExpr aindent env thn with (env, thn) in
    match pprintExpr aindent env els with (env, els) in
    (env, join ["if ", cond, " then", pprintNewline aindent, thn,
                pprintNewline indent, "else", pprintNewline aindent,
                els])
  | FEForEach {param = param, loopVar = loopVar, seq = seq, body = body} ->
    let aindent = pprintIncr indent in
    match pprintPat indent env param.0 with (env, paramPat) in
    match pprintExpr indent env param.1 with (env, paramExpr) in
    match futPprintEnvGetStr env loopVar with (env, loopVar) in
    match pprintExpr indent env seq with (env, seq) in
    match pprintExpr aindent env body with (env, body) in
    (env, join ["loop ", paramPat, " = ", paramExpr,
                " for ", loopVar, " in ", seq, " do",
                pprintNewline aindent, body])
  | FEMatch {target = target, cases = cases} ->
    let aindent = pprintIncr indent in
    let pprintCase = lam env : PprintEnv. lam matchCase : (FutPat, FutExpr).
      match pprintPat indent env matchCase.0 with (env, pat) in
      match pprintExpr aindent env matchCase.1 with (env, expr) in
      (env, join ["case ", pat, " ->", pprintNewline aindent, expr])
    in
    match pprintExpr indent env target with (env, target) in
    match mapAccumL pprintCase env cases with (env, cases) in
    (env, join ["match ", target, pprintNewline indent,
                strJoin (pprintNewline indent) cases])
end

lang FutharkPrettyPrint =
  FutharkConstPrettyPrint + FutharkPatPrettyPrint + FutharkTypePrettyPrint +
  FutharkTypeParamPrettyPrint + FutharkExprPrettyPrint

  sem printFutProg : FutProg -> String
  sem printFutProg =
  | FProg {decls = decls} ->
    let env = pprintEnvEmpty in
    match mapAccumL pprintDecl env decls with (_, decls) in
    strJoin "\n" decls

  sem pprintDecl : PprintEnv -> FutDecl -> (PprintEnv, String)
  sem pprintDecl env =
  | FDeclFun {ident = ident, entry = entry, typeParams = typeParams,
              params = params, ret = ret, body = body} ->
    let pprintParam = lam env. lam param : (Name, FutType).
      match param with (ident, ty) in
      match futPprintEnvGetStr env ident with (env, ident) in
      match pprintType 0 env ty with (env, ty) in
      let ty = if eqString ty "" then "" else concat " : " ty in
      (env, join ["(", ident, ty, ")"])
    in
    let entryStr = if entry then "entry" else "let" in
    let bodyIndent = pprintIncr 0 in
    match mapAccumL pprintTypeParam env typeParams with (env, typeParams) in
    match futPprintEnvGetStr env ident with (env, ident) in
    match mapAccumL pprintParam env params with (env, params) in
    match pprintType 0 env ret with (env, ret) in
    let ret = if eqString ret "" then "" else concat " : " ret in
    match pprintExpr bodyIndent env body with (env, body) in
    (env, join [entryStr, " ", ident,
                join (map (cons ' ') typeParams),
                join (map (cons ' ') params), ret, " =",
                pprintNewline bodyIndent, body])
  | FDeclConst {ident = ident, ty = ty, val = val} ->
    let valIndent = pprintIncr 0 in
    match futPprintEnvGetStr env ident with (env, ident) in
    match pprintType 0 env ty with (env, ty) in
    match pprintExpr valIndent env val with (env, val) in
      (env, join ["let ", ident, " : ", ty, " =",
                  pprintNewline valIndent, val])
  | FDeclType { ident = ident, typeParams = typeParams, ty = ty } ->
    match mapAccumL pprintTypeParam env typeParams with (env, typeParams) in
    match futPprintEnvGetStr env ident with (env, ident) in
    match pprintType 0 env ty with (env, ty) in
    let typarams =
      if null typeParams then ""
      else cons ' ' (strJoin " " typeParams)
    in
    (env, join ["type ", ident, typarams, " = ", ty])
  | FDeclModuleAlias { ident = ident, moduleId = moduleId } ->
    match futPprintEnvGetStr env ident with (env, ident) in
    (env, join ["module ", ident, " = ", moduleId])
end

mexpr

use FutharkPrettyPrint in

utest futharkFloatToString 0.0 (None ()) with "0.0f64" in
utest futharkFloatToString 0.0 (Some (F32 ())) with "0.0f32" in
utest futharkFloatToString 0.0 (Some (F64 ())) with "0.0f64" in
utest futharkFloatToString inf (None ()) with "f64.inf" in
utest futharkFloatToString inf (Some (F32 ())) with "f32.inf" in
utest futharkFloatToString inf (Some (F64 ())) with "f64.inf" in
utest futharkFloatToString (negf inf) (None ()) with "-f64.inf" in
utest futharkFloatToString (negf inf) (Some (F32 ())) with "-f32.inf" in
utest futharkFloatToString (negf inf) (Some (F64 ())) with "-f64.inf" in
utest futharkFloatToString nan (None ()) with "f64.nan" in
utest futharkFloatToString nan (Some (F32 ())) with "f32.nan" in
utest futharkFloatToString nan (Some (F64 ())) with "f64.nan" in

let printDecl = lam decl.
  let prog = FProg {decls = [decl]} in
  printFutProg prog in

let x = nameSym "x" in
let constDecl = FDeclConst {
  ident = x,
  ty = futIntTy_,
  val = futAdd_ (futInt_ 2) (futInt_ 3),
  info = NoInfo ()
} in
utest printDecl constDecl with strJoin "\n" [
  "let x : i64 =",
  "  (+)",
  "    2i64",
  "    3i64"
] in

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
utest printDecl recordProjDecl with strJoin "\n" [
  "let recordProj (y : {a : i64,b : f64}) : i64 =",
  "  y.a"
] in

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
utest printDecl diffPairsDecl with strJoin "\n" [
  "let diffPairs (a : []i64) (b : []i64) : []i64 =",
  "  map2",
  "    (\\x ->",
  "       \\y ->",
  "         (-)",
  "           x",
  "           y)",
  "    a",
  "    b"
] in

let literals = nameSym "literals" in
let literalsDecl = FDeclFun {
  ident = literals,
  entry = false,
  typeParams = [],
  params = [],
  ret = futRecordTy_ [],
  body = futBindall_ [
    uFutLet_ "int" (futInt_ 4),
    uFutLet_ "float" (futFloat_ 3.14),
    uFutLet_ "array" (futArray_ [futInt_ 1, futInt_ 2, futInt_ 0]),
    uFutLet_ "tuple" (futRecord_ [("0", futInt_ 2), ("1", futInt_ 3)]),
    uFutLet_ "rec" (futRecord_ [("e", futFloat_ 2.718), ("pi", futFloat_ 3.14)]),
    futUnit_ ()
  ],
  info = NoInfo ()
} in
utest printDecl literalsDecl with strJoin "\n" [
  "let literals : {} =",
  "  let int =",
  "    4i64 in",
  "  let float =",
  "    3.14f64 in",
  "  let array =",
  "    [1i64,2i64,0i64] in",
  "  let tuple =",
  "    {0 = 2i64,1 = 3i64} in",
  "  let rec =",
  "    {e = 2.718f64,pi = 3.14f64} in",
  "  {}"
] in

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
utest printDecl arraysDecl with strJoin "\n" [
  "let arrays : i64 =",
  "  let a =",
  "    [1i64,2i64,3i64] in",
  "  a[1i64]"
] in

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
utest printDecl genericGetDecl with strJoin "\n" [
  "let get [n] 'a (seq : [n]a) (i : i64) : a =",
  "  seq[i]"
] in

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
utest printDecl recordMatchDecl with strJoin "\n" [
  "let recordMatching (r : {a : i64,b : bool}) : i64 =",
  "  match r",
  "  case {a = 4, b = _} ->",
  "    0i64",
  "  case {a = a1, b = false} ->",
  "    a1",
  "  case {a = a1, b = true} ->",
  "    (+)",
  "      a1",
  "      1i64"
] in

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
utest printDecl mainDecl with strJoin "\n" [
  "entry main (z : []i64) : []i64 =",
  "  map",
  "    (\\w ->",
  "       (+)",
  "         w",
  "         x)",
  "    z"
] in

let escapingDecl = FDeclConst {
  ident = nameSym "a*b+c",
  ty = futIntTy_,
  val = futAdd_ (futMul_ (futInt_ 2) (futInt_ 3)) (futInt_ 4),
  info = NoInfo ()} in
utest printDecl escapingDecl with strJoin "\n" [
  "let a_b_c : i64 =",
  "  (+)",
  "    ((*)",
  "       2i64",
  "       3i64)",
  "    4i64"
] in

let x = nameSym "x" in
let extDecl = FDeclFun {
  ident = nameSym "sin",
  entry = false,
  typeParams = [],
  params = [(x, futFloatTy_)],
  ret = futFloatTy_,
  body = futApp_ (futVarExt_ "f64.sin") (nFutVar_ x),
  info = NoInfo ()} in
utest printDecl extDecl with strJoin "\n" [
  "let sin (x : f64) : f64 =",
  "  f64.sin",
  "    x"
] in

()
