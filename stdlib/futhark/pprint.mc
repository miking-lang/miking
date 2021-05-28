include "ast-builder.mc"
include "common.mc"
include "mexpr/pprint.mc"

let isValidChar = lam c.
  or (isAlpha c) (eqChar c '_')

let escapeChar = lam c.
  if isValidChar c then c else '_'

utest map escapeChar "abc1_'@x+Yz" with "abc____x_Yz"

let escapeFutharkConString = lam s.
  concat "#_" (map escapeChar s)

utest escapeFutharkConString "abc" with "#_abc"
utest escapeFutharkConString "123" with "#____"
utest escapeFutharkConString "" with "#_"
utest escapeFutharkConString "@bC1two3" with "#__bC_two_"

let escapeFutharkVarString = lam s.
  concat "v_" (map escapeChar s)

utest escapeFutharkVarString "x" with "v_x"
utest escapeFutharkVarString "" with "v_"
utest escapeFutharkVarString "_" with "v__"
utest escapeFutharkVarString "abc123" with "v_abc___"

let escapeFutharkLabelString = lam s.
  if stringIsInt s then
    s
  else
    concat "l" (map escapeChar s)

utest escapeFutharkLabelString "abc" with "labc"
utest escapeFutharkLabelString "abc123" with "labc___"
utest escapeFutharkLabelString "0" with "0"
utest escapeFutharkLabelString "a'b/c" with "la_b_c"

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

let pprintEnvGetFutharkStr : PprintEnv -> Name -> (PprintEnv, String) =
  lam env : PprintEnv. lam name.
    -- Translate the numerical index into one or a sequence of lower-case ASCII
    -- characters. We need to do this for Futhark because it does not allow
    -- integers in names.
    recursive let index2string = lam str. lam i.
      let ch = int2char (addi (modi i 26) (char2int 'a')) in
      let str = cons ch str in
      if lti i 26 then str
      else index2string str (subi (divi i 26) 1)
    in
    match pprintEnvLookup name env with Some str then (env,str)
    else
      let baseStr = nameGetStr name in
      if pprintEnvFree baseStr env then (pprintEnvAdd name baseStr 1 env, baseStr)
      else
        match env with {count = count} then
          let start =
            match mapLookup baseStr count
            with Some i then i else 1 in
          recursive let findFree : String -> Int -> (String, Int) =
            lam baseStr. lam i.
              let proposal = concat baseStr (index2string "" (subi i 1)) in
              if pprintEnvFree proposal env then (proposal, i)
              else findFree baseStr (addi i 1)
          in
          match findFree baseStr start with (str, i) then
            (pprintEnvAdd name str (addi i 1) env, str)
          else never
        else never

lang FutharkIdentifierPrettyPrint = IdentifierPrettyPrint
  sem pprintConName (env : PprintEnv) =
  | name ->
    match pprintEnvGetFutharkStr env name with (env, str) then
      let s = escapeFutharkConString str in
      (env, s)
    else never

  sem pprintVarName (env : PprintEnv) =
  | name ->
    match pprintEnvGetFutharkStr env name with (env, str) then
      let s = escapeFutharkVarString str in
      (env, s)
    else never

  sem pprintLabelString =
  | sid -> escapeFutharkLabelString (sidToString sid)
end

lang FutharkConstPrettyPrint = FutharkAst
  sem pprintConst =
  | FCInt {val = val} -> join [int2string val, "i64"]
  | FCFloat {val = val} -> join [futharkFloat2string val, "f64"]
  | FCAdd () -> "(+)"
  | FCSub () -> "(-)"
  | FCMul () -> "(*)"
  | FCDiv () -> "(/)"
  | FCRem () -> "(%)"
  | FCEq () -> "(=)"
  | FCNeq () -> "(!)"
  | FCGt () -> "(>)"
  | FCLt () -> "(<)"
  | FCGeq () -> "(>=)"
  | FCLeq () -> "(<=)"
  | FCAnd () -> "(&)"
  | FCOr () -> "(|)"
  | FCXor () -> "(^)"
  | FCMap () -> "map"
  | FCMap2 () -> "map2"
  | FCReduce () -> "reduce"
  | FCScan () -> "scan"
  | FCFilter () -> "filter"
  | FCPartition () -> "partition"
  | FCAll () -> "all"
  | FCAny () -> "any"
end

lang FutharkTypePrettyPrint = FutharkAst + FutharkIdentifierPrettyPrint
  sem pprintExpr (indent : Int) (env : PprintEnv) =

  sem pprintType (indent : Int) (env : PprintEnv) =
  | FTyInt _ -> (env, "i64")
  | FTyFloat _ -> (env, "f64")
  | FTyIdent {ident = ident} -> pprintVarName env ident
  | FTyArray {elem = elem, dim = dim} ->
    let pprintDim = lam dim.
      optionMapOrElse (lam. (env, "")) (pprintExpr indent env) dim
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

lang FutharkExprPrettyPrint = FutharkAst + FutharkConstPrettyPrint +
                              FutharkTypePrettyPrint
  sem isAtomic =
  | FEVar _ -> true
  | FEBuiltIn _ -> true
  | FERecord _ -> true
  | FERecordProj _ -> false
  | FEArray _ -> true
  | FEArrayAccess _ -> false
  | FEConst _ -> true
  | FELam _ -> false
  | FEApp _ -> false
  | FELet _ -> false
  | FEIf _ -> false

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
  | FEBuiltIn {str = str} -> (env, str)
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
    match pprintExpr indent env rec with (env, rec) then
      let str = pprintLabelString key in
      (env, join [rec, ".", str])
    else never
  | FEArray {tms = tms} ->
    match mapAccumL (pprintExpr indent) env tms with (env, tms) then
      (env, join ["[", strJoin "," tms, "]"])
    else never
  | FEArrayAccess {array = array, index = index} ->
    match pprintExpr indent env array with (env, array) then
      match pprintExpr indent env index with (env, index) then
        (env, join [array, "[", index, "]"])
      else never
    else never
  | FEConst {val = val} -> (env, pprintConst val)
  | FELam {idents = idents, body = body} ->
    let aindent = pprintIncr indent in
    match mapAccumL pprintVarName env idents with (env, strs) then
      match pprintExpr aindent env body with (env, body) then
        (env, join ["(\\", strJoin " " strs, " ->",
                    pprintNewline aindent, body, ")"])
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
      match pprintType indent env tyBody with (env, tyBody) then
        match pprintExpr indent env inexpr with (env, inexpr) then
          match pprintVarName env ident with (_, ident) then
            (env, join ["let ", ident, " : ", tyBody, " = ", body, " in",
                        pprintNewline indent, inexpr])
          else never
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
end

lang FutharkPrettyPrint = FutharkConstPrettyPrint + FutharkTypePrettyPrint +
                          FutharkTypeParamPrettyPrint + FutharkExprPrettyPrint
  sem expr2str =
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
            (env, join ["(", ident, " : ", ty, ")"])
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
            match pprintExpr bodyIndent env body with (env, body) then
              (env, join [entryStr, " ", ident, " ", strJoin " " typeParams,
                          " ", strJoin " " params, " : ", ret, " =",
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
  val = futAdd_ (futInt_ 2) (futInt_ 3)
} in

let fn = nameSym "recordProj" in
let y = nameSym "y" in
let recordProjDecl = FDeclFun {
  ident = fn,
  entry = false,
  typeParams = [],
  params = [(y, futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)])],
  ret = futIntTy_,
  body = futRecordProj_ (nFutVar_ y) "a"
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
      (nFutLams_ [lamX, lamY] (futSub_ (nFutVar_ lamX) (nFutVar_ lamY)))
      (nFutVar_ diffPairsA)
      (nFutVar_ diffPairsB)
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
  ]
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
  ]
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
  params = [(seq, futSizedArrayTy_ (nFutVar_ n) (nFutIdentTy_ a)),
            (i, futIntTy_)],
  ret = nFutIdentTy_ a,
  body = futArrayAccess_ (nFutVar_ seq) (nFutVar_ i)
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
  body = futMap_ (nFutLam_ w (futAdd_ (nFutVar_ w) (nFutVar_ x))) (nFutVar_ z)} in

let decls = [
  constDecl,
  recordProjDecl,
  diffPairsDecl,
  literalsDecl,
  arraysDecl,
  genericGetDecl,
  mainDecl
] in
let prog = FProg {decls = decls} in
-- print (expr2str prog);
()
