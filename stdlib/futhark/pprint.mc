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
utest escapeFutharkLabelString "0" with "l_"
utest escapeFutharkLabelString "a'b/c" with "la_b_c"

lang FutharkIdentifierPrettyPrint = IdentifierPrettyPrint
  sem pprintConName (env : PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env, str) then
      let s = escapeFutharkConString str in
      (env, s)
    else never

  sem pprintVarName (env : PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env, str) then
      let s = escapeFutharkVarString str in
      (env, s)
    else never

  sem pprintLabelString =
  | sid -> escapeFutharkLabelString (sidToString sid)
end

lang FutharkPrettyPrint = FutharkAst + FutharkIdentifierPrettyPrint
  sem expr2str =
  | FProg {decls = decls} ->
    let env = pprintEnvEmpty in
    match mapAccumL pprintDecl env decls with (_, decls) then
      strJoin "\n" decls
    else never

  sem pprintDecl (env : PprintEnv) =
  | FDeclFun {ident = ident, entry = entry, params = params,
              ret = ret, body = body} ->
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
    match pprintVarName env ident with (env, ident) then
      match mapAccumL pprintParam env params with (env, params) then
        match pprintType 0 env ret with (env, ret) then
          match pprintExpr bodyIndent env body with (env, body) then
            (env, join [entryStr, " ", ident, " ", strJoin " " params, " : ",
                        ret, " =", pprintNewline bodyIndent,
                        body])
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

  sem pprintType (indent : Int) (env : PprintEnv) =
  | FTyIdent {ident = ident} -> pprintEnvGetStr env ident
  | FTyArray {elem = elem, dim = dim} ->
    let dimStr = optionMapOrElse (lam. "") int2string dim in
    match pprintType indent env elem with (env, elem) then
      (env, join ["[", dimStr, "]", elem])
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

  sem pprintExpr (indent : Int) (env : PprintEnv) =
  | FEVar {ident = ident} ->
    pprintVarName env ident
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
  | FEConst {val = val} ->
    (env, pprintConst val)
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
    match pprintExpr indent env (head apps) with (env, fun) then
      let aindent = pprintIncr indent in
      match mapAccumL (pprintExpr aindent) env (tail apps) with (env, args) then
        (env, join [fun, pprintNewline aindent, strJoin (pprintNewline aindent) args])
      else never
    else never
  | FELet {ident = ident, body = body, inexpr = inexpr} ->
    let aindent = pprintIncr indent in
    match pprintExpr aindent env body with (env, body) then
      match pprintExpr indent env inexpr with (env, inexpr) then
        match pprintEnvGetStr env ident with (_, ident) then
          (env, join ["let ", ident, " = ", body, " in",
                      pprintNewline indent, inexpr])
        else never
      else never
    else never

  sem pprintConst =
  | FCInt {val = val} -> join [int2string val, "i64"]
  | FCFloat {val = val} -> join [float2string val, "f64"]
  | FCAdd () -> "(+)"
  | FCSub () -> "(-)"
  | FCMul () -> "(*)"
  | FCDiv () -> "(/)"
  | FCRem () -> "(%)"
  | FCEq () -> "(=)"
  | FCNeq () -> "(!)"
  | FCGt () -> "(>)"
  | FCLt () -> "(<)"
  | FCAnd () -> "(&)"
  | FCOr () -> "(|)"
  | FCXor () -> "(^)"
  | FCMap () -> "map"
  | FCMap2 () -> "map2"
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

let tmp = nameSym "tmp" in
let z = nameSym "z" in
let w = nameSym "w" in
let main = nameSym "main" in
let mainDecl = FDeclFun {
  ident = main,
  entry = true,
  params = [(z, futUnsizedArrayTy_ futIntTy_)],
  ret = futUnsizedArrayTy_ futIntTy_,
  body = futMap_ (nFutLam_ w (futAdd_ (nFutVar_ w) (nFutVar_ x))) (nFutVar_ z)} in

let decls = [
  constDecl,
  recordProjDecl,
  diffPairsDecl,
  literalsDecl,
  mainDecl
] in
let prog = FProg {decls = decls} in
-- print (expr2str prog);
()
