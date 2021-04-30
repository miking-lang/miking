include "ast.mc"
include "common.mc"
include "mexpr/pprint.mc"

let isValidChar = lam c.
  or (isAlpha c) (eqChar c '_')

let escapeChar = lam c.
  if isValidChar c then c else '_'

utest map escapeChar "abc1_'@x+Yz" with "abc__'_x_Yz"

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
  concat "l" (map escapeChar s)

utest escapeFutharkLabelString "abc" with "labc"
utest escapeFutharkLabelString "abc123" with "labc___"
utest escapeFutharkLabelString "0" with "l_"
utest escapeFutharkLabelString "a'b/c" with "la'b_c"

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
    (env, join ["[", dimStr, "]", pprintType 0 env elem])
  | FTyRecord {fields = fields} ->
    let pprintField = lam env. lam k. lam ty.
      let str = pprintLabelString k in
      match pprintExpr indent env ty with (env, tyStr) then
        (env, join [str, " : ", tyStr])
      else never
    in
    match mapMapAccum pprintField env fields with (env, fields) then
      (env, join ["{", strJoin "," fields, "}"])
    else never

  sem pprintExpr (indent : Int) (env : PprintEnv) =
  | FEVar {ident = ident} ->
    pprintVarName env ident
  | FEInt64 {val = val} ->
    (env, join [int2string val, "i64"])
  | FEFloat64 {val = val} ->
    (env, join [float2string val, "f64"])
  | FERecord {fields = fields} ->
    let pprintField = lam env. lam k. lam v.
      let str = pprintLabelString k in
      match pprintExpr indent env v with (env, expr) then
        (env, join [str, " = ", expr])
      else never
    in
    match mapMapAccum pprintField env fields with (env, fields) then
      (env, join ["{", strJoin "," fields, "}"])
    else never
  | FEArray {tms = tms} ->
    match mapAccumL pprintExpr indent env tms with (env, tms) then
      (env, join ["[", strJoin "," tms, "]"])
    else never
  | FEConst {val = val} ->
    (env, pprintConst val)
  | FELam {ident = ident, body = body} ->
    let aindent = pprintIncr indent in
    match pprintVarName env ident with (env, str) then
      match pprintExpr aindent env body with (env, body) then
        (env, join ["\\", ident, " ->", pprintNewline aindent, body])
      else never
    else never
  | FEApp {lhs = lhs, rhs = rhs} ->
    match pprintExpr indent env lhs with (env, lhs) then
      match pprintExpr indent env rhs with (env, rhs) then
        (env, join [lhs, " ", rhs])
      else never
    else never
  | FELet {ident = ident, body = body, inexpr = inexpr} ->
    let aindent = pprintIncr indent in
    match pprintExpr aindent env body with (env, body) then
      match pprintExpr indent env inexpr with (env, inexpr) then
        (env, join ["let ", pprintEnvGetStr env ident, " =",
                    pprintNewline aindent, body, " in",
                    pprintNewline indent, inexpr])
      else never
    else never

  sem pprintConst =
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
end

mexpr

use FutharkPrettyPrint in

let int64Type = FTyIdent {ident = nameSym "i64"} in
let x = nameSym "x" in
let y = nameSym "y" in
let main = nameSym "main" in
let prog = FProg {
  decls = [
    FDeclConst {
      ident = x,
      ty = int64Type,
      val = FEApp {
        lhs = FEConst {val = FCAdd ()},
        rhs = FEApp {
          lhs = FEInt64 {val = 2},
          rhs = FEInt64 {val = 3}
        }
      }
    },
    FDeclFun {
      ident = main,
      entry = true,
      params = [(y, int64Type)],
      ret = int64Type,
      body = FEApp {
        lhs = FEConst {val = FCAdd ()},
        rhs = FEApp {
          lhs = FEVar {ident = x},
          rhs = FEVar {ident = y}
        }
      }
    }
  ]
} in
print (expr2str prog)
