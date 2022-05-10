-- Pretty printing for JavaScript fragments.

include "javascript/ast.mc"
include "string.mc"
include "char.mc"

include "mexpr/pprint.mc"


-------------
-- HELPERS --
-------------

-- All helpers are directly taken from pprint.mc for C.
-- Surrounds a string with parentheses
let _par = lam str. join ["(",str,")"]

let pprintEnvGetStr = lam env. lam id: Name.
  -- Set this to true to print names with their symbols (for debugging)
  if false then
    (env,join [
      nameGetStr id,
      match nameGetSym id with Some sym then int2string (sym2hash sym) else ""
    ])
  else
    let id = nameSetStr id (nameGetStr id) in
    pprintEnvGetStr env id -- Note that this is not a recursive call!

-- Similar to pprintEnvGetStr in mexpr/pprint.mc, but takes an Option Name as
-- argument. If it is None (), the returned string is "".
let pprintEnvGetOptStr = lam env. lam id.
  match id with Some id then pprintEnvGetStr env id else (env,"")

--------------
-- KEYWORDs --
--------------

-- From Draft ECMA-262 / March 3, 2022 (https://tc39.es/ecma262/#sec-keywords-and-reserved-words)
let jsKeywords = [
    "await", "break", "case", "catch", "class", "const", "continue",
    "debugger", "default", "delete", "do", "else", "enum", "export",
    "extends", "false", "finally", "for", "function", "if", "import",
    "in", "instanceof", "new", "null", "undefined", "return", "super", "switch",
    "this", "throw", "true", "try", "typeof", "var", "void", "while",
    "with", "yield", "function",
    -- Extra reserved words (Not in spec)
    "console", "document", "window", "global", "localStorage", "sessionStorage",
    "location", "navigator", "history"
]



----------------------------
-- JavaScript EXPRESSIONS --
----------------------------
lang JSExprPrettyPrint = JSExprAst

  sem printJSDef (indent: Int) (env: PprintEnv) (id: String) =
  | expr -> (env, join [pprintNewline indent, "let ", id, " = ", printJSExpr expr])

  sem printJSExprs (indent: Int) (env: PprintEnv) =
  | exprs ->
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) then
      (env, strJoin (pprintNewline indent) exprs)
    else never

  sem printJSExpr (indent : Int) (env: PprintEnv) =
  | JSEVar { id = id } -> pprintEnvGetStr env id
  | JSEApp { fun = fun, args = args } ->
    match (printJSExpr indent) env fun with (env,fun) then
      match mapAccumL (printJSExpr indent) env args with (env,args) then
        (env, join [fun, "(", (strJoin ", " args), ")"])
      else never
    else never
  | JSEMember { expr = expr, id = id } ->
    match (printJSExpr indent) env expr with (env,expr) then
      match (pprintEnvGetStr env id) with (env,id) then
        (env, join [expr, ".", id])
      else never
    else never
  | JSEDef { id = id, expr = expr } ->
    match pprintEnvGetOptStr env id with (env,id) then
      match printJSDef indent env id expr with (env,str) then
        (env, join [str, ";"])
      else never
    else never

  | JSEFun { param = param, body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match (printJSExpr ii) env body with (env,body) then
      (env, "function() { return 42; }")
      -- (env, join ["function (", param, ") {", pprintNewline ii, body, pprintNewline i, "}"])
    else never

  | JSEInt   { i = i } -> (env, int2string i)
  | JSEFloat { f = f } -> (env, float2string f)
  | JSEBool  { b = b } -> (env, if b then "true" else "false")
  | JSEChar  { c = c } -> (env, ['\'', c, '\''])

  | JSEString { s = s } -> (env, join ["\"", escapeString s, "\""])

  | JSEBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match (printJSExpr indent) env lhs with (env,lhs) then
      match (printJSExpr indent) env rhs with (env,rhs) then
        (env, _par (printJSBinOp lhs rhs op))
      else never
    else never

  | JSEUnOp { op = op, rhs = rhs } ->
    match (printJSExpr indent) env rhs with (env,rhs) then
      (env, _par (printJSUnOp rhs op))
    else never

  | JSESeq { exprs = exprs, info = info } ->
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) then
      (env, join ["[", strJoin ", " exprs, "]"])
    else never

  sem printJSBinOp (lhs: String) (rhs: String) =
  | JSOAssign    {} -> join [lhs, " = ", rhs]
  | JSOSubScript {} -> join [lhs, "[", rhs, "]"]
  | JSOOr        {} -> join [lhs, " || ", rhs]
  | JSOAnd       {} -> join [lhs, " && ", rhs]
  | JSOEq        {} -> join [lhs, " == ", rhs]
  | JSONeq       {} -> join [lhs, " != ", rhs]
  | JSOLt        {} -> join [lhs, " < ", rhs]
  | JSOGt        {} -> join [lhs, " > ", rhs]
  | JSOLe        {} -> join [lhs, " <= ", rhs]
  | JSOGe        {} -> join [lhs, " >= ", rhs]
  | JSOAdd       {} -> join [lhs, " + ", rhs]
  | JSOSub       {} -> join [lhs, " - ", rhs]
  | JSOMul       {} -> join [lhs, " * ", rhs]
  | JSODiv       {} -> join [lhs, " / ", rhs]
  | JSOMod       {} -> join [lhs, " % ", rhs]

  sem printJSUnOp (arg: String) =
  | JSONeg       {} -> join ["-", arg]
  | JSONot       {} -> join ["!", arg]

end



------------------------
-- JavaScript PROGRAM --
------------------------
lang JSProgPrettyPrint = JSProgAst + JSExprPrettyPrint

  sem printJSProg =
  | JSPProg { imports = imports, exprs = exprs } ->
    let indent = 0 in
    let imports = map (lam imp. join ["import '", imp, "';"]) imports in
    let env = pprintEnvEmpty in
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) then
      let importsStr = strJoin "\n" imports in
      let exprsStr = strJoin (pprintNewline indent) exprs in
      join [importsStr, exprsStr]
    else never

end
