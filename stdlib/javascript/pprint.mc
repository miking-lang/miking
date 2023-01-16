-- Pretty printing for JavaScript fragments.

include "javascript/ast.mc"
include "string.mc"
include "char.mc"

include "mexpr/pprint.mc"


-------------
-- HELPERS --
-------------


let pprintEnvGetStr = lam env. lam id: Name.
  use IdentifierPrettyPrint in
  -- Set this to true to print names with their symbols (for debugging)
  if false then
    (env,join [
      nameGetStr id,
      match nameGetSym id with Some sym then int2string (sym2hash sym) else ""
    ])
  else
    pprintEnvGetStr env id -- Note that this is not a recursive call!

let joinAsStatements = lam indent. lam seq.
  if null seq then ""
  else join [pprintNewline indent, (strJoin (concat ";" (pprintNewline indent)) seq), ";"]


let getNameStrDefault =  lam default: String.lam env. lam id: Name.
  if null (nameGetStr id) then (env, default)
  else if stringIsInt (nameGetStr id) then
    match pprintEnvGetStr env id with (env, str) in
    (env, cons 'd' str)
  else pprintEnvGetStr env id


--------------
-- KEYWORDS --
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



-------------------------------------------
-- JavaScript EXPRESSIONS and STATEMENTS --
-------------------------------------------
lang JSPrettyPrint = JSExprAst

  sem printJSExprs : Int -> PprintEnv -> [JSExpr] -> (PprintEnv, String)
  sem printJSExprs indent env =
  | exprs ->
    match mapAccumL (printJSExpr indent) env exprs with (env, exprs) in
    (env, strJoin (pprintNewline indent) exprs)


  sem printJSFunParams : PprintEnv -> Bool -> [Name] -> (PprintEnv, String)
  sem printJSFunParams env curried =
  | params ->
    if curried then
      match mapAccumL (getNameStrDefault "()") env params with (env, params) in
      (env, strJoin " => " params)
    else
      match mapAccumL (getNameStrDefault "_") env params with (env, params) in
      (env, join ["(", strJoin ", " params, ")"])

  sem printJSFunApp : PprintEnv -> Bool -> JSExpr -> [JSExpr] -> (PprintEnv, String)
  sem printJSFunApp env curried fun =
  | args ->
    match (printJSExpr 0) env fun with (env, fun) in
    match mapAccumL (printJSExpr 0) env args with (env, args) in
    let sep = if curried then strJoin ")(" else strJoin ", " in
    (env, join [fun, "(", sep args, ")"])

  sem printJSValue : Int -> PprintEnv -> JSExpr -> (PprintEnv, String)
  sem printJSValue indent env =
  | JSEObject _ & e ->
    match printJSExpr indent env e with (env, s) in
    (env, join ["(", s, ")"])
  | e -> printJSExpr indent env e

  sem printJSExpr : Int -> PprintEnv -> JSExpr -> (PprintEnv, String)
  sem printJSExpr indent env =
  | JSEVar { id = id } -> getNameStrDefault "_" env id
  | JSEApp { fun = fun, args = args, curried = curried } ->
    printJSFunApp env curried fun args
  | JSEMember { expr = expr, id = id } ->
    match (printJSExpr indent) env expr with (env,expr) in
    (env, join [expr, ".", id])
  | JSEIndex { expr = expr, index = index } ->
    match (printJSExpr indent) env expr with (env,expr) in
    (env, join [expr, "[", index, "]"])
  | JSEDef { id = id, expr = expr } ->
    match getNameStrDefault "_" env id with (env,id) in
    match (printJSExpr indent env) expr with (env, str) in
    (env, join ["const ", id, " = ", str])
  | JSEDec { ids = ids } ->
    match mapAccumL (getNameStrDefault "_") env ids with (env, idents) in
    (env, join ["let ", strJoin ", " idents])

  -- ES6 arrow functions (released 2015)
  -- https://en.wikipedia.org/wiki/ECMAScript#6th_Edition_%E2%80%93_ECMAScript_2015
  -- Comparison to anonymous functions:
  -- https://dmitripavlutin.com/differences-between-arrow-and-regular-functions
  | JSEFun { params = params, body = body } ->
    let i = indent in
    match (printJSFunParams env true params) with (env, args) in
    match printJSValue i env body with (env,body) in
    (env, join [args, " => ", body])
  | JSEIIFE { body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match (printJSExpr ii) env body with (env,body) in
    (env, join ["(() => ", body, ")()"])

  | JSEInt   { i = i } -> (env, int2string i)
  | JSEFloat { f = f } -> (env, float2string f)
  | JSEBool  { b = b } -> (env, if b then "true" else "false")
  | JSEChar  { c = c } -> (env, join ["'", escapeChar c, "'"])
  | JSEString { s = s } -> (env, join ["\"", escapeString s, "\""])

  | JSETernary { cond = cond, thn = thn, els = els } ->
    let i = indent in
    match (printJSExpr 0 env) cond with (env, cond) in
    match printJSValue i env thn with (env, thn) in
    match printJSValue i env els with (env, els) in
    (env, join ["(", cond, " ? ", thn, " : ", els, ")"])
  | JSEBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match (printJSExpr indent) env lhs with (env,lhs) in
    match (printJSExpr indent) env rhs with (env,rhs) in
    (env, join ["(", printJSBinOp lhs rhs op, ")"])

  | JSEUnOp { op = op, rhs = rhs } ->
    match (printJSExpr indent) env rhs with (env,rhs) in
    (env, printJSUnOp rhs op)

  | JSEArray { exprs = exprs } ->
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) in
    (env, join ["[", strJoin ", " exprs, "]"])
  | JSEObject { fields = fields } ->
    let printPair = lam env. lam field.
      match field with (n, e) in
      match (printJSExpr 0) env e with (env,e) in
      (env, join [n, ": ", e])
    in
    match mapAccumL printPair env fields with (env, prs) in
    (env, join ["{", strJoin ", " prs, "}"])
  | JSEBlock { exprs = exprs, ret = ret } ->
    let i = indent in
    let ii = pprintIncr indent in
    match mapAccumL (printJSExpr ii) env exprs with (env, exprs) in
    let ret = match (printJSExpr 0 env) ret with (env, val) then
        match val with "" then ""
        else join [pprintNewline ii, "return ", val, ";"]
      else "" in
    (env, join ["{",
      joinAsStatements ii exprs,
      ret,
      pprintNewline i, "}"])
  | JSEReturn { expr = expr } ->
    match (printJSExpr indent) env expr with (env,expr) in
    (env, join ["return ", expr])
  | JSENop _ -> (env, "")

  sem printJSBinOp : String -> String -> JSBinOp -> String
  sem printJSBinOp lhs rhs =
  | JSOAssign    {} -> join [lhs, " = ", rhs]
  | JSOSubScript {} -> join [lhs, "[", rhs, "]"]
  | JSOAdd       {} -> join [lhs, " + ", rhs]
  | JSOSub       {} -> join [lhs, " - ", rhs]
  | JSOMul       {} -> join [lhs, " * ", rhs]
  | JSODiv       {} -> join [lhs, " / ", rhs]
  | JSOMod       {} -> join [lhs, " % ", rhs]
  | JSOEq        {} -> join [lhs, " === ", rhs]
  | JSONeq       {} -> join [lhs, " !== ", rhs]
  | JSOLt        {} -> join [lhs, " < ", rhs]
  | JSOGt        {} -> join [lhs, " > ", rhs]
  | JSOLe        {} -> join [lhs, " <= ", rhs]
  | JSOGe        {} -> join [lhs, " >= ", rhs]
  | JSOOr        {} -> join [lhs, " || ", rhs]
  | JSOAnd       {} -> join [lhs, " && ", rhs]

  sem printJSUnOp : String -> JSUnOp -> String
  sem printJSUnOp arg =
  | JSONeg       {} -> join ["-", arg]
  | JSONot       {} -> join ["!", arg]
  | JSOSpread    {} -> join ["...", arg]

end



------------------------
-- JavaScript PROGRAM --
------------------------
lang JSProgPrettyPrint = JSProgAst + JSPrettyPrint

  sem printJSProg : JSProg -> String
  sem printJSProg =
  | JSPProg { imports = imports, exprs = exprs } ->
    let indent = 0 in
    let imports = map (lam imp. join ["import '", imp, "';"]) imports in
    let env = pprintEnvEmpty in
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) in
    let importsStr = strJoin "\n" imports in
    let exprsStr = joinAsStatements indent exprs in
    join [importsStr, exprsStr]

end
