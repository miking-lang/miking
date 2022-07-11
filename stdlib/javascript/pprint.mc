-- Pretty printing for JavaScript fragments.

include "javascript/ast.mc"
include "string.mc"
include "char.mc"

include "mexpr/pprint.mc"


-------------
-- HELPERS --
-------------


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

let joinAsStatements = lam indent. lam seq.
  concat (strJoin (concat ";" (pprintNewline indent)) seq) ";"

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



-------------------------------------------
-- JavaScript EXPRESSIONS and STATEMENTS --
-------------------------------------------
lang JSPrettyPrint = JSExprAst


  sem printJSExprs (indent: Int) (env: PprintEnv) =
  | exprs ->
    match mapAccumL (printJSExpr indent) env exprs with (env, exprs) then
      (env, strJoin (pprintNewline indent) exprs)
    else never


  sem printJSFunParams : PprintEnv -> Bool -> [Name] -> (PprintEnv, String)
  sem printJSFunParams env simplify =
  | params ->
    match mapAccumL (pprintEnvGetStr) env params with (env, params) then
      let args = strJoin ", " params in
      if and simplify (eqi (length params) 1) then (env, args)
      else (env, join ["(", args, ")"])
    else never


  sem printJSExpr (indent : Int) (env: PprintEnv) =
  | JSEVar { id = id } -> pprintEnvGetStr env id
  | JSEApp { fun = fun, args = args, curried = curried } ->
    match (printJSExpr indent) env fun with (env,fun) then
      match mapAccumL (printJSExpr 0) env args with (env,args) then
        let joinArgs = if curried then (strJoin ")(") else (strJoin ", ") in
        (env, join [fun, "(", joinArgs args, ")"])
      else never
    else never
  | JSEMember { expr = expr, id = id } ->
    match (printJSExpr indent) env expr with (env,expr) then
      (env, join [expr, ".", id])
    else never
  | JSEDef { id = id, expr = expr } ->
    match pprintEnvGetStr env id with (env,id) then
      match (printJSExpr indent env) expr with (env, str) then
        (env, join ["let ", id, " = ", str])
      else never
    else never

  -- ES6 arrow functions (released 2015)
  -- https://en.wikipedia.org/wiki/ECMAScript#6th_Edition_%E2%80%93_ECMAScript_2015
  -- Comparison to anonymous functions:
  -- https://dmitripavlutin.com/differences-between-arrow-and-regular-functions
  | JSEFun { params = params, body = body } ->
    let i = indent in
    match (printJSFunParams env true params) with (env, args) then
      match (printJSExpr i) env body with (env,body) then
        (env, join [args, " => ", body])
      else never
    else never
  | JSEIIFE { body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match (printJSExpr ii) env body with (env,body) then
      (env, join ["(() => ", body, ")()"])
    else never

  | JSEInt   { i = i } -> (env, int2string i)
  | JSEFloat { f = f } -> (env, float2string f)
  | JSEBool  { b = b } -> (env, if b then "true" else "false")
  | JSEChar  { c = c } -> (env, ['\'', c, '\''])
  | JSEString { s = s } -> (env, join ["\"", escapeString s, "\""])

  | JSETernary { cond = cond, thn = thn, els = els } ->
    let i = indent in
    match (printJSExpr 0 env) cond with (env, cond) then
      match (printJSExpr i env) thn with (env, thn) then
        match (printJSExpr i env) els with (env, els) then
          (env, join ["(", cond, " ? ", thn, " : ", els, ")"])
        else never
      else never
    else never
  | JSEBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match (printJSExpr indent) env lhs with (env,lhs) then
      match (printJSExpr indent) env rhs with (env,rhs) then
        (env, join ["(", printJSBinOp lhs rhs op, ")"])
      else never
    else never

  | JSEUnOp { op = op, rhs = rhs } ->
    match (printJSExpr indent) env rhs with (env,rhs) then
      (env, printJSUnOp rhs op)
    else never

  | JSEArray { exprs = exprs } ->
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) then
      (env, join ["[", strJoin ", " exprs, "]"])
    else never
  | JSEObject { fields = fields } ->
    let printPair = lam field.
      match field with (n, e)
      then match (printJSExpr 0) env e with (env,e) then
          join [n, ": ", e]
        else never
      else never in
    match map (printPair) fields with prs then
      (env, join ["{", strJoin ", " prs, "}"])
    else never
  | JSEBlock { exprs = exprs, ret = ret } ->
    let i = indent in
    let ii = pprintIncr indent in
    match mapAccumL (printJSExpr ii) env exprs with (env, exprs) then
      let ret = match (printJSExpr 0 env) ret with (env, val) then
          match val with "" then ""
          else join [pprintNewline ii, "return ", val, ";"]
        else "" in
      (env, join ["{",
        pprintNewline ii, joinAsStatements ii exprs,
        ret,
        pprintNewline i, "}"])
    else never
  | JSENop _ -> (env, "")

  sem printJSBinOp (lhs: String) (rhs: String) =
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

  sem printJSUnOp (arg: String) =
  | JSONeg       {} -> join ["-", arg]
  | JSONot       {} -> join ["!", arg]
  | JSOSpread    {} -> join ["...", arg]

end



------------------------
-- JavaScript PROGRAM --
------------------------
lang JSProgPrettyPrint = JSProgAst + JSPrettyPrint

  sem printJSProg =
  | JSPProg { imports = imports, exprs = exprs } ->
    let indent = 0 in
    let imports = map (lam imp. join ["import '", imp, "';"]) imports in
    let env = pprintEnvEmpty in
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) then
      let importsStr = strJoin "\n" imports in
      let exprsStr = joinAsStatements indent exprs in
      join [importsStr, exprsStr]
    else never

end
