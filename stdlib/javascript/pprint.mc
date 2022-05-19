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



-------------------------------------------
-- JavaScript EXPRESSIONS and STATEMENTS --
-------------------------------------------
lang JSPrettyPrint = JSExprAst + JSStmtAst

  sem printJSStmt (indent: Int) (env: PprintEnv) =
  | JSSDef { id = id, expr = expr } ->
    match pprintEnvGetStr env id with (env,id) then
      match (printJSExpr indent env) expr with (env, str) then
        (env, join ["var ", id, " = ", str, ";"])
      else never
    else never
  | JSSIf { cond = cond, thn = thn, els = els } ->
    let i = indent in
    match (printJSExpr 0 env) cond with (env, cond) then
      match (printJSStmt i env) thn with (env, thn) then
        match (printJSStmt i env) els with (env, els) then
          let ifBlock = join ["if (", cond, ") ", thn] in
          let elseBlock = join ["else ", els] in
          (env, join [ifBlock, " ", elseBlock])
        else never
      else never
    else never
  | JSSBlock { stmts = stmts } ->
    let i = indent in
    let ii = pprintIncr indent in
    match mapAccumL (printJSStmt ii) env stmts with (env,stmts) then
      (env, join [pprintSpacing i, "{",
                  pprintNewline ii, strJoin (pprintNewline ii) stmts,
                  pprintNewline i, "}"])
    else never
  | JSSSeq { stmts = stmts } ->
    let i = indent in
    match mapAccumL (printJSStmt i) env stmts with (env,stmts) then
      (env, strJoin (pprintNewline i) stmts)
    else never
  | JSSRet { val = val } ->
    match val with Some val then
      match (printJSExpr 0 env) val with (env, val) then
        (env, join ["return ", val, ";"])
      else never
    else (env, "return")
  | ( ((JSEApp _) & expr) -- Outmost calls are valid statements
    | (JSSExpr {expr = expr})
    ) ->
    match (printJSExpr indent env) expr with (env, str) then
      (env, concat str ";")
    else never
  | _ -> error "printJSStmt: unexpected expression"




  sem printJSExprs (indent: Int) (env: PprintEnv) =
  | exprs ->
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) then
      (env, strJoin (pprintNewline indent) exprs)
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
      match (pprintEnvGetStr env id) with (env,id) then
        (env, join [expr, ".", id])
      else never
    else never

  | JSEFun { param = param, body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match pprintEnvGetStr env param with (env,param) then
      match (printJSExpr ii) env body with (env,body) then
        -- ES6 arrow functions (released 2015)
        -- https://en.wikipedia.org/wiki/ECMAScript#6th_Edition_%E2%80%93_ECMAScript_2015
        -- Comparison to anonymous functions:
        -- https://dmitripavlutin.com/differences-between-arrow-and-regular-functions
        (env, join [param, " => ", body])
      else never
    else never

  | JSEInt   { i = i } -> (env, int2string i)
  | JSEFloat { f = f } -> (env, float2string f)
  | JSEBool  { b = b } -> (env, if b then "true" else "false")
  | JSEChar  { c = c } -> (env, ['\'', c, '\''])
  | JSEString { s = s } -> (env, join ["\"", escapeString s, "\""])

  | JSEBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match (printJSExpr indent) env lhs with (env,lhs) then
      match (printJSExpr indent) env rhs with (env,rhs) then
        (env, join ["(", printJSBinOp lhs rhs op, ")"])
      else never
    else never

  | JSEUnOp { op = op, rhs = rhs } ->
    match (printJSExpr indent) env rhs with (env,rhs) then
      (env, join ["(", printJSUnOp rhs op, ")"])
    else never

  | JSEArray { exprs = exprs, info = info } ->
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
lang JSProgPrettyPrint = JSProgAst + JSPrettyPrint

  sem printJSProg =
  | JSPProg { imports = imports, exprs = exprs } ->
    let indent = 0 in
    let imports = map (lam imp. join ["import '", imp, "';"]) imports in
    let env = pprintEnvEmpty in
    match mapAccumL (printJSStmt indent) env exprs with (env,exprs) then
      let importsStr = strJoin "\n" imports in
      let exprsStr = strJoin (pprintNewline indent) exprs in
      join [importsStr, exprsStr]
    else never

end
