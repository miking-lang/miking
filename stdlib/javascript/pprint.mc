-- Pretty printing for JavaScript fragments.

include "javascript/ast.mc"
include "string.mc"
include "char.mc"

include "mexpr/pprint.mc"


--------------
-- KEYWORDs --
--------------

-- From Draft ECMA-262 / March 3, 2022 (https://tc39.es/ecma262/#sec-keywords-and-reserved-words)
let jsKeywords = [
    "await", "break", "case", "catch", "class", "const", "continue",
    "debugger", "default", "delete", "do", "else", "enum", "export",
    "extends", "false", "finally", "for", "function", "if", "import",
    "in", "instanceof", "new", "null", "return", "super", "switch",
    "this", "throw", "true", "try", "typeof", "var", "void", "while",
    "with", "yield",
    -- Extra reserved words (Not in spec)
    "console", "document", "window", "global", "localStorage", "sessionStorage",
    "location", "navigator", "history"
]



----------------------------
-- JavaScript EXPRESSIONS --
----------------------------
lang JSExprPrettyPrint = JSExprTypeAst

  sem printJSDef (env: PprintEnv) (id: String) =
  | expr -> (env, join [id, " = ", printJSExpr expr, ";"]) -- Should ; be here?

  sem printJSExprs (indent: Int) (env: PprintEnv) =
  | exprs ->
    match mapAccumL (printJSExpr indent) env exprs with (env,exprs) then
      (env, strJoin (pprintNewline indent) exprs)
    else never

  sem printJSExpr (indent : Int) (env: PprintEnv) =
  | JSEVar { id = id } -> pprintEnvGetStr env id
  | JSEApp { fun = fun, args = args } ->
    match pprintEnvGetStr env fun with (env,fun) then
      match mapAccumL printJSExpr env args with (env,args) then
        (env, join [fun, "(", (strJoin ", " args), ")"])
      else never
    else never

  | JSEDef { id = id, expr = expr } ->
    match pprintEnvGetOptStr env id with (env,id) then
      match printJSDef env id expr with (env,str) then
        (env, join [str, ";"])
      else never
    else never

  | JSEFun { id = id, params = params, body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match pprintEnvGetStr env id with (env,id) then
      let f = lam env. lam t: Name.
        match pprintEnvGetStr env t.1 with (env,t1) then
          printJSDef env t.0 t1 (None ())
        else never in
      match mapAccumL f env params with (env,params) then
        let params = join ["(", strJoin ", " params, ")"] in
        match printJSExprs ii env body with (env,body) then
          (env, join [id, params, " {", pprintNewline ii, body, pprintNewline i, "}"])
        else never
      else never
    else never

  | JSEInt   { i = i } -> (env, int2string i)
  | JSEFloat { f = f } -> (env, float2string f)
  | JSEChar  { c = c } -> (env, ['\'', c, '\''])

  | JSEString { s = s } -> (env, join ["\"", escapeString s, "\""])

  | JSEBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match printJSExpr env lhs with (env,lhs) then
      match printJSExpr env rhs with (env,rhs) then
        (env, _par (printJSBinOp lhs rhs op))
      else never
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
    match mapAccumL (printJSExpr indent env) exprs with (env,code) then
      strJoin (pprintNewline indent) (join [imports, "", code])
    else never

end
