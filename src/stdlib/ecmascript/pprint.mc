-- Pretty printing for the ECMAScript AST.
--
-- Parenthesization is driven by the ECMA-262 precedence table rather than being
-- inserted defensively around every operand, so `a + b` prints as `a + b` and
-- only genuinely ambiguous nesting such as `a - (b - c)` keeps its parentheses.

include "char.mc"
include "common.mc"
include "ecmascript/ast.mc"
include "ecmascript/ident.mc"
include "seq.mc"
include "string.mc"

-- Indentation is two spaces per level.
let esIndentIncr : Int = 2
let esNl : Int -> String = lam indent. concat "\n" (make indent ' ')

-- Is `str` usable as a bare property key, as in `{ foo: 1 }`? Reserved words
-- are fine in that position, so only the character shape matters.
let esIsIdentLike : String -> Bool = lam str.
  match str with [first] ++ rest then
    if or (isAlpha first) (or (eqc first '_') (eqc first '$')) then
      forAll (lam c. or (isAlphanum c) (or (eqc c '_') (eqc c '$'))) rest
    else false
  else false

let _esHexDigits : String = "0123456789abcdef"

let esUnicodeEscape : Int -> String = lam code.
  recursive let go = lam n. lam acc. lam i.
    if eqi i 0 then acc
    else go (divi n 16) (cons (get _esHexDigits (modi n 16)) acc) (subi i 1)
  in concat "\\u" (go code "" 4)

-- Escapes a character for inclusion in a double-quoted ECMAScript string.
--
-- U+2028 and U+2029 are escaped because they terminate a line in ECMAScript and
-- would otherwise split the literal. Codepoints above the BMP are emitted
-- literally, so the output file must be written as UTF-8.
let esEscapeChar : Char -> String = lam c.
  let code = char2int c in
  switch c
  case '\\' then "\\\\"
  case '\"' then "\\\""
  case '\n' then "\\n"
  case '\t' then "\\t"
  case '\r' then "\\r"
  case _ then
    if or (lti code 32) (or (eqi code 8232) (eqi code 8233))
    then esUnicodeEscape code
    else [c]
  end

let esEscapeString : String -> String = lam s. join (map esEscapeChar s)

-- `float2string` renders 1.0 as "1." and the non-finite values as "inf", "-inf"
-- and "nan", none of which are ECMAScript numeric literals.
let esFloatLit : Float -> String = lam f.
  let s = float2string f in
  if eqString s "inf" then "Infinity"
  else if eqString s "-inf" then "-Infinity"
  else if or (eqString s "nan") (eqString s "-nan") then "NaN"
  else match s with _ ++ "." then snoc s '0'
  else s

lang ESPrettyPrint = ESAst

  ---------------
  -- OPERATORS --
  ---------------

  sem printESBinOp : ESBinOp -> String
  sem printESBinOp =
  | ESOAdd _ -> "+"    | ESOSub _ -> "-"     | ESOMul _ -> "*"
  | ESODiv _ -> "/"    | ESOMod _ -> "%"     | ESOEq _ -> "==="
  | ESONeq _ -> "!=="  | ESOLt _ -> "<"      | ESOLe _ -> "<="
  | ESOGt _ -> ">"     | ESOGe _ -> ">="     | ESOAnd _ -> "&&"
  | ESOOr _ -> "||"    | ESOShl _ -> "<<"    | ESOShr _ -> ">>"
  | ESOUShr _ -> ">>>" | ESOBitAnd _ -> "&"  | ESOBitOr _ -> "|"
  | ESOBitXor _ -> "^"

  -- Precedence levels follow the ECMA-262 expression grammar.
  sem esBinOpPrec : ESBinOp -> Int
  sem esBinOpPrec =
  | ESOMul _ | ESODiv _ | ESOMod _ -> 12
  | ESOAdd _ | ESOSub _ -> 11
  | ESOShl _ | ESOShr _ | ESOUShr _ -> 10
  | ESOLt _ | ESOLe _ | ESOGt _ | ESOGe _ -> 9
  | ESOEq _ | ESONeq _ -> 8
  | ESOBitAnd _ -> 7
  | ESOBitXor _ -> 6
  | ESOBitOr _ -> 5
  | ESOAnd _ -> 4
  | ESOOr _ -> 3

  sem printESUnOp : ESUnOp -> String
  sem printESUnOp =
  | ESONeg _ -> "-"
  | ESONot _ -> "!"
  | ESOSpread _ -> "..."
  | ESOTypeof _ -> "typeof "

  -----------------
  -- EXPRESSIONS --
  -----------------

  sem esExprPrec : ESExpr -> Int
  sem esExprPrec =
  -- A negative literal behaves like a unary minus for parenthesization.
  | ESEInt t -> if lti t.value 0 then 14 else 18
  | ESEFloat t -> if ltf t.value 0.0 then 14 else 18
  | ESEVar _ | ESEBool _ | ESEString _ | ESEUndefined _ | ESENull _
  | ESEArray _ | ESEObject _ -> 18
  | ESEMember _ | ESEIndex _ | ESECall _ | ESENew _ -> 17
  | ESEUn _ -> 14
  | ESEBin t -> esBinOpPrec t.op
  | ESEInstanceOf _ -> 9
  | ESECond _ | ESEArrow _ -> 2

  -- Prints `e`, parenthesizing it when it binds more loosely than `prec`.
  sem printESExprP : ESNameEnv -> Int -> Int -> ESExpr -> (ESNameEnv, String)
  sem printESExprP env indent prec =
  | e ->
    match printESExpr env indent e with (env, s) in
    if lti (esExprPrec e) prec then (env, join ["(", s, ")"]) else (env, s)

  sem printESExprs : ESNameEnv -> Int -> Int -> [ESExpr] -> (ESNameEnv, String)
  sem printESExprs env indent prec =
  | exprs ->
    match mapAccumL (lam env. lam e. printESExprP env indent prec e) env exprs
      with (env, strs) in
    (env, strJoin ", " strs)

  sem printESExpr : ESNameEnv -> Int -> ESExpr -> (ESNameEnv, String)
  sem printESExpr env indent =
  | ESEVar t -> esNameGet env t.id
  | ESEInt t -> (env, int2string t.value)
  | ESEFloat t -> (env, esFloatLit t.value)
  | ESEBool t -> (env, if t.value then "true" else "false")
  | ESEString t -> (env, join ["\"", esEscapeString t.value, "\""])
  | ESEUndefined _ -> (env, "undefined")
  | ESENull _ -> (env, "null")
  | ESEArray t ->
    -- Elements are AssignmentExpressions, so a bare comma operator would need
    -- parentheses; nothing else does.
    match printESExprs env indent 2 t.exprs with (env, s) in
    (env, join ["[", s, "]"])
  | ESEObject t ->
    match mapAccumL (lam env. lam f.
        match printESExprP env indent 2 f.1 with (env, v) in
        let k = if esIsIdentLike f.0 then f.0
                else join ["\"", esEscapeString f.0, "\""] in
        (env, join [k, ": ", v]))
      env t.fields
      with (env, fields) in
    if null fields then (env, "{}")
    else (env, join ["{ ", strJoin ", " fields, " }"])
  | ESEMember t ->
    match printESExprP env indent 17 t.obj with (env, o) in
    (env, join [o, ".", t.prop])
  | ESEIndex t ->
    match printESExprP env indent 17 t.obj with (env, o) in
    match printESExpr env indent t.index with (env, i) in
    (env, join [o, "[", i, "]"])
  | ESECall t ->
    match printESExprP env indent 17 t.callee with (env, c) in
    match printESExprs env indent 2 t.args with (env, a) in
    (env, join [c, "(", a, ")"])
  | ESENew t ->
    match printESExprP env indent 17 t.callee with (env, c) in
    match printESExprs env indent 2 t.args with (env, a) in
    (env, join ["new ", c, "(", a, ")"])
  | ESEArrow t ->
    match esNameGetMany env t.params with (env, params) in
    let ps = match params with [p] then p else join ["(", strJoin ", " params, ")"] in
    match t.body with ESFBExpr b then
      -- A concise body starting with `{` would be parsed as a block.
      let prec = match b.expr with ESEObject _ then 19 else 2 in
      match printESExprP env indent prec b.expr with (env, body) in
      (env, join [ps, " => ", body])
    else match t.body with ESFBBlock b then
      match printESBlock env indent b.stmts with (env, body) in
      (env, join [ps, " => ", body])
    else never
  | ESEBin t ->
    let prec = esBinOpPrec t.op in
    -- All binary operators we emit are left-associative, so the right operand
    -- must bind one level tighter to survive without parentheses.
    match printESExprP env indent prec t.lhs with (env, l) in
    match printESExprP env indent (addi prec 1) t.rhs with (env, r) in
    (env, join [l, " ", printESBinOp t.op, " ", r])
  | ESEUn t ->
    match printESExprP env indent 14 t.arg with (env, a) in
    (env, concat (printESUnOp t.op) a)
  | ESECond t ->
    match printESExprP env indent 3 t.cond with (env, c) in
    match printESExprP env indent 2 t.thn with (env, thn) in
    match printESExprP env indent 2 t.els with (env, els) in
    (env, join [c, " ? ", thn, " : ", els])
  | ESEInstanceOf t ->
    match printESExprP env indent 9 t.lhs with (env, l) in
    match printESExprP env indent 10 t.rhs with (env, r) in
    (env, join [l, " instanceof ", r])

  ----------------
  -- STATEMENTS --
  ----------------

  sem printESBlock : ESNameEnv -> Int -> [ESStmt] -> (ESNameEnv, String)
  sem printESBlock env indent =
  | [] -> (env, "{}")
  | stmts ->
    let inner = addi indent esIndentIncr in
    match printESStmts env inner stmts with (env, s) in
    (env, join ["{", esNl inner, s, esNl indent, "}"])

  sem printESStmts : ESNameEnv -> Int -> [ESStmt] -> (ESNameEnv, String)
  sem printESStmts env indent =
  | stmts ->
    match mapAccumL (lam env. lam s. printESStmt env indent s) env stmts
      with (env, strs) in
    (env, strJoin (esNl indent) strs)

  sem printESStmt : ESNameEnv -> Int -> ESStmt -> (ESNameEnv, String)
  sem printESStmt env indent =
  | ESSConst t ->
    match esNameGet env t.id with (env, id) in
    match printESExpr env indent t.init with (env, e) in
    (env, join ["const ", id, " = ", e, ";"])
  | ESSLet t ->
    match esNameGet env t.id with (env, id) in
    match t.init with Some init then
      match printESExpr env indent init with (env, e) in
      (env, join ["let ", id, " = ", e, ";"])
    else (env, join ["let ", id, ";"])
  | ESSAssign t ->
    match printESExprP env indent 17 t.target with (env, target) in
    match printESExpr env indent t.value with (env, v) in
    (env, join [target, " = ", v, ";"])
  | ESSExpr t ->
    -- A statement starting with `{` would be parsed as a block.
    let prec = match t.expr with ESEObject _ then 19 else 0 in
    match printESExprP env indent prec t.expr with (env, e) in
    (env, concat e ";")
  | ESSReturn t ->
    match t.expr with Some e then
      match printESExpr env indent e with (env, s) in
      (env, join ["return ", s, ";"])
    else (env, "return;")
  | ESSIf t ->
    match printESExpr env indent t.cond with (env, c) in
    match printESBlock env indent t.thn with (env, thn) in
    let head = join ["if (", c, ") ", thn] in
    switch t.els
    case [] then (env, head)
    -- Chain `else if` rather than nesting, which keeps lowered match cascades
    -- flat and readable.
    case [ESSIf _ & inner] then
      match printESStmt env indent inner with (env, e) in
      (env, join [head, " else ", e])
    case els then
      match printESBlock env indent els with (env, e) in
      (env, join [head, " else ", e])
    end
  | ESSBlock t -> printESBlock env indent t.stmts
  | ESSWhile t ->
    match printESExpr env indent t.cond with (env, c) in
    match printESBlock env indent t.body with (env, b) in
    (env, join ["while (", c, ") ", b])
  | ESSFunDecl t ->
    match esNameGet env t.id with (env, id) in
    match esNameGetMany env t.params with (env, params) in
    match printESBlock env indent t.body with (env, b) in
    (env, join ["function ", id, "(", strJoin ", " params, ") ", b])
  | ESSClass t ->
    match esNameGet env t.id with (env, id) in
    match t.extends with Some base then
      match esNameGet env base with (env, b) in
      (env, join ["class ", id, " extends ", b, " {}"])
    else (env, join ["class ", id, " {}"])
  | ESSExportDefault t ->
    match printESStmt env indent t.stmt with (env, s) in
    (env, concat "export default " s)

  -------------
  -- MODULES --
  -------------

  sem printESImport : ESNameEnv -> ESImport -> (ESNameEnv, String)
  sem printESImport env =
  | ESImportNamed t ->
    match mapAccumL (lam env. lam n.
        match esNameGet env n.1 with (env, local) in
        (env, if eqString n.0 local then local else join [n.0, " as ", local]))
      env t.names
      with (env, names) in
    (env, join ["import { ", strJoin ", " names, " } from \"", t.from, "\";"])
  | ESImportDefault t ->
    match esNameGet env t.name with (env, n) in
    (env, join ["import ", n, " from \"", t.from, "\";"])

  sem printESProg : ESNameEnv -> ESProg -> (ESNameEnv, String)
  sem printESProg env =
  | ESProg t ->
    match mapAccumL printESImport env t.imports with (env, imports) in
    match printESStmts env 0 t.stmts with (env, stmts) in
    let head = if null imports then "" else join [strJoin "\n" imports, "\n\n"] in
    (env, join [head, stmts, "\n"])

end

mexpr

use ESPrettyPrint in

let pp = lam e.
  match printESExpr esNameEnvEmpty 0 e with (_, s) in s in
let pps = lam s.
  match printESStmt esNameEnvEmpty 0 s with (_, str) in str in

let a = nameSym "a" in
let b = nameSym "b" in
let c = nameSym "c" in
let va = ESEVar { id = a } in
let vb = ESEVar { id = b } in
let vc = ESEVar { id = c } in
let sub = lam l. lam r. ESEBin { op = ESOSub {}, lhs = l, rhs = r } in
let add = lam l. lam r. ESEBin { op = ESOAdd {}, lhs = l, rhs = r } in
let mul = lam l. lam r. ESEBin { op = ESOMul {}, lhs = l, rhs = r } in

-- Operands that already bind tightly enough are not parenthesized.
utest pp (add va vb) with "a + b" in
utest pp (sub (sub va vb) vc) with "a - b - c" in
utest pp (mul (add va vb) vc) with "(a + b) * c" in
-- ... but a right operand at the same level is, since `-` is left-associative.
utest pp (sub va (sub vb vc)) with "a - (b - c)" in
utest pp (add (mul va vb) vc) with "a * b + c" in

-- Access and application.
utest pp (ESECall { callee = esMember va "print", args = [vb] }) with "a.print(b)" in
utest pp (esMember (ESECall { callee = va, args = [] }) "x") with "a().x" in
utest pp (ESENew { callee = va, args = [vb] }) with "new a(b)" in
utest pp (ESEIndex { obj = va, index = ESEInt { value = 0 } }) with "a[0]" in

-- Literals.
utest pp (ESEInt { value = 3 }) with "3" in
utest pp (ESEInt { value = negi 3 }) with "-3" in
utest pp (esMember (ESEInt { value = negi 3 }) "x") with "(-3).x" in
utest pp (ESEFloat { value = 1.0 }) with "1.0" in
utest pp (ESEFloat { value = 0.5 }) with "0.5" in
utest pp (ESEFloat { value = divf 1.0 0.0 }) with "Infinity" in
utest pp (ESEString { value = "hi\n\"there\"" }) with "\"hi\\n\\\"there\\\"\"" in
utest pp (ESEString { value = [int2char 8232] }) with "\"\\u2028\"" in
utest pp esUnit with "undefined" in

-- Objects: bare keys where possible, quoted otherwise.
utest pp (ESEObject { fields = [("x", va), ("0", vb)] }) with "{ x: a, \"0\": b }" in
utest pp (ESEObject { fields = [] }) with "{}" in

-- Arrows: a single parameter drops its parentheses.
utest pp (ESEArrow { params = [a], body = ESFBExpr { expr = add va (ESEInt { value = 1 }) } })
with "a => a + 1" in
utest pp (ESEArrow { params = [a, b], body = ESFBExpr { expr = vb } })
with "(a, b) => b" in
-- A concise body that is an object literal needs parentheses.
utest pp (ESEArrow { params = [], body = ESFBExpr { expr = ESEObject { fields = [("x", va)] } } })
with "() => ({ x: a })" in

-- Conditionals and instanceof.
utest pp (ESECond { cond = va, thn = vb, els = vc }) with "a ? b : c" in
utest pp (ESEInstanceOf { lhs = va, rhs = vb }) with "a instanceof b" in
utest pp (ESEUn { op = ESONot {}, arg = va }) with "!a" in
utest pp (ESEUn { op = ESONot {}, arg = add va vb }) with "!(a + b)" in

-- Statements.
utest pps (ESSConst { id = a, init = ESEInt { value = 1 } }) with "const a = 1;" in
utest pps (ESSLet { id = a, init = None () }) with "let a;" in
utest pps (ESSReturn { expr = None () }) with "return;" in
utest pps (ESSExpr { expr = ESECall { callee = va, args = [] } }) with "a();" in
utest pps (ESSClass { id = a, extends = Some b }) with "class a extends b {}" in
utest pps (ESSClass { id = a, extends = None () }) with "class a {}" in

utest pps (ESSIf { cond = va, thn = [ESSReturn { expr = Some vb }], els = [] })
with "if (a) {\n  return b;\n}" in

-- A lone `if` in the else branch chains rather than nesting.
utest pps (ESSIf { cond = va
                 , thn = [ESSReturn { expr = Some vb }]
                 , els = [ESSIf { cond = vb
                                , thn = [ESSReturn { expr = Some vc }]
                                , els = [ESSReturn { expr = Some va }] }] })
with "if (a) {\n  return b;\n} else if (b) {\n  return c;\n} else {\n  return a;\n}" in

utest pps (ESSFunDecl { id = a, params = [b], body = [ESSReturn { expr = Some vb }] })
with "function a(b) {\n  return b;\n}" in

utest pps (ESSFunDecl { id = a, params = [], body = [] }) with "function a() {}" in

let env = nameSym "env" in
let prog = ESProg
  { imports = []
  , stmts =
    [ ESSExportDefault
      { stmt = ESSFunDecl
        { id = nameSym "main"
        , params = [env]
        , body =
          [ ESSConst { id = a, init = ESEInt { value = 1 } }
          , ESSConst { id = b, init = ESEInt { value = 2 } }
          , ESSConst { id = c, init = add va vb }
          , ESSExpr { expr = ESECall
              { callee = esMember (ESEVar { id = env }) "dprint", args = [vc] } }
          ] } } ] } in
match printESProg esNameEnvEmpty prog with (_, out) in
utest out with join
  [ "export default function main(env) {\n"
  , "  const a = 1;\n"
  , "  const b = 2;\n"
  , "  const c = a + b;\n"
  , "  env.dprint(c);\n"
  , "}\n" ] in

()
