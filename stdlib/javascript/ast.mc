
--------------------------------------
-- JavaScript TYPES AND EXPRESSIONS --
--------------------------------------

lang JSExprAst

  syn JSExpr =
  | JSEVar       { id: Name }                   -- Variables
  | JSEDef       { id: Name, expr: JSExpr }     -- Definitions
  | JSEApp       { fun: JSExpr, args: [JSExpr], curried: Bool }  -- Function application
  | JSEFun       { param: Name, body: JSStmt} -- Functions
  | JSEMember    { expr: JSExpr, id: String }  -- Member access
  | JSEInt       { i: Int }                     -- Integer literals
  | JSEFloat     { f: Float }                   -- Float literals
  | JSEBool      { b: Bool }                    -- Boolean literals
  | JSEChar      { c: Char }                    -- Character literals
  | JSEString    { s: String }                  -- String literals
  | JSETernary   { cond: JSExpr, thn: JSExpr, els: JSExpr } -- Ternary operator
  | JSEBinOp     { op: JSBinOp, lhs: JSExpr, rhs: JSExpr } -- Binary operators
  | JSEUnOp      { op: JSUnOp, rhs: JSExpr }    -- Unary operators
  | JSEArray     { exprs : [JSExpr] } -- Sequences
  | JSEObject    { fields: [(String, JSExpr)] } -- Objects
  | JSEIIFE      { body: JSExpr } -- Immediately-invoked function expression
  | JSEBlock     { exprs: [JSExpr], ret: JSExpr } -- Block
  | JSENop       { } -- No-op

  syn JSBinOp =
  | JSOAssign    {} -- lhs = rhs
  | JSOSubScript {} -- lhs[rhs]
  | JSOOr        {} -- lhs || rhs
  | JSOAnd       {} -- lhs && rhs
  | JSOEq        {} -- lhs === rhs
  | JSONeq       {} -- lhs !== rhs
  | JSOLt        {} -- lhs < rhs
  | JSOGt        {} -- lhs > rhs
  | JSOLe        {} -- lhs <= rhs
  | JSOGe        {} -- lhs >= rhs
  | JSOAdd       {} -- lhs + rhs
  | JSOSub       {} -- lhs - rhs
  | JSOMul       {} -- lhs * rhs
  | JSODiv       {} -- lhs / rhs
  | JSOMod       {} -- lhs % rhs
  -- TODO: Add support for object member access "lhs.rhs"
  -- Otherwise replicateable with JOSubScript.

  syn JSUnOp =
  | JSONeg       {} -- -arg
  | JSONot       {} -- !arg

end

--------------------------------------
-- JS PROGRAM in COMBINED FRAGMENTS --
--------------------------------------
lang JSProgAst = JSExprAst

  -- We support importing a set of modules at the top of the program.
  -- TODO: Add support for "from" keyword.
  -- https://tc39.es/ecma262/#sec-imports
  syn JSProg =
  | JSPProg { imports: [String], exprs: [JSExpr] }

end
