
--------------------------------------
-- JavaScript TYPES AND EXPRESSIONS --
--------------------------------------

lang JSExprAst

  syn JSExpr =
  | JSEVar       { id: Name }                   -- Variables
  | JSEApp       { fun: JSExpr, args: [JSExpr], curried: Bool }  -- Function application
  | JSEFun       { param: Name, body: JSExpr} -- Functions
  | JSEMember    { expr: JSExpr, id: Name }  -- Member access
  | JSEInt       { i: Int }                     -- Integer literals
  | JSEFloat     { f: Float }                   -- Float literals
  | JSEBool      { b: Bool }                    -- Boolean literals
  | JSEChar      { c: Char }                    -- Character literals
  | JSEString    { s: String }                  -- String literals
  | JSEBinOp     { op: JSBinOp, lhs: JSExpr, rhs: JSExpr } -- Binary operators
  | JSEUnOp      { op: JSUnOp, rhs: JSExpr }    -- Unary operators
  | JSEArray     { exprs : [JSExpr] } -- Sequences
  | JSEObject    { fields: [(String, JSExpr)] } -- Objects

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


------------------
-- JS STATEMENTS --
------------------
lang JSStmtAst = JSExprAst

  syn JSStmt =
  | JSSExpr    { expr: JSExpr } -- Expression statement
  | JSSDef     { id: Name, expr: JSExpr }     -- Definitions
  | JSSIf      { cond: JSExpr, thn: JSStmt, els: JSStmt }
  | JSSSwitch  { cond: JSExpr, body: [(Int, [JSStmt])], default: Option [JSStmt] }
  | JSSWhile   { cond: JSExpr, body: JSStmt } -- While loop
  | JSSRet     { val: Option JSExpr } -- Return
  | JSSCont    { } -- Continue
  | JSSBreak   { } -- Break
  | JSSDelete  { ident: Name } -- Delete variable
  | JSSBlock   { stmts: [JSStmt] } -- Block statement (With surrounding closing braces)
  | JSSSeq     { stmts: [JSStmt] } -- Sequence of statements
  | JSSNop     { } -- No-op

end


--------------------------------------
-- JS PROGRAM in COMBINED FRAGMENTS --
--------------------------------------
lang JSProgAst = JSExprAst + JSStmtAst

  -- We support importing a set of modules at the top of the program.
  -- TODO: Add support for "from" keyword.
  -- https://tc39.es/ecma262/#sec-imports
  syn JSProg =
  | JSPProg { imports: [String], exprs: [JSExpr] }

end
