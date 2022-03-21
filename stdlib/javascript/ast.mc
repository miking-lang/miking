
--------------------------------------
-- JavaScript TYPES AND EXPRESSIONS --
--------------------------------------

lang JSExprAst

  syn JSExpr = 
  | JSEVar       { id: Name }                   -- Variables 
  | JSEApp       { fun: Name, args: [JSExpr] }  -- Function application
  | JSEDef       { id: Name, expr: JSExpr }     -- Definitions
  | JSEFun       { id: Name, params: [Name], body: JSExpr }  -- Functions
  | JSEInt       { i: Int }                     -- Integer literals
  | JSEFloat     { f: Float }                   -- Float literals
  | JSEChar      { c: Char }                    -- Character literals
  | JSEString    { s: String }                  -- String literals 
  | JSEBinOp     { op: JSBinOp, lhs: JSExpr, rhs: JSExpr } -- Binary operators
  | JSEUnOp      { op: JSUnOp, rhs: JSExpr }    -- Unary operators
  | JSESeq       { exprs : [JSExpr], info: Info } -- Sequences

  syn JSBinOp =
  | JSOAssign    {} -- lhs = rhs
  | JSOSubScript {} -- lhs[rhs]
  | JSOOr        {} -- lhs || rhs
  | JSOAnd       {} -- lhs && rhs
  | JSOEq        {} -- lhs == rhs
  | JSONeq       {} -- lhs != rhs
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
-- C STATEMENTS --
------------------
lang JStmtAst = JSExprAst

  syn JSStmt =
  -- | JSSDef     { ty: CType, id: Option Name, init: Option CInit }
  | JSSIf      { cond: JSExpr, thn: [JSStmt], els: [JSStmt] }
  | JSSSwitch  { cond: JSExpr, body: [(Int, [JSStmt])], default: Option [JSStmt] }
  | JSSWhile   { cond: JSExpr, body: [JSStmt] }
  | JSSExpr    { expr: JSExpr }
  | JSSComp    { stmts: [JSStmt] }
  | JSSRet     { val: Option JSExpr }
  | JSSCont    {}
  | JSSBreak   {}
  | JSSNop     {}

end

-----------------------
-- COMBINED FRAGMENT --
-----------------------
lang JSAst = JSExprAst + JStmtAst -- + JInitAst + JTopAst
end


---------------
-- JS PROGRAM --
---------------
lang JSProgAst = JSAst
  -- We support importing a set of modules at the top of the program.
  -- TODO: Add support for "from" keyword.
  -- https://tc39.es/ecma262/#sec-imports
  syn JSProg =
  | JSPProg { imports: [String], exprs: [JSExpr] }

end
