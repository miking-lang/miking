include "mexpr/info.mc"
include "name.mc"

--------------------------------------
-- JavaScript TYPES AND EXPRESSIONS --
--------------------------------------

lang JSExprAst

  syn JSExpr =
  | JSEVar       { id: Name }                   -- Variables
  | JSEDef       { id: Name, expr: JSExpr }     -- Definitions (Constants)
  | JSEDec       { ids: [Name] }                -- Declarations (Mutable)
  | JSEApp       { fun: JSExpr, args: [JSExpr], curried: Bool }  -- Function application
  | JSEFun       { params: [Name], body: JSExpr } -- Functions
  | JSEMember    { expr: JSExpr, id: String }   -- Member access
  | JSEIndex     { expr: JSExpr, index: String } -- Indexing
  | JSEInt       { i: Int }                     -- Integer literals
  | JSEFloat     { f: Float }                   -- Float literals
  | JSEBool      { b: Bool }                    -- Boolean literals
  | JSEChar      { c: Char }                    -- Character literals
  | JSEString    { s: String }                  -- String literals
  | JSETernary   { cond: JSExpr, thn: JSExpr, els: JSExpr } -- Ternary operator
  | JSEBinOp     { op: JSBinOp, lhs: JSExpr, rhs: JSExpr } -- Binary operators
  | JSEUnOp      { op: JSUnOp, rhs: JSExpr }    -- Unary operators
  | JSEArray     { exprs : [JSExpr] }           -- Sequences
  | JSEObject    { fields: [(String, JSExpr)] } -- Objects
  | JSEIIFE      { body: JSExpr }               -- Immediately-invoked function expression
  | JSEBlock     { exprs: [JSExpr], ret: JSExpr } -- Block
  | JSEReturn    { expr: JSExpr }               -- Early return
  | JSENop       { }                            -- No-op

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

  syn JSUnOp =
  | JSONeg       {} -- -arg
  | JSONot       {} -- !arg
  | JSOSpread    {} -- ...arg

  sem smapJSExprJSExpr : (JSExpr -> JSExpr) -> JSExpr -> JSExpr
  sem smapJSExprJSExpr f =
  | JSEDef { id = id, expr = expr } -> JSEDef { id = id, expr = f expr }
  | JSEApp { fun = fun, args = args, curried = curried } -> JSEApp { fun = f fun, args = map f args, curried = curried }
  | JSEFun { params = params, body = body } -> JSEFun { params = params, body = f body }
  | JSEMember { expr = expr, id = id } -> JSEMember { expr = f expr, id = id }
  | JSETernary { cond = cond, thn = thn, els = els } -> JSETernary { cond = f cond, thn = f thn, els = f els }
  | JSEBinOp { op = op, lhs = lhs, rhs = rhs } -> JSEBinOp { op = op, lhs = f lhs, rhs = f rhs }
  | JSEUnOp { op = op, rhs = rhs } -> JSEUnOp { op = op, rhs = f rhs }
  | JSEArray { exprs = exprs } -> JSEArray { exprs = map f exprs }
  | JSEObject { fields = fields } -> JSEObject { fields = map (lam p. match p with (id, expr) in (id, f expr) ) fields }
  | JSEIIFE { body = body } -> JSEIIFE { body = f body }
  | JSEBlock { exprs = exprs, ret = ret } -> JSEBlock { exprs = map f exprs, ret = f ret }
  | JSEReturn { expr = expr } -> JSEReturn { expr = f expr }
  | e -> e

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
