-- AST fragment for a subset of the C language, suitable for code generation.

-- NOTE(dlunde,2020-10-29): Missing functionality (most things are probably not
-- needed for code generation or can be expressed through other language
-- constructs):
-- * Includes/module system
-- * Labeled statements and goto
-- * Storage class specifiers (typedef, auto, register, static, extern)
-- * Type qualifiers (const, volatile)
-- * Increment/decrement operators
-- * Combined assignment operators (e.g. +=, *=)
-- * Ternary operator (cond ? expr : expr)

include "name.mc"

lang CAst

  -------------------
  -- C EXPRESSIONS --
  -------------------
  -- NOTE(dlunde,2020-10-28): We cannot reuse operators from mexpr (such as
  -- CAddi) since they are curried. Maybe this will change in the future?

  syn Expr =
  | EVar        { id: Name }
  | EApp        { fun: Name, args: [Expr] }
  | EInt        { i: Int }
  | EFloat      { f: Float }
  | EChar       { c: Char }
  | EString     { s: String }
  | EBinOp      { op: UnOp, lhs: Expr, rhs: Expr }
  | EUnOp       { op: BinOp, arg: Expr }
  | EMemb       { lhs: Expr, id: Name }
  | ECast       { ty: Type, rhs: Expr }
  | ESizeOfType { ty: Type }

  syn BinOp =
  | OAssg {}
  | OSubScr {}
  | OOr {}
  | OAnd {}
  | OEq {}
  | ONeq {}
  | OLt {}
  | OGt {}
  | OLe {}
  | OGe {}
  | OShiftL {}
  | OShiftR {}
  | OAdd {}
  | OSub {}
  | OMul {}
  | ODiv {}
  | OMod {}
  | OBOr {}
  | OBAnd {}
  | OXor {}

  syn UnOp =
  | OSizeOf {}
  | ODeref {}
  | OAddrOf {}
  | ONeg {}
  | ONot {}


  -------------
  -- C TYPES --
  -------------

  syn Type =
  -- TyIdent not really needed unless we add typedef
--| TyIdent { id: Name }
  | TyChar {}
  | TyInt {}
  | TyDouble {}
  | TyVoid {}
  | TyPtr { ty: Type }
  | TyFun { ret: Type, params: [Type] }
  | TyArr { ty: Type, size: Option Int }
  | TyStruct { id: Name, mem: Option [(Type,Name)] }
  | TyUnion { id: Name, mem: Option [(Type,Name)] }
  | TyEnum { id: Name, mem: Option [Name] }


  --------------------
  -- C INITIALIZERS --
  --------------------

  syn Init =
  | IExpr { expr: Expr }
  | IList { inits: [Init] }


  ------------------
  -- C STATEMENTS --
  ------------------

  -- We force if, switch, and while to introduce new scopes (by setting the
  -- body type to [Stmt] rather than Stmt). It is allowed in C to have a single
  -- (i.e., not compound) statement as the body, but this statement is NOT
  -- allowed to be a definition. To do this properly, we would need to separate
  -- statements and definitions into different data types.
  syn Stmt =
  | SDef     { ty: Type, id: Option Name, init: Option Init }
  | SIf      { cond: Expr, thn: [Stmt], els: [Stmt] }
  | SSwitch  { cond: Expr, body: [(Int, [Stmt])], default: Option [Stmt] }
  | SWhile   { cond: Expr, body: [Stmt] }
  | SExpr    { expr: Expr }
  | SComp    { stmts: [Stmt] }
  | SRet     { val: Option Expr }
  | SCont    { }
  | SBreak   { }


  -----------------
  -- C TOP-LEVEL --
  -----------------

  syn Top =
  | TDef      { ty: Type, id: Option Name, init: Option Init }
  | TFun      { ret: Type, id: Name, params: [(Type,Name)], body: [Stmt] }

  syn Prog =
  | PProg { tops: [Top] }

end

