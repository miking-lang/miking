-- AST fragment for a subset of the C language, suitable for code generation.

-- NOTE(dlunde,2020-10-29): Missing functionality (most things are probably not
-- needed for code generation or can be expressed through other language
-- constructs):
--
-- * Includes/module system
-- * Labeled statements and goto
-- * Storage class specifiers (typedef, auto, register, static, extern)
-- * Type qualifiers (const, volatile)
-- * Increment/decrement operators
-- * Combined assignment operators (e.g. +=, *=)
-- * Ternary operator (cond ? expr : expr)
-- * DoWhile, For

-- NOTE(dlunde,2020-10-30):
--
-- * Identifiers are _not_ checked for validity. You must make sure they are
--   valid in your own code.
--
-- * Definitions have optional identifiers and initializers to allow for
--   declaring struct/union/enum types without instantiating them
--   ```
--   struct ty { ... members ... };
--   ```
--   and to initialize variables directly
--   ```
--   int arr[] = {1, 2, 3};
--   ```
--   To keep the AST clean, however, this currently also allows for incorrect
--   definitions such as
--   ```
--   int *;
--   ```
--   and
--   ```
--   int = 1;
--   ```
--   which are not valid in C.

include "name.mc"

lang CAst

  -------------------
  -- C EXPRESSIONS --
  -------------------

  syn CExpr =
  | CEVar        { id: Name }
  | CEApp        { fun: Name, args: [CExpr] }
  | CEInt        { i: Int }
  | CEFloat      { f: Float }
  | CEChar       { c: Char }
  | CEString     { s: String }
  | CEBinOp      { op: CBinOp, lhs: CExpr, rhs: CExpr }
  | CEUnOp       { op: CUnOp, arg: CExpr }
  | CEMember     { lhs: CExpr, id: String }
  | CECast       { ty: CType, rhs: CExpr }
  | CESizeOfType { ty: CType }

  syn CBinOp =
  | COAssign {}
  | COSubScript {}
  | COOr {}
  | COAnd {}
  | COEq {}
  | CONeq {}
  | COLt {}
  | COGt {}
  | COLe {}
  | COGe {}
  | COShiftL {}
  | COShiftR {}
  | COAdd {}
  | COSub {}
  | COMul {}
  | CODiv {}
  | COMod {}
  | COBOr {}
  | COBAnd {}
  | COXor {}

  syn CUnOp =
  | COSizeOf {}
  | CODeref {}
  | COAddrOf {}
  | CONeg {}
  | CONot {}


  -------------
  -- C TYPES --
  -------------

  syn CType =
  -- CTyIdent not really needed unless we add typedef
--| CTyIdent { id: Name }
  | CTyChar {}
  | CTyInt {}
  | CTyDouble {}
  | CTyVoid {}
  | CTyPtr { ty: CType }
  | CTyFun { ret: CType, params: [CType] }
  | CTyArray { ty: CType, size: Option Int }
  | CTyStruct { id: Name, mem: Option [(CType,String)] }
  | CTyUnion { id: Name, mem: Option [(CType,String)] }
  | CTyEnum { id: Name, mem: Option [Name] }


  --------------------
  -- C INITIALIZERS --
  --------------------

  syn CInit =
  | CIExpr { expr: CExpr }
  | CIList { inits: [CInit] }


  ------------------
  -- C STATEMENTS --
  ------------------
  -- We force if, switch, and while to introduce new scopes (by setting the
  -- body type to [CStmt] rather than CStmt). It is allowed in C to have a single
  -- (i.e., not compound) statement as the body, but this statement is NOT
  -- allowed to be a definition. To do this properly, we would need to separate
  -- statements and definitions into different data types.

  syn CStmt =
  | CSDef     { ty: CType, id: Option Name, init: Option CInit }
  | CSIf      { cond: CExpr, thn: [CStmt], els: [CStmt] }
  | CSSwitch  { cond: CExpr, body: [(Int, [CStmt])], default: Option [CStmt] }
  | CSWhile   { cond: CExpr, body: [CStmt] }
  | CSExpr    { expr: CExpr }
  | CSComp    { stmts: [CStmt] }
  | CSRet     { val: Option CExpr }
  | CSCont    { }
  | CSBreak   { }


  -----------------
  -- C TOP-LEVEL --
  -----------------

  syn CTop =
  | CTDef { ty: CType, id: Option Name, init: Option CInit }
  | CTFun { ret: CType, id: Name, params: [(CType,Name)], body: [CStmt] }

  syn CProg =
  | CPProg { includes: [String], tops: [CTop] }

end

