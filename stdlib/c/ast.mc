-- AST fragment for a subset of the C language, suitable for code generation.

-- NOTE(dlunde,2020-10-29): Missing functionality (most things are probably not
-- needed for code generation or can be expressed through other language
-- constructs):
--
-- * Labeled statements and goto
-- * Storage class specifiers (typedef, auto, register, static, extern)
-- * Type qualifiers (const, volatile)
-- * Increment/decrement operators
-- * Combined assignment operators (e.g. +=, *=)
-- * Ternary operator (cond ? expr : expr)
-- * DoWhile, For
--
-- The above list is of course not exhaustive.

-- NOTE(dlunde,2020-10-30):
--
-- * Identifiers are _not_ checked for validity. You must make sure they are
--   valid C identifiers in your own code.
--
-- * Definitions have optional identifiers and initializers to allow for
--   declaring struct/union/enum types without instantiating them
--
--   struct ty { ... members ... };
--
--   and to initialize variables directly
--
--   int arr[] = {1, 2, 3};
--
--   To keep the AST clean, however, this currently also allows for incorrect
--   definitions such as
--
--   int *;
--
--   int = 1;
--
--   which are not valid in C.
--
-- * Furthermore, to support anonymous structs and unions, the tag is also
--   optional, thus allowing
--
--   struct;
--
--   union;
--
--   which are also not valid in C.

include "name.mc"

lang CAst

  -------------------
  -- C EXPRESSIONS --
  -------------------

  syn CExpr =
  | CEVar        /- Variables -/            { id: Name }
  | CEApp        /- Function application -/ { fun: Name, args: [CExpr] }
  | CEInt        /- Integer literals -/     { i: Int }
  | CEFloat      /- Float literals -/       { f: Float }
  | CEChar       /- Character literals -/   { c: Char }
  | CEString     /- String literals -/      { s: String }
  | CEBinOp      /- Binary operators -/     { op: CBinOp,
                                              lhs: CExpr,
                                              rhs: CExpr }
  | CEUnOp       /- Unary operators -/      { op: CUnOp, arg: CExpr }
  | CEMember     /- lhs.id -/               { lhs: CExpr, id: String }
  | CEArrow      /- lhs->id -/              { lhs: CExpr, id: String }
  | CECast       /- (ty) rhs -/             { ty: CType, rhs: CExpr }
  | CESizeOfType /- sizeof(ty) -/           { ty: CType }

  syn CBinOp =
  | COAssign    /- lhs = rhs -/  {}
  | COSubScript /- lhs[rhs] -/   {}
  | COOr        /- lhs || rhs -/ {}
  | COAnd       /- lhs && rhs -/ {}
  | COEq        /- lhs == rhs -/ {}
  | CONeq       /- lhs != rhs -/ {}
  | COLt        /- lhs < rhs -/  {}
  | COGt        /- lhs > rhs -/  {}
  | COLe        /- lhs <= rhs -/ {}
  | COGe        /- lhs >= rhs -/ {}
  | COShiftL    /- lhs << rhs -/ {}
  | COShiftR    /- lhs >> rhs -/ {}
  | COAdd       /- lhs + rhs -/  {}
  | COSub       /- lhs - rhs -/  {}
  | COMul       /- lhs * rhs -/  {}
  | CODiv       /- lhs / rhs -/  {}
  | COMod       /- lhs % rhs -/  {}
  | COBOr       /- lhs | rhs -/  {}
  | COBAnd      /- lhs & rhs -/  {}
  | COXor       /- lhs ^ rhs -/  {}

  syn CUnOp =
  | COSizeOf /- sizeof(arg) -/ {}
  | CODeref  /- *arg -/        {}
  | COAddrOf /- &arg -/        {}
  | CONeg    /- -arg -/        {}
  | CONot    /- ~arg -/        {}


  -------------
  -- C TYPES --
  -------------

  syn CType =
  | CTyVar    { id: Name }
  | CTyChar   {}
  | CTyInt    {}
  | CTyDouble {}
  | CTyVoid   {}
  | CTyPtr    { ty: CType }
  | CTyFun    { ret: CType, params: [CType] }
  | CTyArray  { ty: CType, size: Option Int }
  | CTyStruct { id: Option Name, mem: Option [(CType,Option String)] }
  | CTyUnion  { id: Option Name, mem: Option [(CType,Option String)] }
  | CTyEnum   { id: Option Name, mem: Option [Name] }


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
  -- body type to [CStmt] rather than CStmt). It is allowed in C to have a
  -- single (i.e., not compound) statement as the body, but this statement is
  -- NOT allowed to be a definition. To do this properly, we would need to have
  -- separate data types for statements and definitions.

  syn CStmt =
  | CSDef     { ty: CType, id: Option Name, init: Option CInit }
  | CSIf      { cond: CExpr, thn: [CStmt], els: [CStmt] }
  | CSSwitch  { cond: CExpr, body: [(Int, [CStmt])], default: Option [CStmt] }
  | CSWhile   { cond: CExpr, body: [CStmt] }
  | CSExpr    { expr: CExpr }
  | CSComp    { stmts: [CStmt] }
  | CSRet     { val: Option CExpr }
  | CSCont    {}
  | CSBreak   {}
  | CSNop     {}


  -----------------
  -- C TOP-LEVEL --
  -----------------
  -- We support including a set of header files at the top of the program.
  -- Type definitions are supported at this level as well.

  syn CTop =
  | CTTyDef { ty: CType, id: Name }
  | CTDef { ty: CType, id: Option Name, init: Option CInit }
  | CTFun { ret: CType, id: Name, params: [(CType,Name)], body: [CStmt] }

  syn CProg =
  | CPProg { includes: [String], tops: [CTop] }

end

