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
include "option.mc"

-------------
-- C TYPES --
-------------
lang CTypeAst

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

end


-------------------
-- C EXPRESSIONS --
-------------------
lang CExprAst = CTypeAst

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

  sem sfold_CExpr_CExpr (f: a -> CExpr -> a) (acc: a) =
  | CEVar _        -> acc
  | CEApp t        -> foldl f acc t.args
  | CEInt _        -> acc
  | CEFloat _      -> acc
  | CEChar _       -> acc
  | CEString _     -> acc
  | CEBinOp t      -> f (f acc t.lhs) t.rhs
  | CEUnOp t       -> f acc t.arg
  | CEMember t     -> f acc t.lhs
  | CEArrow t      -> f acc t.lhs
  | CECast t       -> f acc t.rhs
  | CESizeOfType _ -> acc

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

end


--------------------
-- C INITIALIZERS --
--------------------
lang CInitAst = CExprAst

  syn CInit =
  | CIExpr { expr: CExpr }
  | CIList { inits: [CInit] }

  sem sfold_CInit_CExpr (f: a -> CExpr -> a) (acc: a) =
  | CIExpr t -> f acc t.expr
  | CIList t -> foldl (sfold_CInit_CExpr f) acc t.inits

end

------------------
-- C STATEMENTS --
------------------
lang CStmtAst = CTypeAst + CInitAst + CExprAst
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

  sem smap_CStmt_CStmt (f: CStmt -> a) =
  | CSDef t -> CSDef t
  | CSIf t -> CSIf {{ t with thn = map f t.thn } with els = map f t.els }
  | CSSwitch t -> error "TODO"
  | CSWhile t -> error "TODO"
  | CSExpr t -> CSExpr t
  | CSComp t -> error "TODO"
  | CSRet t -> CSRet t
  | CSCont t -> CSCont t
  | CSBreak t -> CSBreak t
  | CSNop t -> CSNop t

  sem sfold_CStmt_CExpr (f: a -> CExpr -> a) (acc: a) =
  | CSDef t -> optionMapOrElse (lam. acc) (sfold_CInit_CExpr f acc) t.init
  | CSIf t ->
    let sf = sfold_CStmt_CExpr f in
    foldl sf (foldl sf (f acc t.cond) t.thn) t.els
  | CSSwitch t -> error "TODO"
  | CSWhile t -> error "TODO"
  | CSExpr t -> f acc t.expr
  | CSComp t -> error "TODO"
  | CSRet t -> optionMapOrElse (lam. acc) (f acc) t.val
  | CSCont _ -> acc
  | CSBreak _ -> acc
  | CSNop _ -> acc

  sem sreplace_CStmt_CStmt (f: CStmt -> [CStmt]) =
  | CSDef t -> CSDef t
  | CSIf t ->
    let thn = join (map f t.thn) in
    let els = join (map f t.els) in
    CSIf {{ t with thn = thn } with els = els }
  | CSSwitch t -> error "TODO"
  | CSWhile t -> error "TODO"
  | CSExpr t -> CSExpr t
  | CSComp t -> error "TODO"
  | CSRet t -> CSRet t
  | CSCont t -> CSCont t
  | CSBreak t -> CSBreak t
  | CSNop t -> CSNop t

end


-----------------
-- C TOP-LEVEL --
-----------------
lang CTopAst = CTypeAst + CInitAst + CStmtAst

  syn CTop =
  -- Type definitions are supported at this level.
  | CTTyDef { ty: CType, id: Name }
  | CTDef { ty: CType, id: Option Name, init: Option CInit }
  | CTFun { ret: CType, id: Name, params: [(CType,Name)], body: [CStmt] }

  sem sreplace_CTop_CStmt (f: CStmt -> [CStmt]) =
  | CTTyDef _ & t -> t
  | CTDef _ & t -> t
  | CTFun t -> CTFun { t with body = join (map f t.body) }

end

-----------------------
-- COMBINED FRAGMENT --
-----------------------
lang CAst = CExprAst + CTypeAst + CInitAst + CStmtAst + CTopAst


---------------
-- C PROGRAM --
---------------
lang CProgAst = CTopAst
  -- We support including a set of header files at the top of the program.

  syn CProg =
  | CPProg { includes: [String], tops: [CTop] }

end
