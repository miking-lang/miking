-- AST fragment for a subset of the C language, suitable for code generation.

include "name.mc"

lang CAst =

  -------------------
  -- C EXPRESSIONS --
  -------------------
  -- Missing:
  -- * TODO(dlunde,2020-10-26): Many operators.
  --
  -- NOTE(dlunde,2020-10-28): We cannot reuse operators from mexpr (such as
  -- CAddi) since they are curried. Maybe this will change in the future?

  syn Expr =
  | TmVar        { id: Name }
  | TmApp        { fun: Name, args: [Expr] }
  | TmInt        { i: Int }
  | TmFloat      { f: Float }
  | TmChar       { c: Char }
  | TmUnOp       { op: BinOp, arg: Expr }
  | TmBinOp      { op: UnOp, lhs: Expr, rhs: Expr }
  | TmMemb       { lhs: Expr, id: Name }
  | TmCast       { ty: Type, rhs: Expr }
  | TmSizeOfType { ty: Type }

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

  -- We keep type expressions minimal to avoid dealing with the C type syntax.
  -- To use more complicated types, you first need to bind these to type
  -- identifiers (see Top below).
  syn Type =
  | TyIdent { id: Name }
  | TyChar {}
  | TyInt {}
  | TyDouble {}
  | TyVoid {}

  -------------------
  -- C DEFINITIONS --
  -------------------
  -- Missing:
  -- * More storage class specifiers (auto, register, static, extern)
  -- * Type qualifiers (const, volatile)

  syn Def =
  | DVar { ty: Type, id: Name, init: Option Init }

  syn Init =
  | IExpr { expr: Expr }
  | IList { inits: [Init] }

  ------------------
  -- C STATEMENTS --
  ------------------
  -- Missing:
  -- * Labeled statements and goto

  syn Stmt =
  | SDef     { def: Def }
  | SIf      { cond: Expr, thn: Stmt, els: Stmt }
  | SSwitch  { cond: Expr, body: [(Int, [Stmt])], default: Option [Stmt] }
  | SWhile   { cond: Expr, body: Stmt }
  | SExpr    { expr: Expr }
  | SComp    { stmts: [Stmt] }
  | SRet     { val: Option Expr }
  | SCont    { }
  | SBreak   { }


  -----------------
  -- C TOP-LEVEL --
  -----------------

  syn Top =
  | TDef      { def: Def }
  | TPtrTy    { ty: Type, id: Name }
  | TFunTy    { ret: Type, id: Name, params: [Type] }
  | TArrTy    { ty: Type, size: Int }
  | TStructTy { id: Name, mem: Option [Def] }
  | TUnionTy  { id: Name, mem: Option [Def] }
  | TEnumTy   { id: Name, mem: Option [Name] }
  | TFun      { ty: Type, id: Name, params: [(Type, Name)], body: [Stmt] }

  syn Prog =
  | CProg { tops: [Top] }

end

