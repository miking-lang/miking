-- AST fragments for the C language.

include "mexpr/ast.mc"

include "name.mc"

---------------
-- TEMPLATES --
---------------

lang Expr
  syn Expr =
  -- Intentionally left blank
end

lang Type
  syn Type =
  -- Intentionally left blank
end

lang Decl
  syn Decl =
  -- Intentionally left blank
end

lang Stmt
  syn Stmt =
  -- Intentionally left blank
end


-------------------
-- C EXPRESSIONS --
-------------------
-- Missing:
-- * TODO Standard operators. We cannot reuse operators from mexpr (such as
-- CAddi) since they are curried. Maybe this will change in the future?
-- * Struct pointer access (e.g. structptr->item)

lang AssgExpr
  syn Expr =
  | TmAssg { lhs: Expr, rhs: Expr }
end

lang AppExpr
  syn Expr =
  | TmApp { fun: Name, args: [Expr] }
end

lang SubScrExpr
  syn Expr =
  | TmSubScr { lhs: Expr, rhs: Expr }
end

lang MembExpr
  syn Expr =
  | TmMemb { lhs: Expr, rhs: String }
end

lang CastExpr = Type
  syn Expr =
  | TmCast { lhs: Type, rhs: Expr }
end

lang SizeOfExpr
  syn Expr =
  | TmSizeOf { arg: Expr }
end

lang SizeOfTypeExpr = Type
  syn Expr =
  | TmSizeOfType { arg: Type }
end


-------------
-- C TYPES --
-------------

lang FunType
  syn Type =
  | TyFun { ret: Type, params: [Type] }
end

lang PtrType
  syn Type =
  | TyPtr { ty: Type }
end

lang ArrType
  syn Type =
  | TyArr { ty: Type, size: Int }
end

lang StructType
  syn Type =
  | TyStruct { id: Option Name, mem: [(Type, String)] }
end

lang UnionType
  syn Type =
  | TyUnion { id: Option Name, mem: [(Type, String)] }
end

lang EnumType
  syn Type =
  | TyEnum { id: Option Name, mem: [Name]}
end


--------------------
-- C DECLARATIONS --
--------------------
-- Missing:
-- * Multiple declarators within the same declaration.
-- * Designated initializers (e.g. struct s pi = { .z = "Pi", .x = 3, .y =
-- 3.1415 };)
-- * Storage class specifiers (auto, register, static, extern)
-- * Type qualifiers (const, volatile)

lang DeclDecl = Type + Expr
  syn Decl =
  | DDecl { ty: Type, id: Option Name, init: Option Init }

  -- NOTE(dlunde,2020-10-24): Declarations with initializers could form a
  -- separate language fragment.
  syn Init =
  | IExpr { expr: Expr }
  | IList { inits: [Init] }

end

lang TypeDefDecl = Type
  syn Decl =
  | DTypeDef { ty: Type, id: Name }
end


------------------
-- C STATEMENTS --
------------------
-- Missing:
-- * goto (including labeled statements)

lang DeclStmt = Decl
  syn Stmt =
  | SDecl { decl: Decl }
end

lang IfStmt = Expr
  syn Stmt =
  | SIf { cond: Expr, thn: Stmt, els: Stmt }
end

lang SwitchStmt
  syn Stmt =
  | SSwitch { cond: Expr, body: [(Int, Stmt)], default: Option Stmt }
end

lang WhileStmt
  syn Stmt =
  | SWhile { cond: Expr, body: Stmt }
end

lang DoWhileStmt
  syn Stmt =
  | SDoWhile { body: Stmt, cond: Expr }
end

lang ForStmt
  syn Stmt =
  | SFor { init: Expr, cond: Expr, after: Expr, body: Stmt }
end

lang ExprStmt
  syn Stmt =
  | SExpr { expr: Expr }
end

lang CompStmt
  syn Stmt =
  | SComp { stmts: [Stmt] }
end

lang RetStmt
  syn Stmt =
  | SRet { val: Option Expr }
end

lang ContStmt
  syn Stmt =
  | SCont {}
end

lang BreakStmt
  syn Stmt =
  | SBreak {}
end


-----------------
-- C TOP-LEVEL --
-----------------

lang DeclTop
  syn Top =
  | TDecl { decl: Decl }
end

lang FunTop
  syn Top =
  | TFun { ty: Type, id: Name, params: [(Type, Name)], body: Stmt }
end

lang CompTop
  syn Top =
  | TComp { tops: [Top] }
end


--------------------
-- C AST FRAGMENT --
--------------------

lang CAst =

  -- Expressions (some reuse from mexpr/ast.mc)
  VarAst + ConstAst + IntAst + FloatAst + CharAst + AssgExpr + AppExpr +
  SubScrExpr + MembExpr + CastExpr + SizeOfExpr + SizeOfTypeExpr +

  -- Types (some reuse from mexpr/ast.mc)
  CharTypeAst + IntTypeAst + FloatTypeAst + TypeVarAst + FunType + PtrType +
  ArrType + StructType + UnionType + EnumType +

  -- Declarations
  DeclDecl + TypeDefDecl +

  -- Statements
  DeclStmt + IfStmt + SwitchStmt + WhileStmt + DoWhileStmt + ForStmt + ExprStmt
  + CompStmt + RetStmt + ContStmt + BreakStmt +

  -- Top-level
  DeclTop + FunTop + CompTop

