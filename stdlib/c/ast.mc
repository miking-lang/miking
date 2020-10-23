-- AST for a subset of the C language.

include "mexpr/ast.mc"

include "name.mc"

-- Missing:
-- * Storage class specifiers (auto, register, static, extern)
-- * Type qualifiers (const, volatile)
-- * typedef
-- * Standard operators. We cannot reuse operators from mexpr (such as CAddi) since
--   they are curried. Maybe this will change in the future?

lang CExprAst = VarAst + ConstAst + IntAst + FloatAst + CharAst
  syn Expr =
  | TmAssg     { lhs: Expr, rhs: Expr }
  | TmApp      { fun: Name, args: [Expr] }
  | TmSubScr   { lhs: Expr, rhs: Expr }
  | TmSubScr   { lhs: Expr, rhs: Expr }
  | TmMemb     { lhs: Expr, rhs: String }
  | TmCast     { lhs: Type, rhs: Expr }
  | TmSize     { arg: Expr }
  | TmSizeType { arg: Type }

  -- NOTE(dlunde,2020-10-21): The below things are missing

  -- Missing:
  -- * Struct pointer access (e.g. structptr->item)
end

lang CTypeAst = CharTypeAst + IntTypeAst + FloatTypeAst + TypeVarAst
  syn Type =
  | TyFun { ret: Type, args: [Type] }
  | TyPtr { to: Type }
  | TyArr { ty: Type, size: Int }
  | TyStruct { id: Option Name, mem: [(Type, String)] }
  | TyUnion { id: Option Name, mem: [(Type, String)] }
  | TEnum { id: Option Name, mem: [Name]}
end

lang CDeclAst
  -- Missing:
  -- * Mulitple declarators within the same declaration.
  -- * Designated initializers (e.g. struct s pi = { .z = "Pi", .x = 3, .y =
  -- 3.1415 };)
  syn Decl =
  | Decl { ty: Type, id: Option Name, init: Option Expr }

  syn Init =
  | IExpr { expr: Expr }
  | IList { inits: [Init] }

end

lang CStmtAst = CExprAst + CTypeAst
  syn Stmt =
  | SDecl     { decl: Decl }
  | SIf       { cond: Expr, thn: Stmt, els: Stmt }
  | SWhile    { cond: Expr, body: Stmt }
  | SFor      { init: Expr, cond: Expr, after: Expr }
  | SRet      { val: Option Expr }
  | SExpr     { expr: Expr }
  | SComp     { stmts: [Stmt] }

  -- Missing:
  -- * switch
  -- * continue
  -- * break
  -- * do-while
  -- * goto
end

lang CTopAst = CStmtAst + CTypeAst
  syn Top =
  | TDecl    { decl: Decl }
  | TFun     { ty: Type,
               id: Name,
               params: [(Type, Name)],
               body: Stmt }
end

lang CAst = CTopAst
  syn C =
  | CProg { tops: [Top] }
end

