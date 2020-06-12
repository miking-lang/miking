-- AST for a subset of the C language.

include "mexpr/ast.mc"

lang CExprAst = VarAst + ConstAst + IntAst + FloatAst + CharAst
  syn Expr =
    | TmAssg { lhs: Expr, rhs: Expr }
    | TmApp { fun: String, args: [Expr] }

    -- TODO Many other things missing, for instance:
    -- * Operators. We cannot reuse operators from mexpr (such as CAddi) since
    --   they are curried. Maybe this will change in the future?
    -- * Pointers
    -- * Arrays
    -- * Unions (NOTE: not tagged unions, aka variants)
    -- * Enums (variants with only nullary constructors)
    -- * Structs (should be reusable if we decompose RecordAst a bit)
end

-- TODO Types (Some reuse from mexpr should be possible after some refactoring)
lang CTypeAst

lang CStmtAst = CExprAst + CTypeAst
  syn Stmt =
    | SDecl     { ty: Type, id: String }
    | SIf       { cond: Expr, thn: Stmt, els: Stmt }
    | SWhile    { cond: Expr, body: Stmt }
    | SFor      { init: Expr, cond: Expr, after: Expr }
    | SRet      { val: Option }
    | SExpr     { expr: Expr }
    | SBlock    { stmts: [Stmt] }
    | SNop      {}
end

lang CTopAst = CStmtAst + CTypeAst
  syn Top =
    | TDecl    { ty: Type, id: String }
    | TFunDecl { ty: Type,
                 id: String,
                 params: [{ ty: Type, id: String }]}
    | TFun     { ty: Type,
                 id: String,
                 params: [{ ty: Type, id: String }],
                 body: Stmt }
end

lang CAst = CTopAst
  syn Prog =
    | Prog { tops: [Top] }
end

