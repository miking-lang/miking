include "mexpr/ast.mc"
include "mlang/loader.mc"

lang Desugar = Ast + OpaqueAst
  sem desugarExpr: Expr -> Expr
  sem desugarExpr =
  | tm & TmOpaque _ -> tm
  | tm -> smap_Expr_Expr desugarExpr tm
end

lang DesugarLoader = Ast + LoaderInterface + OpaqueAst
  syn Hook +=
  | DesugarHook ()

  sem desugarDecl : Loader -> Decl -> (Loader, Decl)
  sem desugarDecl loader = | decl ->
    smapAccumL_Decl_Expr desugarExpr loader decl

  sem desugarExpr : Loader -> Expr -> (Loader, Expr)
  sem desugarExpr loader =
  | expr & TmOpaque _ -> (loader, expr)
  | expr ->
    smapAccumL_Expr_Expr desugarExpr loader expr

  sem enableDesugar : Loader -> Loader
  sem enableDesugar = | loader ->
    if hasHook (lam x. match x with DesugarHook _ then true else false) loader then loader else

    addHook loader (DesugarHook ())

  sem _postTypecheck loader decl += | DesugarHook _ ->
    desugarDecl loader decl
end
