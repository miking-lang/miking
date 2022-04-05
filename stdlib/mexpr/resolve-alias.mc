-- Resolves all type aliases in an MExpr program, by replacing alias types with
-- the concrete types they represent.

include "mexpr/ast.mc"
include "mexpr/cmp.mc"

lang MExprResolveAlias = MExprAst + Cmp
  sem resolveAliases : Expr -> Expr
  sem resolveAliases =
  | t ->
    match resolveAliasesH (mapEmpty cmpType) t with (_, t) in
    t

  sem resolveAliasesH : Map Type Type -> Expr -> (Map Type Type, Expr)
  sem resolveAliasesH env =
  | TmType t ->
    match t.tyIdent with TyVariant _ then
      let ty = resolveAliasesType env t.ty in
      match resolveAliasesH env t.inexpr with (env, inexpr) in
      (env, TmType {{t with inexpr = inexpr} with ty = ty})
    else
      let srcTy = TyCon {ident = t.ident, info = t.info} in
      let aliasTy = resolveAliasesType env t.tyIdent in
      let env = mapInsert srcTy aliasTy env in
      match resolveAliasesH env t.inexpr with (env, inexpr) in
      (env, inexpr)
  | expr ->
    let ty = resolveAliasesType env (tyTm expr) in
    let expr = withType ty expr in
    let expr = smap_Expr_Type (resolveAliasesType env) expr in
    smapAccumL_Expr_Expr resolveAliasesH env expr

  sem resolveAliasesType : Map Type Type -> Type -> Type
  sem resolveAliasesType env =
  | ty ->
    match mapLookup ty env with Some newTy then
      resolveAliasesType env newTy
    else smap_Type_Type (resolveAliasesType env) ty
end
