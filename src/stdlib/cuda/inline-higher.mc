-- Performs inlining of applications that produce a function-type value, to
-- allow use of higher-order functions in built-in constants such as loop.

include "mexpr/ast.mc"

lang CudaInlineHigherOrder = MExprAst
  sem inlinePartialFunctions : Expr -> Expr
  sem inlinePartialFunctions =
  | expr -> inlinePartialFunctionsH (mapEmpty nameCmp) expr

  sem inlinePartialFunctionsH : Map Name Expr -> Expr -> Expr
  sem inlinePartialFunctionsH inlineBodies =
  | TmVar t ->
    match mapLookup t.ident inlineBodies with Some body then body else TmVar t
  | TmLet (t & {body = !TmLam _}) ->
    match t.tyBody with TyArrow _ then
      let inlineBodies = mapInsert t.ident t.body inlineBodies in
      inlinePartialFunctionsH inlineBodies t.inexpr
    else TmLet {t with body = inlinePartialFunctionsH inlineBodies t.body,
                       inexpr = inlinePartialFunctionsH inlineBodies t.inexpr}
  | t -> smap_Expr_Expr (inlinePartialFunctionsH inlineBodies) t
end
