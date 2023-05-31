include "ast.mc"
include "ast-builder.mc"
include "eq.mc"

lang MExprRemoveTypeAscription = MExprAst
  sem removeTypeAscription : Expr -> Expr
  sem removeTypeAscription =
  | (TmLet {ident = idLet, body = body, inexpr = TmVar {ident = idExpr}}) & letexpr ->
    if nameEq idLet idExpr then
      removeTypeAscription body
    else smap_Expr_Expr removeTypeAscription letexpr
  | expr -> smap_Expr_Expr removeTypeAscription expr
end

lang TestLang = MExprAst + MExprRemoveTypeAscription + MExprEq
end

mexpr
use TestLang in

let t1 = bind_ (ulet_ "x" (int_ 1)) (var_ "x") in
utest removeTypeAscription t1
with int_ 1 using eqExpr in

let t2 = bind_ (ulet_ "x" t1) (var_ "x") in
utest removeTypeAscription t2
with int_ 1 using eqExpr in

()
