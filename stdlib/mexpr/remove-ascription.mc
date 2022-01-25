include "ast.mc"
include "ast-builder.mc"
include "eq.mc"

recursive
let removeTypeAscription = use MExprAst in
  lam expr.
    match expr with TmLet {ident = idLet, body = body, inexpr = inexpr} then
      match inexpr with TmVar {ident = idExpr} then
        if nameEq idLet idExpr then removeTypeAscription body
        else smap_Expr_Expr removeTypeAscription expr
      else smap_Expr_Expr removeTypeAscription expr
    else smap_Expr_Expr removeTypeAscription expr
end

lang TestLang = MExprAst + MExprEq
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
