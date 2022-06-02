-- CPS tranformation for MExpr terms in ANF (produced by MExprANFAll in anf.mc).

include "ast.mc"
include "ast-builder.mc"
include "boot-parser.mc"
include "eq.mc"
include "anf.mc"

lang CPS = LamAst + VarAst + LetAst

  sem cps : Expr -> Expr
  sem cps =
  | e -> cpsCont (ulam_ "x" (var_ "x")) e

  sem cpsCont : Expr -> Expr -> Expr

end

lang VarCPS = CPS + VarAst + AppAst
  sem cpsCont k =
  | TmVar _ & t-> app_ k t
end

lang AppCPS = CPS + AppAst
  sem cpsCont k =
  | TmLet { ident = ident, body = TmApp app, inexpr = inexpr } ->
    let tailCall =
      match inexpr with TmVar { ident = varIdent } then nameEq ident varIdent
      else false
    in
    if tailCall then
      -- Optimize tail call
      appf2_ app.lhs k app.rhs
    else
      let inexpr = cpsCont k inexpr in
      let kName = nameSym "k" in
      let k = nulam_ ident inexpr in
      bindall_ [
        nulet_ kName k,
        appf2_ app.lhs (nvar_ kName) app.rhs
      ]
end

lang LamCPS = CPS + LamAst
  sem cpsCont k =
  | TmLet ({ ident = ident, body = TmLam t, inexpr = inexpr } & r) ->
    let kName = nameSym "k" in
    let body =
      nulam_ kName (TmLam {t with body = cpsCont (nvar_ kName) t.body}) in
    TmLet { r with body = body }
end

lang MExprCPS = CPS + VarCPS + AppCPS + LamCPS
end

-----------
-- TESTS --
-----------

lang Test = MExprCPS + BootParser + MExprEq + MExprANFAll
end
mexpr
use Test in

let _parse =
  parseMExprString { defaultBootParserParseMExprStringArg with allowFree = true }
in
let _cps = lam e. cps (normalizeTerm (_parse e)) in
utest _cps "
  a b
" with _parse "
  a (lam x. x) b
" using eqExpr in

()
