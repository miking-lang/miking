-- This file contains functions for CPS transformation of component
-- languages of MExpr.

include "ast.mc"
include "ast-builder.mc"
include "eval.mc"

lang VarCPS = VarAst + AppAst
  sem cpsAtomic (env: Env) =
  | TmVar t -> TmVar t
  sem cpsComplex (env: Env) (cont: Expr) =
  | TmVar t -> app_ cont (cpsAtomic (TmVar t))
  sem cps =
  | TmVar t -> cpsAtomic [] (TmVar t)
end

lang AppCPS = AppAst
  sem cpsComplex (env: Env) (cont: Expr) =
  | TmApp t -> error "TODO: CPS App"
  sem cps =
  | TmApp t ->
  let str = "x" in
  let var = var_ str in
  let id = lam_ str None var in
  cpsComplex [] id (TmApp t)
end

lang FunCPS = FunAst
  sem cpsAtomic (env: Env) =
  | TmLam t -> error "TODO"
  sem cpsComplex (env: Env) (cont: Expr) =
  | TmLam t -> app_ cont (cpsAtomic (TmVar t))
end

lang MExprCPS = VarCPS + AppCPS + FunCPS
