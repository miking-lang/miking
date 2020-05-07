-- This file contains proof-of-concept functions for CPS transformation of the
-- basic lambda calculus subset of MExpr. It is based on
-- http://matt.might.net/articles/cps-conversion/.
-- TODO Implement gensym, so that we can remove the CPS variable env (much
-- cleaner).
-- TODO Add full support for MExpr when stable.

include "mexpr.mc"
include "ast-builder.mc"

lang FunCPS = FunAst

  sem cpsK (env: Env) (cont: Expr -> Env -> Expr) =
  | TmLam t -> cont (cpsM env (TmLam t)) env
  | TmVar t -> cont (cpsM env (TmVar t)) env
  | TmApp t ->
    let rv = fresh "rv" env in
    let rvvar = var_ rv in
    let env = cons (rv, ()) env in
    let cont = ulam_ rv (cont rvvar env) in
    cpsK
      env
      (lam lhs. lam env.
        cpsK
          env
          (lam rhs. lam env.
            appf2_ lhs rhs cont)
          t.rhs)
      t.lhs

  sem cpsC (env: Env) (cont: Expr) =
  | TmLam t -> app_ cont (cpsM env (TmLam t))
  | TmVar t -> app_ cont (cpsM env (TmVar t))
  | TmApp t ->
    cpsK
      env
      (lam lhs. lam env.
        cpsK
          env
          (lam rhs. lam env.
            appf2_ lhs rhs cont)
          t.rhs)
      t.lhs

  sem cpsM (env: Env) =
  | TmApp t -> error "CPS: TmApp is not atomic"
  | TmVar t -> TmVar t
  | TmLam t ->
    let k = fresh "k" env in
    let kvar = var_ k in
    let env = cons (k, ()) (cons (t.ident, ()) env) in
    lam_ t.ident t.tpe (ulam_ k (cpsC env kvar t.body))

end

mexpr
use FunCPS in

let id = ulam_ "x" (var_ "x") in

utest cpsM [] (var_ "x") with
      var_ "x"
in

utest cpsM [] id with
      ulam_ "x" (ulam_ "k" (app_ (var_ "k") (var_ "x")))
in

utest cpsC [] id (app_ (var_ "a") (var_ "b")) with
      appf2_ (var_ "a") (var_ "b") id
in

utest cpsC [] id (app_
                   (app_ (var_ "a") (var_ "b"))
                   (app_ (var_ "c") (var_ "d"))) with
      appf2_ (var_ "a") (var_ "b")
        (ulam_ "rv"
          (appf2_ (var_ "c") (var_ "d")
            (ulam_ "rv0"
              (appf2_ (var_ "rv") (var_ "rv0") id))))
in

()
