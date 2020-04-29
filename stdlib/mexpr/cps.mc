-- This file contains proof-of-concepts functions for CPS transformation of the
-- basic lambda calculus subset of MExpr. It is based on
-- http://matt.might.net/articles/cps-conversion/.
-- TODO Implement gensym (transformation is incorrect now since it does not use
-- fresh variables)
-- TODO Add full language support when MExpr definition is stable.

-- TODO Seems like the includes are order-dependent here. Including ast-builder
-- before mexpr gives an error. Is this a bug or intentional?
include "mexpr.mc"
include "pprint.mc"
include "ast-builder.mc"

-- TODO Generate fresh symbols
let gensym = lam str. str

lang MExprCPS = MExpr + MExprPrettyPrint

  sem cpsK (cont: Expr -> Expr) =
  | TmApp t ->
    let rv = gensym "rv" in
    let rvvar = var_ rv in
    let cont = ulam_ rv (cont rvvar) in
    cpsK
      (lam lhs.
        cpsK
          (lam rhs.
            appf2_ lhs rhs cont)
          t.rhs)
      t.lhs

  | TmLam t -> cont (cpsM (TmLam t))
  | TmVar t -> cont (cpsM (TmVar t))

  sem cpsC (cont: Expr) =
  | TmApp t ->
    cpsK
      (lam lhs.
        cpsK
          (lam rhs.
            appf2_ lhs rhs cont)
          t.rhs)
      t.lhs

  | TmLam t -> app_ cont (cpsM (TmLam t))
  | TmVar t -> app_ cont (cpsM (TmVar t))

  sem cpsM =
  | TmApp t -> error "CPS: TmApp is not atomic"
  | TmLam t ->
    let k = gensym "k" in
    let kvar = var_ k in
    lam_ t.ident t.tpe (ulam_ k (cpsC kvar t.body))

  | TmVar t -> TmVar t

end

mexpr
use MExprCPS in

let id = ulam_ "x" (var_ "x") in

utest cpsM (var_ "x") with
      var_ "x"
in

utest cpsM id with
      ulam_ "x" (ulam_ "k" (app_ (var_ "k") (var_ "x")))
in

utest cpsC id (app_ (var_ "a") (var_ "b")) with
      appf2_ (var_ "a") (var_ "b") id
in

-- TODO Replace second occurrence of rv with fresh var when this is fixed
utest cpsC id (app_
                (app_ (var_ "a") (var_ "b"))
                (app_ (var_ "c") (var_ "d"))) with
      appf2_ (var_ "a") (var_ "b")
        (ulam_ "rv"
          (appf2_ (var_ "c") (var_ "d")
            (ulam_ "rv"
              (appf2_ (var_ "rv") (var_ "rv") id))))
in

()
