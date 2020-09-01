-- This file contains proof-of-concept functions for CPS transformation of the
-- basic lambda calculus subset of MExpr. It is based on
-- http://matt.might.net/articles/cps-conversion/.
-- TODO Add full support for MExpr when stable.

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"

lang FunCPS = FunSym

  sem cpsK (cont: Expr -> Expr) =
  | TmLam t -> cont (cpsM (TmLam t))
  | TmVar t -> cont (cpsM (TmVar t))
  | TmApp t ->
    let rv = nameSym "rv" in
    let rvvar = nvar_ rv in
    let cont = nulam_ rv (cont rvvar) in
    cpsK
      (lam lhs.
        cpsK
          (lam rhs.
            appf2_ lhs rhs cont)
          t.rhs)
      t.lhs

  sem cpsC (cont: Expr) =
  | TmLam t -> app_ cont (cpsM (TmLam t))
  | TmVar t -> app_ cont (cpsM (TmVar t))
  | TmApp t ->
    cpsK
      (lam lhs.
        cpsK
          (lam rhs.
            appf2_ lhs rhs cont)
          t.rhs)
      t.lhs

  sem cpsM =
  | TmApp t -> error "CPS: TmApp is not atomic"
  | TmVar t -> TmVar t
  | TmLam t ->
    let k = nameSym "k" in
    let kvar = nvar_ k in
    nlam_ t.ident t.tpe (nulam_ k (cpsC kvar t.body))

end

mexpr
use FunCPS in

let _s = symbolize [] in

let id = _s (ulam_ "x" (var_ "x")) in

-- TODO This is currently not working since the symbols differ between the LHS
-- and RHS. Implement equality check between terms that takes care of symbols?
-- utest cpsM id
-- with _s (ulam_ "x" (ulam_ "k" (app_ (var_ "k") (var_ "x")))) in

-- TODO Add more test cases

()
