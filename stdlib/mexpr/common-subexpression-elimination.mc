-- Implementation of local common subexpression elimination, performed at the
-- innermost lambda of a let-expression or recursive binding. This
-- implementation assumes that the given expression has no side-effects.

include "mexpr/anf.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"

lang CSE = MExprCmpClosed
  sem cseCount (exprCount : Map Expr Int) =
  | t -> sfold_Expr_Expr cseCount exprCount t

  sem cseReplace (exprReplace : Map Expr Name) =
  | t -> smap_Expr_Expr (cseReplace exprReplace) t

  sem cse =
  | t -> smap_Expr_Expr cse t
end

lang AppCSE = CSE + AppAst + VarAst
  sem cseCount (exprCount : Map Expr Int) =
  | TmApp t ->
    match mapLookup (TmApp t) exprCount with Some cnt then
      mapInsert (TmApp t) (addi cnt 1) exprCount
    else
      let exprCount = mapInsert (TmApp t) 1 exprCount in
      cseCount (cseCount exprCount t.lhs) t.rhs

  sem cseReplace (exprReplace : Map Expr Name) =
  | TmApp t ->
    match mapLookup (TmApp t) exprReplace with Some id then
      TmVar {ident = id, ty = t.ty, info = t.info}
    else
      TmApp {{t with lhs = cseReplace exprReplace t.lhs}
                with rhs = cseReplace exprReplace t.rhs}
end

lang LamCSE = CSE + LamAst
  sem cse =
  | TmLam t ->
    -- Only run common subexpression elimination on the innermost body of a
    -- series of lambda expressions.
    match t.body with !(TmLam _) then
      -- Count the number of times each expression occurs within the body to
      -- identify common subexpressions.
      let bodyExprCount = cseCount (mapEmpty cmpExpr) t.body in
      let commonSubexpressions =
        filter
          (lam entry : (Expr, Int).
            gti entry.1 1)
          (mapBindings bodyExprCount) in

      -- Create a new variable for each common subexpression and replace all
      -- occurrences of that expression with the variable. Then add a
      -- let-expression at the top of the body to assign the subexpression to
      -- the new variable.
      let expressionReplacements =
        mapFromSeq cmpExpr
          (map
            (lam entry : (Expr, Int).
              (entry.0, nameSym "t"))
            commonSubexpressions) in
      let body = cseReplace expressionReplacements t.body in
      let body =
        mapFoldWithKey
          (lam acc. lam key : Expr. lam value : Name.
            TmLet {ident = value, tyBody = ty key, body = key,
                   inexpr = acc, ty = ty acc, info = infoTm key})
          body
          expressionReplacements in
      TmLam {t with body = body}
    else TmLam {t with body = cse t.body}
end

lang DataCSE = CSE + DataAst + VarAst
  sem cseCount (exprCount : Map Expr Int) =
  | TmConApp t ->
    match mapLookup (TmConApp t) exprCount with Some cnt then
      mapInsert (TmConApp t) (addi cnt 1) exprCount
    else
      let exprCount = mapInsert (TmConApp t) 1 exprCount in
      cseCount exprCount t.body

  sem cseReplace (exprReplace : Map Expr Name) =
  | TmConApp t ->
    match mapLookup (TmConApp t) exprReplace with Some id then
      TmVar {ident = id, ty = t.ty, info = t.info}
    else
      TmConApp {t with body = cseReplace exprReplace t.body}
end

lang MExprCSE = AppCSE + LamCSE + DataCSE

lang TestLang = MExprCSE + MExprEq + MExprPrettyPrint

mexpr

use TestLang in

let t =
  ulet_ "f" (ulam_ "n" (bindall_ [
    ulet_ "x" (muli_ (int_ 2) (var_ "n")),
    ulet_ "y" (addi_ (int_ 4) (muli_ (int_ 2) (var_ "n"))),
    addi_ (var_ "x") (var_ "y")
  ])) in
let expected = 
  ulet_ "f" (ulam_ "n" (bindall_ [
    ulet_ "t" (muli_ (int_ 2) (var_ "n")),
    ulet_ "x" (var_ "t"),
    ulet_ "y" (addi_ (int_ 4) (var_ "t")),
    addi_ (var_ "x") (var_ "y")
  ])) in
utest cse t with expected using eqExpr in
utest cse expected with expected using eqExpr in

let t = bindall_ [
  ulet_ "a" (addi_ (var_ "b") (var_ "c")),
  ulet_ "b" (addi_ (var_ "a") (int_ 1)),
  ulet_ "c" (addi_ (var_ "b") (var_ "c")),
  addi_ (var_ "b") (var_ "c")
] in
utest cse t with t using eqExpr in

let t = ureclets_ [
  ("takeNonEmpty", ulam_ "s" (ulam_ "n" (
    if_ (eqi_ (length_ (var_ "s")) (int_ 1))
      (head_ (var_ "s"))
      (cons_
        (head_ (var_ "s"))
        (appf2_ (var_ "takeNonEmpty") (tail_ (var_ "s")) (subi_ (var_ "n") (int_ 1))))
  )))
] in
let expected = ureclets_ [
  ("takeNonEmpty", ulam_ "s" (ulam_ "n" (
    bind_
      (ulet_ "h" (head_ (var_ "s")))
      (if_ (eqi_ (length_ (var_ "s")) (int_ 1))
        (var_ "h")
        (cons_
          (var_ "h")
          (appf2_ (var_ "takeNonEmpty") (tail_ (var_ "s")) (subi_ (var_ "n") (int_ 1)))))
  )))
] in
utest cse t with expected using eqExpr in
utest cse expected with expected using eqExpr in

let t = ureclets_ [
  ("f", ulam_ "p" (ulam_ "s" (bindall_ [
    ulet_ "h" (head_ (var_ "s")),
    if_ (app_ (var_ "p") (var_ "h"))
      (cons_ (var_ "h") (appf2_ (var_ "f") (var_ "p") (tail_ (var_ "s"))))
      (appf2_ (var_ "f") (var_ "p") (tail_ (var_ "s")))
  ])))
] in
let expected = ureclets_ [
  ("f", ulam_ "p" (ulam_ "s" (bindall_ [
    ulet_ "t" (appf2_ (var_ "f") (var_ "p") (tail_ (var_ "s"))),
    ulet_ "h" (head_ (var_ "s")),
    if_ (app_ (var_ "p") (var_ "h"))
      (cons_ (var_ "h") (var_ "t"))
      (var_ "t")
  ])))
] in
utest cse t with expected using eqExpr in
utest cse expected with expected using eqExpr in

let t = ulam_ "" (
  if_ (app_ (var_ "f") (conapp_ "CInt" (var_ "r")))
    (conapp_ "CInt" (var_ "r"))
    (conapp_ "CInt" (var_ "r"))
) in
let expected = ulam_ "" (bindall_ [
  ulet_ "t" (conapp_ "CInt" (var_ "r")),
  if_ (app_ (var_ "f") (var_ "t"))
    (var_ "t")
    (var_ "t")
]) in
utest cse t with expected using eqExpr in
utest cse expected with expected using eqExpr in

()
