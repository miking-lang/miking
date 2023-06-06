include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/call-graph.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"

-- Performs a "demotion" of all recursive bindings in the given expression.
-- The result is that
-- 1. Bindings that do not make use of recursion at all are translated to
--    let-expressions.
-- 2. Bindings are split up into multiple recursive let-expressions, such that
--    all bindings of each resulting recursive let are dependent on each other.
lang MExprDemoteRecursive = MExprAst + MExprCallGraph
  sem demoteRecursive : Expr -> Expr
  sem demoteRecursive =
  | TmRecLets t ->
    let demoteBindingBody = lam bind.
      {bind with body = demoteRecursive bind.body}
    in
    let bindingId = lam bind. (bind.ident, bind) in
    let constructRecLets = lam acc. lam binds.
      TmRecLets {bindings = binds, inexpr = acc, ty = tyTm acc, info = t.info}
    in
    let bindings = map demoteBindingBody t.bindings in
    let g = constructCallGraph (TmRecLets {t with bindings = bindings}) in
    let sccs = digraphTarjan g in
    let bindMap = mapFromSeq nameCmp (map bindingId bindings) in
    foldl
      (lam acc. lam scc.
        let addBind = lam binds. lam componentId.
          -- NOTE(larshum, 2023-04-20): The call graph includes bound identifiers
          -- in the bodies of the bindings, but we only care about the bindings.
          match mapLookup componentId bindMap with Some binding then
            snoc binds binding
          else binds
        in
        let binds = foldl addBind [] scc in
        switch binds
        case [] then acc
        case [bind] then
          if isSelfRecursive bind.ident false bind.body then
            constructRecLets acc [bind]
          else toLetBinding acc bind
        case _ then
          -- NOTE(larshum, 2023-04-20): We intentionally reverse the bindings
          -- to keep them in declaration order.
          constructRecLets acc (reverse binds)
        end)
      (demoteRecursive t.inexpr) (reverse sccs)
  | t -> smap_Expr_Expr demoteRecursive t

  sem isSelfRecursive : Name -> Bool -> Expr -> Bool
  sem isSelfRecursive ident acc =
  | TmVar {ident = id} -> if nameEq ident id then true else acc
  | t -> sfold_Expr_Expr (isSelfRecursive ident) acc t

  sem toLetBinding : Expr -> RecLetBinding -> Expr
  sem toLetBinding inexpr =
  | bind ->
    TmLet {
      ident = bind.ident, tyAnnot = bind.tyAnnot, tyBody = bind.tyBody,
      body = bind.body, inexpr = inexpr, ty = tyTm inexpr, info = bind.info }
end

lang TestLang = MExprDemoteRecursive + MExprEq end

mexpr

use TestLang in

let t = symbolize (ureclets_ [
  ("a", ulam_ "x" (app_ (var_ "b") (var_ "x"))),
  ("b", ulam_ "y" (app_ (var_ "b") (var_ "y")))
]) in
let expected = symbolize (bindall_ [
  ureclets_ [ ("b", ulam_ "y" (app_ (var_ "b") (var_ "y"))) ],
  ulet_ "a" (ulam_ "x" (app_ (var_ "b") (var_ "x")))
]) in
utest demoteRecursive t with expected using eqExpr in

let t = symbolize (ureclets_ [
  ("a", ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ("b", ulam_ "x" (app_ (var_ "c") (var_ "x"))),
  ("c", ulam_ "x" (app_ (var_ "b") (var_ "x"))),
  ("d", ulam_ "x" (bind_
    (ulet_ "e" (ulam_ "y" (app_ (var_ "c") (var_ "x"))))
    (app_ (var_ "e") (var_ "x")))),
  ("f", ulam_ "x" (app_ (var_ "a") (var_ "x")))
]) in
let expected = symbolize (bindall_ [
  ulet_ "a" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ureclets_ [
    ("b", ulam_ "x" (app_ (var_ "c") (var_ "x"))),
    ("c", ulam_ "x" (app_ (var_ "b") (var_ "x"))) ],
  ulet_ "d" (ulam_ "x" (bind_
    (ulet_ "e" (ulam_ "y" (app_ (var_ "c") (var_ "x"))))
    (app_ (var_ "e") (var_ "x")))),
  ulet_ "f" (ulam_ "x" (app_ (var_ "a") (var_ "x")))
]) in
utest demoteRecursive t with expected using eqExpr in

let t = symbolize (ureclets_ [
  ("b", ulam_ "y" (muli_ (var_ "y") (app_ (var_ "a") (int_ 3)))),
  ("c", ulam_ "z" (subi_ (var_ "z") (app_ (var_ "b") (int_ 2)))),
  ("a", ulam_ "x" (addi_ (var_ "x") (int_ 2)))
]) in
let expected = symbolize (bindall_ [
  ulet_ "a" (ulam_ "x" (addi_ (var_ "x") (int_ 2))),
  ulet_ "b" (ulam_ "y" (muli_ (var_ "y") (app_ (var_ "a") (int_ 3)))),
  ulet_ "c" (ulam_ "z" (subi_ (var_ "z") (app_ (var_ "b") (int_ 2)))),
  unit_
]) in
utest demoteRecursive t with expected using eqExpr in

()
