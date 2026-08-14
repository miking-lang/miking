include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/free-vars.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "digraph.mc"
include "map.mc"
include "seq.mc"
include "name.mc"
include "set.mc"

-- Performs a "demotion" of all recursive bindings in the given expression.
-- The result is that
-- 1. Bindings that do not make use of recursion at all are translated to
--    let-expressions.
-- 2. Bindings are split up into multiple recursive let-expressions, such that
--    all bindings of each resulting recursive let are dependent on each other.
lang MExprDemoteRecursive = MExprAst + MExprFreeVars
  sem demoteRecursive : Expr -> Expr
  sem demoteRecursive =
  | tm & TmOpaque _ -> tm
  | tm -> smap_Expr_Expr demoteRecursive tm
  | TmDecl (x & {decl = DeclRecLets t}) ->
    let f = lam acc. lam binding.
      ( mapInsert binding.ident (binding, freeVars binding.body) acc
      , {binding with body = demoteRecursive binding.body}
      ) in
    match mapAccumL f (mapEmpty nameCmp) t.bindings with (usedMap, bindings) in
    let g = mapFoldWithKey (lam g. lam k. lam. digraphMaybeAddVertex k g)
      (digraphEmpty nameCmp (lam. lam. true))
      usedMap in
    let f = lam g. lam from. lam pair.
      setFold (lam g. lam to. if mapMem to usedMap then digraphAddEdge from to () g else g) g pair.1 in
    let g = mapFoldWithKey f g usedMap in
    let attachGroup = lam group. lam inexpr.
      switch group
      case [] then
        -- TODO(vipa, 2025-03-19): Is this even possible? It's in the
        -- old code
        inexpr
      case [name] then
        match mapFindExn name usedMap with (binding, free) in
        if setMem name free
        then TmDecl
          {x with decl = DeclRecLets {t with bindings = [binding]}
          , inexpr = inexpr
          }
        else TmDecl
          {x with decl = DeclLet
            {ident = binding.ident
            , tyAnnot = binding.tyAnnot
            , tyBody = binding.tyBody
            , body = binding.body
            , info = binding.info
            }
          , inexpr = inexpr
          , ty = x.ty
          }
      case names then
        let bindings = mapReverse (lam name. (mapFindExn name usedMap).0) names in
        TmDecl {x with decl = DeclRecLets {t with bindings = bindings}, inexpr = inexpr}
      end in
    let inexpr = demoteRecursive x.inexpr in
    foldr attachGroup inexpr (digraphTarjan g)
end

lang TestLang = MExprDemoteRecursive + MExprEq end

mexpr

use TestLang in

let t = symbolize (bind_ (ureclets_ [
  ("a", ulam_ "x" (app_ (var_ "b") (var_ "x"))),
  ("b", ulam_ "y" (app_ (var_ "b") (var_ "y")))
]) unit_) in
let expected = symbolize (bindall_ [
  ureclets_ [ ("b", ulam_ "y" (app_ (var_ "b") (var_ "y"))) ],
  ulet_ "a" (ulam_ "x" (app_ (var_ "b") (var_ "x")))
] unit_) in
utest demoteRecursive t with expected using eqExpr in

let t = symbolize (bind_ (ureclets_ [
  ("a", ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ("b", ulam_ "x" (app_ (var_ "c") (var_ "x"))),
  ("c", ulam_ "x" (app_ (var_ "b") (var_ "x"))),
  ("d", ulam_ "x" (bind_
    (ulet_ "e" (ulam_ "y" (app_ (var_ "c") (var_ "x"))))
    (app_ (var_ "e") (var_ "x")))),
  ("f", ulam_ "x" (app_ (var_ "a") (var_ "x")))
]) unit_) in
let expected = symbolize (bindall_ [
  ulet_ "a" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ureclets_ [
    ("b", ulam_ "x" (app_ (var_ "c") (var_ "x"))),
    ("c", ulam_ "x" (app_ (var_ "b") (var_ "x"))) ],
  ulet_ "d" (ulam_ "x" (bind_
    (ulet_ "e" (ulam_ "y" (app_ (var_ "c") (var_ "x"))))
    (app_ (var_ "e") (var_ "x")))),
  ulet_ "f" (ulam_ "x" (app_ (var_ "a") (var_ "x")))
] unit_) in
utest demoteRecursive t with expected using eqExpr in

let t = symbolize (bind_ (ureclets_ [
  ("b", ulam_ "y" (muli_ (var_ "y") (app_ (var_ "a") (int_ 3)))),
  ("c", ulam_ "z" (subi_ (var_ "z") (app_ (var_ "b") (int_ 2)))),
  ("a", ulam_ "x" (addi_ (var_ "x") (int_ 2)))
]) unit_) in
let expected = symbolize (bindall_ [
  ulet_ "a" (ulam_ "x" (addi_ (var_ "x") (int_ 2))),
  ulet_ "b" (ulam_ "y" (muli_ (var_ "y") (app_ (var_ "a") (int_ 3)))),
  ulet_ "c" (ulam_ "z" (subi_ (var_ "z") (app_ (var_ "b") (int_ 2))))]
  unit_
) in
utest demoteRecursive t with expected using eqExpr in

()
