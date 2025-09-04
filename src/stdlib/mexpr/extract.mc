-- Performs an extraction of an MExpr AST, where the bindings corresponding to
-- a given set of identifiers are extracted from a provided AST.
--
-- The extraction assumes all bindings that are to be part of the extraction
-- are in the top-level of the program. That is, they cannot be nested in a
-- let-expression, for example. This can be achieved through lambda lifting.

include "digraph.mc"
include "name.mc"
include "set.mc"
include "mexpr/ast.mc"
include "mexpr/type-check.mc"
include "mexpr/free-vars.mc"

lang MExprExtract = MExprAst + MExprFreeNames
  sem extractAst : Set Name -> Expr -> Expr
  sem extractAst identifiers = | ast ->
    -- NOTE(larshum, 2022-09-06): In the base case, we return the integer
    -- literal 0, rather than an empty record, as the former works better in
    -- our C compiler.
    let defaultBase = TmConst
      { val = CInt {val = 0}
      , ty = TyInt {info = NoInfo ()}
      , info = NoInfo ()
      } in
    (extractAstExpr identifiers defaultBase ast).1

  sem extractAstExpr : Set Name -> Expr -> Expr -> (Set Name, Expr)
  sem extractAstExpr used base = | tm ->
    match tm with TmDecl (x & {decl = decl, inexpr = expr}) then
      match extractAstExpr used base expr with (used, expr) in
      match extractAstDecl used decl with Some (used, decl)
      then (used, TmDecl {x with decl = decl, inexpr = expr})
      else (used, expr)
    else (used, base)

  sem extractAstDecl : Set Name -> Decl -> Option (Set Name, Decl)
  sem extractAstDecl used =
  -- NOTE(vipa, 2025-03-19): Utests cannot be used; they don't define
  -- anything
  | DeclUtest _ -> None ()

  -- NOTE(vipa, 2025-03-19): All these define exactly one name that's
  -- only in scope after the Decl, thus they can be treated
  -- identically
  | decl & (DeclConDef {ident = ident} | DeclLet {ident = ident} | DeclType {ident = ident} | DeclExt {ident = ident}) ->
    if setMem ident used then
      let used = mapRemove ident used in
      let used = sfold_Decl_Expr freeNamesExpr used decl in
      let used = sfold_Decl_Type freeNamesType used decl in
      Some (used, decl)
    else None ()

  -- NOTE(vipa, 2025-03-19): RecLets are harder because they define
  -- multiple things simultaneously with potential mutual dependency
  | DeclRecLets x ->
    let bindingToUsed = lam acc. lam binding.
      let usedHere = freeNames binding.body in
      let usedHere = freeNamesType usedHere binding.tyAnnot in
      mapInsert binding.ident usedHere acc in
    let usedInBindings = foldl bindingToUsed (mapEmpty nameCmp) x.bindings in
    let transitiveClosure
      : all x. (Map x (Set x)) -> Set x -> Set x
      = lam trans. lam initial.
        recursive let work = lam curr. lam new.
          let findNew = lam acc. lam x.
            optionMapOr acc (setUnion acc) (mapLookup x trans) in
          let new = setSubtract (setFold findNew (setEmpty (mapGetCmpFun curr)) new) curr in
          if setIsEmpty new then curr else
          work (setUnion curr new) new in
        work initial initial in
    let used = transitiveClosure usedInBindings used in
    match filter (lam b. setMem b.ident used) x.bindings with bindings & ([_] ++ _) then
      let used = foldl (lam used. lam b. setRemove b.ident used) used bindings in
      Some (used, DeclRecLets {x with bindings = bindings})
    else None ()
end

lang TestLang =
  MExprExtract + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam t. typeCheck (symbolize t) in
let setOfSeq = lam ids. setOfSeq nameCmp ids in

let f = nameSym "f" in
let g = nameSym "g" in
let h = nameSym "h" in
let tmp = nameSym "tmp" in
let t = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ g (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  nulet_ h (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  nulet_ tmp (app_ (nvar_ h) (int_ 2))]
  (nvar_ tmp
)) in
let extractF = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1)))]
  (int_ 0
)) in
utest extractAst (setOfSeq [f]) t with extractF using eqExpr in

let extractG = preprocess (bindall_ [
  nulet_ g (ulam_ "x" (muli_ (var_ "x") (int_ 2)))]
  (int_ 0
)) in
utest extractAst (setOfSeq [g]) t with extractG using eqExpr in

let extractTmp = preprocess (bindall_ [
  nulet_ h (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  nulet_ tmp (app_ (nvar_ h) (int_ 2))]
  (int_ 0
)) in
utest extractAst (setOfSeq [tmp]) t with extractTmp using eqExpr in

let t = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ g (ulam_ "x" (muli_ (app_ (nvar_ f) (var_ "x")) (int_ 2))),
  nulet_ h (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  nulet_ tmp (app_ (nvar_ g) (int_ 4))]
  (nvar_ tmp
)) in

let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ g (ulam_ "x" (muli_ (app_ (nvar_ f) (var_ "x")) (int_ 2))),
  nulet_ tmp (app_ (nvar_ g) (int_ 4))]
  (int_ 0
)) in
utest extractAst (setOfSeq [tmp]) t with extracted using eqExpr in

let t1 = nameSym "t" in
let t2 = nameSym "t" in
let distinctCalls = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  nulet_ g (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (app_ (nvar_ f) (int_ 1)),
  nulet_ t2 (app_ (nvar_ g) (int_ 0))]
  (addi_ (nvar_ t1) (nvar_ t2)
)) in
let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  nulet_ g (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (app_ (nvar_ f) (int_ 1)),
  nulet_ t2 (app_ (nvar_ g) (int_ 0))]
  (int_ 0
)) in
utest extractAst (setOfSeq [t1, t2]) distinctCalls with extracted using eqExpr in

let inRecursiveBinding = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  nureclets_ [
    (g, ulam_ "x" (app_ (nvar_ f) (addi_ (var_ "x") (int_ 1)))),
    (h, ulam_ "x" (app_ (nvar_ t1) (var_ "x"))),
    (t1, ulam_ "x" (app_ (nvar_ g) (var_ "x")))
  ]]
  (app_ (nvar_ h) (int_ 3)
)) in
let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  nureclets_ [
    (g, ulam_ "x" (app_ (nvar_ f) (addi_ (var_ "x") (int_ 1)))),
    (t1, ulam_ "x" (app_ (nvar_ g) (var_ "x")))]]
  (int_ 0
)) in
utest extractAst (setOfSeq [t1]) inRecursiveBinding with extracted using eqExpr in

-- Tests that a binding that is used by multiple extracted bindings is only
-- included once in the extracted AST.
let multipleDependOnSame = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (ulam_ "x" (ulam_ "y" (
    addi_ (var_ "x") (app_ (nvar_ f) (var_ "y"))))),
  nulet_ t2 (ulam_ "x" (ulam_ "y" (
    muli_ (var_ "x") (app_ (nvar_ f) (var_ "y")))))]
  (addi_ (appf2_ (nvar_ t1) (int_ 0) (int_ 1)) (appf2_ (nvar_ t2) (int_ 3) (int_ 4))
)) in
let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (ulam_ "x" (ulam_ "y" (
    addi_ (var_ "x") (app_ (nvar_ f) (var_ "y"))))),
  nulet_ t2 (ulam_ "x" (ulam_ "y" (
    muli_ (var_ "x") (app_ (nvar_ f) (var_ "y")))))]
  (int_ 0
)) in
utest extractAst (setOfSeq [t1, t2]) multipleDependOnSame with extracted using eqExpr in

-- NOTE(larshum, 2023-05-30): This test checks that the type referred to only
-- by an external is included, even if type-checking has not ran yet (meaning
-- there are no other references to the type in the expression).
let extTypeDependency = preprocess (bindall_ [
  type_ "t" [] (tyvariant_ []),
  ext_ "fun" false (tyarrow_ tyint_ (tycon_ "t")),
  nulet_ f (ulam_ "x" (app_ (var_ "fun") (var_ "x")))]
  (int_ 0
)) in
utest expr2str (extractAst (setOfSeq [f]) extTypeDependency)
with expr2str extTypeDependency using eqString in

-- NOTE(larshum, 2024-04-17): We only run symbolization, to expose a (now
-- fixed) bug in the collection of type identifiers in constructor definitions.
let extConApp = symbolize (bindall_ [
  type_ "T" [] (tyvariant_ []),
  condef_ "Con" (tyarrow_ tyint_ (tycon_ "T")),
  nulet_ f (ulam_ "x" (var_ "x")),
  nulet_ g (ulam_ "y" (conapp_ "Con" (app_ (nvar_ f) (var_ "y"))))]
  (int_ 0
)) in
utest expr2str (extractAst (setOfSeq [g]) extConApp)
with expr2str extConApp using eqString in

let multiConExtract = preprocess (bindall_ [
  type_ "T" [] (tyvariant_ []),
  condef_ "A" (tyarrow_ tyint_ (tycon_ "T")),
  nlet_ f (tyarrow_ tyint_ (tycon_ "T")) (ulam_ "x" (conapp_ "A" (var_ "x")))]
  (int_ 0
)) in
utest expr2str (extractAst (setOfSeq [f]) multiConExtract)
with expr2str multiConExtract using eqString in

()
