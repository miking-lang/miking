-- This file provides attributes (see `mexpr/attribute-grammar.mc`)
-- for finding nodes in the AST that do not have an info field set.
--
-- To use, supply a `WithoutInfoAttr (mkThunk "WithoutInfoAttr#root")`
-- to `processAst`, then read from it afterwards.

include "mexpr/ast.mc"
include "mexpr/invariants.mc"

include "mexpr/cmp.mc"

lang WithoutInfoAttr = Invariant
  type WithoutInfoAttr loc = [loc]
  syn Attr loc =
  | WithoutInfoAttr (Thunk (WithoutInfoAttr loc))

  sem newAttr label =
  | WithoutInfoAttr _ -> WithoutInfoAttr (mkThunk label)

  sem attrKindToString =
  | WithoutInfoAttr _ -> "WithoutInfoAttr"

  sem printInvariantSummary =
  | WithoutInfoAttr x ->
    let start = wallTimeMs () in
    let x = x.read () in
    let timeMs = subf (wallTimeMs ()) start in
    let numMissing = length x in
    let example =
      match x with [example] ++ _ then
        let lines = strSplit "\n" (loc2str example) in
        let lines = match lines with [l1, l2, l3, _, _] ++ _ ++ [r1, r2, r3]
          then [l1, l2, l3, "...elided...", r1, r2, r3]
          else lines in
        join [" Example:\n    ", strJoin "\n    " lines]
      else "" in
    printLn (join
      [ "  NoInfo: ", int2string numMissing, " missing Info fields ("
      , float2string timeMs, "ms).", example
      ])

  sem openWithoutInfoAttr : all loc. Attr loc -> Thunk (WithoutInfoAttr loc)
  sem openWithoutInfoAttr = | WithoutInfoAttr x -> x

  sem processAttrDecl env st loc =
  | pair & (decl, WithoutInfoAttr _) ->
    simpleSynthesizedDecl st
      pair
      openWithoutInfoAttr
      []
      concat
      (match infoDecl decl with NoInfo _ then cons loc else lam x. x)

  sem processAttrExpr env st loc =
  | pair & (tm, WithoutInfoAttr _) ->
    simpleSynthesizedExpr st
      pair
      openWithoutInfoAttr
      []
      concat
      (match infoTm tm with NoInfo _ then cons loc else lam x. x)

  sem processAttrType env st loc =
  | pair & (TyAlias _, WithoutInfoAttr _) ->
    simpleSynthesizedType st
      pair
      openWithoutInfoAttr
      []
      concat
      (lam x. x)
  | pair & (ty, WithoutInfoAttr _) ->
    simpleSynthesizedType st
      pair
      openWithoutInfoAttr
      []
      concat
      (match infoTy ty with NoInfo _ then cons loc else lam x. x)

  sem processAttrPat env st loc =
  | pair & (pat, WithoutInfoAttr _) ->
    simpleSynthesizedPat st
      pair
      openWithoutInfoAttr
      []
      concat
      (match infoPat pat with NoInfo _ then cons loc else lam x. x)
end

lang TestLang = WithoutInfoAttr + MExprAst + MExprCmp
end

mexpr

use TestLang in

-- NOTE(vipa, 2026-03-04): We check info fields of the top node as
-- well, so we're able to distinguish sub-trees that are otherwise
-- identical
let locEq = lam a. lam b. switch (a, b)
  case (LocExpr a, LocExpr b) then
    if eqi 0 (cmpExpr a b)
    then eqi 0 (infoCmp (infoTm a) (infoTm b))
    else false
  case (LocDecl a, LocDecl b) then
    if eqi 0 (cmpDecl a b)
    then eqi 0 (infoCmp (infoDecl a) (infoDecl b))
    else false
  case (LocType a, LocType b) then
    if eqi 0 (cmpType a b)
    then eqi 0 (infoCmp (infoTy a) (infoTy b))
    else false
  case (LocPat a, LocPat b) then
    if eqi 0 (cmpPat a b)
    then eqi 0 (infoCmp (infoPat a) (infoPat b))
    else false
  end in
let eq = eqSeq locEq in

-- NOTE(vipa, 2026-03-04): Helper for attaching an arbitrary info
-- field to a node
let itm = withInfo (infoVal "i" 0 0 0 0) in
let ity = tyWithInfo (infoVal "i" 0 0 0 0) in
let idecl = declWithInfo (infoVal "i" 0 0 0 0) in
let ipat = withInfoPat (infoVal "i" 0 0 0 0) in

let check = lam ast.
  let attrs = [WithoutInfoAttr (mkThunk (lazyPure "WithoutInfoAttr#root"))] in
  let res = processAst attrs ast in
  match getAttrEnv (WithoutInfoAttr noThunk) res with WithoutInfoAttr thunk in
  thunk.read () in


-- === Actual tests ===

utest check (utuple_ [var_ "x", conapp_ "C" unit_]) with
  [ LocExpr (utuple_ [var_ "x", conapp_ "C" unit_])
  , LocExpr (var_ "x")
  , LocExpr (conapp_ "C" unit_)
  , LocExpr (unit_)
  ] using eq in

utest check (utuple_ [itm (var_ "x"), conapp_ "C" unit_]) with
  [ LocExpr (utuple_ [var_ "x", conapp_ "C" unit_])
  , LocExpr (conapp_ "C" unit_)
  , LocExpr (unit_)
  ] using eq in

utest check (itm (utuple_ [itm (var_ "x"), conapp_ "C" unit_])) with
  [ LocExpr (conapp_ "C" unit_)
  , LocExpr (unit_)
  ] using eq in

utest check (itm (utuple_ [itm (var_ "x"), itm (conapp_ "C" unit_)])) with
  [ LocExpr (unit_)
  ] using eq in

utest check (itm (utuple_ [itm (var_ "x"), itm (conapp_ "C" (itm unit_))])) with
  [] using eq in

utest check (itm (bind_ (let_ "x" tyunit_ (itm unit_)) (itm (match_ (itm (var_ "x")) (pvar_ "y") (itm unit_) (itm unit_))))) with
  [ LocDecl (let_ "x" tyunit_ (itm unit_))
  , LocType tyunit_
  , LocPat (pvar_ "y")
  ] using eq in

utest check (itm (bind_ (idecl (let_ "x" tyunit_ (itm unit_))) (itm (match_ (itm (var_ "x")) (pvar_ "y") (itm unit_) (itm unit_))))) with
  [ LocType tyunit_
  , LocPat (pvar_ "y")
  ] using eq in

utest check (itm (bind_ (idecl (let_ "x" (ity tyunit_) (itm unit_))) (itm (match_ (itm (var_ "x")) (pvar_ "y") (itm unit_) (itm unit_))))) with
  [ LocPat (pvar_ "y")
  ] using eq in

utest check (itm (bind_ (idecl (let_ "x" (ity tyunit_) (itm unit_))) (itm (match_ (itm (var_ "x")) (ipat (pvar_ "y")) (itm unit_) (itm unit_))))) with
  [] using eq in

()
