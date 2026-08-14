-- This file provides attributes (see `mexpr/attribute-grammar.mc`)
-- for finding all places where each `Name` is defined in the AST.
--
-- To use, supply a `DefinedAttr (mkThunk "DefinedAttr#root")`
-- to `processAst`, then read from it afterwards.

include "mexpr/ast.mc"
include "mexpr/invariants.mc"
include "mexpr/invariants/in-scope.mc"

include "mexpr/cmp.mc"
include "map.mc"
include "name.mc"
include "thunk.mc"
include "common.mc"
include "seq.mc"
include "string.mc"
include "set.mc"
include "mexpr/info.mc"
include "tuple.mc"
include "lazy.mc"
include "mexpr/ast-builder.mc"

lang DefinedAttr = Invariant + MExprAst + DeclaredHereAttr
  type DefinedAttr loc = Map Name [loc]
  syn Attr loc +=
  | DefinedAttr (Thunk (DefinedAttr loc))

  sem newAttr label +=
  | DefinedAttr _ -> DefinedAttr (mkThunk label)

  sem attrKindToString +=
  | DefinedAttr _ -> "DefinedAttr"

  sem printInvariantSummary +=
  | DefinedAttr x ->
    let start = wallTimeMs () in
    let x = x.read () in
    let timeMs = subf (wallTimeMs ()) start in
    let numNoSym =
      mapFoldWithKey (lam n. lam k. lam. if nameHasSym k then n else addi n 1) 0 x in
    let numMultiDef = mapFoldWithKey
      (lam n. lam. lam defs. match defs with [_, _] ++ _ then addi n 1 else n) 0 x in
    printLn (join
      [ "  Definitions: ", int2string numNoSym, " names without symbols, "
      , int2string numMultiDef, " with multiple definitions ("
      , float2string timeMs, "ms)."
      ])

  sem openDefinedAttr : all loc. Attr loc -> Thunk (DefinedAttr loc)
  sem openDefinedAttr = | DefinedAttr x -> x

  sem addDefinitions : all loc. loc -> InScopeAttr loc -> DefinedAttr loc -> DefinedAttr loc
  sem addDefinitions loc scope = | x ->
    let f = lam x. lam n. mapInsertWith concat n [loc] x in
    let x = setFold f x scope.values in
    let x = setFold f x scope.constructors in
    let x = setFold f x scope.tyValues in
    let x = setFold f x scope.tyConstructors in
    x

  sem processDefinedExpr : all loc. InvEnv loc -> InvState -> loc -> Expr -> (InvState, DefinedAttr loc -> DefinedAttr loc)
  sem processDefinedExpr env st loc =
  | TmLam x -> (st, mapInsertWith concat x.ident [loc])
  | TmDecl x ->
    match willRead st (openInScopeAttr (getAttrDecl (DeclaredHere noThunk) x.decl)) with (st, readDecl) in
    ( st
    , lam definitions.
      let res = readDecl () in
      addDefinitions loc res definitions
    )
  | _ -> (st, lam x. x)

  sem processDefinedType : all loc. loc -> Type -> DefinedAttr loc -> DefinedAttr loc
  sem processDefinedType loc =
  | TyAll x -> mapInsertWith concat x.ident [loc]
  | _ -> lam x. x

  sem processAttrDecl env st loc +=
  | pair & (_, DefinedAttr _) ->
    simpleSynthesizedDecl st
      pair
      openDefinedAttr
      (mapEmpty nameCmp)
      (mapUnionWith concat)
      (lam x. x)

  sem processAttrExpr env st loc +=
  | (TmMatch x, attr & DefinedAttr here) ->
    match willWrite st here with (st, writeHere) in
    match willRead st (openDefinedAttr (getAttrExpr attr x.target)) with (st, readTarget) in
    match willRead st (openInScopeAttr (getAttrPat (DeclaredHere noThunk) x.pat)) with (st, readPat) in
    match willRead st (openDefinedAttr (getAttrExpr attr x.thn)) with (st, readThn) in
    match willRead st (openDefinedAttr (getAttrExpr attr x.els)) with (st, readEls) in
    ( st
    , lam.
      let res = mapUnionWith concat (readTarget ()) (readThn ()) in
      let res = mapUnionWith concat res (readEls ()) in
      let res = addDefinitions loc (readPat ()) res in
      writeHere res
    )
  | pair & (tm, DefinedAttr _) ->
    match processDefinedExpr env st loc tm with (st, addHere) in
    simpleSynthesizedExpr st
      pair
      openDefinedAttr
      (mapEmpty nameCmp)
      (mapUnionWith concat)
      addHere

  sem processAttrType env st loc +=
  | pair & (ty, DefinedAttr _) ->
    simpleSynthesizedType st
      pair
      openDefinedAttr
      (mapEmpty nameCmp)
      (mapUnionWith concat)
      (processDefinedType loc ty)
end

lang TestLang = DefinedAttr + MExprCmp
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
let eq = eqSeq (tupleEq2 nameEq (eqSeq locEq)) in

-- NOTE(vipa, 2026-03-04): Two helpers for attaching two distinct info
-- fields to each kind of node
let itm = withInfo (infoVal "i" 0 0 0 0) in
let jtm = withInfo (infoVal "j" 0 0 0 0) in
let ity = tyWithInfo (infoVal "i" 0 0 0 0) in
let jty = tyWithInfo (infoVal "j" 0 0 0 0) in
let idecl = declWithInfo (infoVal "i" 0 0 0 0) in
let jdecl = declWithInfo (infoVal "j" 0 0 0 0) in
let ipat = withInfoPat (infoVal "i" 0 0 0 0) in
let jpat = withInfoPat (infoVal "j" 0 0 0 0) in

let check = lam ast.
  let attrs = [DefinedAttr (mkThunk (lazyPure "DefinedAttr#root"))] in
  let res = processAst attrs ast in
  match getAttrEnv (DefinedAttr noThunk) res with DefinedAttr thunk in
  mapBindings (thunk.read ()) in


-- === Actual tests ===

utest check (bindall_ [ulet_ "x" unit_, ulet_ "x" (int_ 1)] unit_) with
  [ ( nameNoSym "x"
    , [ LocExpr (bindall_ [ulet_ "x" (int_ 1)] unit_)
      , LocExpr (bindall_ [ulet_ "x" unit_, ulet_ "x" (int_ 1)] unit_)
      ]
    )
  ] using eq in
utest check (match_ unit_ (por_ (pvar_ "x") pvarw_) unit_ unit_) with [] using eq in
utest check (match_ unit_ (por_ (pvar_ "x") (pvar_ "x")) unit_ unit_) with
  [ (nameNoSym "x", [LocExpr (match_ unit_ (por_ (pvar_ "x") (pvar_ "x")) unit_ unit_)])
  ] using eq in

()
