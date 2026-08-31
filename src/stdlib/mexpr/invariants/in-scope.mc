-- This file provides attributes (see `mexpr/attribute-grammar.mc`)
-- for checking if names used are actually bound and in scope.
--
-- To use, supply a `InScopeAttr (filledThunk <initial-environment>)`
-- and `UnboundErrorAttr (mkThunk "UnboundErrorAttr#root")` to
-- `processAst`, then read from the `UnboundErrorAttr` afterwards.

include "mexpr/ast.mc"
include "mexpr/invariants.mc"

include "mexpr/cmp.mc"
include "tuple.mc"
include "mexpr/attribute-grammar.mc"
include "set.mc"
include "name.mc"
include "map.mc"
include "thunk.mc"
include "seq.mc"
include "string.mc"
include "common.mc"
include "mexpr/info.mc"
include "lazy.mc"
include "mexpr/ast-builder.mc"

-- The `DeclaredHere` attribute is a helper attribute, and is used to
-- compute declarations that can "float upwards":
-- * Names introduced by `Decl`s flow up to the containing `TmDecl`,
--   then on to its `inexpr`.
-- * Names introduced by `Pat`s flow up to the containing `TmMatch`,
--   then on to its `thn`.
-- * Names introduced by (potentially nested) `TyAll`s that are
--   top-most in a type signature of a `let` flow to the body of the
--   `let`
lang DeclaredHereAttr = AttributeGrammar + MExprAst
  -- TODO(vipa, 2026-03-02): Make something extensible that can attach attributes to each name
  type InScopeAttr loc =
    { values : Set Name
    , constructors : Set Name
    , tyValues : Set Name
    , tyConstructors : Set Name
    }

  sem _scopeMerge : all loc. InScopeAttr loc -> InScopeAttr loc -> InScopeAttr loc
  sem _scopeMerge a = | b ->
    { values = mapUnion a.values b.values
    , constructors = mapUnion a.constructors b.constructors
    , tyValues = mapUnion a.tyValues b.tyValues
    , tyConstructors = mapUnion a.tyConstructors b.tyConstructors
    }

  sem _scopeIntersect : all loc. InScopeAttr loc -> InScopeAttr loc -> InScopeAttr loc
  sem _scopeIntersect a = | b ->
    { values = mapIntersectWith (lam a. lam. a) a.values b.values
    , constructors = mapIntersectWith (lam a. lam. a) a.constructors b.constructors
    , tyValues = mapIntersectWith (lam a. lam. a) a.tyValues b.tyValues
    , tyConstructors = mapIntersectWith (lam a. lam. a) a.tyConstructors b.tyConstructors
    }

  sem _scopeValues : all loc. [Name] -> InScopeAttr loc
  sem _scopeValues = | names ->
    { values = setOfSeq nameCmp names
    , constructors = setEmpty nameCmp
    , tyValues = setEmpty nameCmp
    , tyConstructors = setEmpty nameCmp
    }

  sem _scopeConstructors : all loc. [Name] -> InScopeAttr loc
  sem _scopeConstructors = | names ->
    { values = setEmpty nameCmp
    , constructors = setOfSeq nameCmp names
    , tyValues = setEmpty nameCmp
    , tyConstructors = setEmpty nameCmp
    }

  sem _scopeTyValues : all loc. [Name] -> InScopeAttr loc
  sem _scopeTyValues = | names ->
    { values = setEmpty nameCmp
    , constructors = setEmpty nameCmp
    , tyValues = setOfSeq nameCmp names
    , tyConstructors = setEmpty nameCmp
    }

  sem _scopeTyConstructors : all loc. [Name] -> InScopeAttr loc
  sem _scopeTyConstructors = | names ->
    { values = setEmpty nameCmp
    , constructors = setEmpty nameCmp
    , tyValues = setEmpty nameCmp
    , tyConstructors = setOfSeq nameCmp names
    }

  sem _scopeEmpty : all loc. () -> InScopeAttr loc
  sem _scopeEmpty = | _ ->
    { values = setEmpty nameCmp
    , constructors = setEmpty nameCmp
    , tyValues = setEmpty nameCmp
    , tyConstructors = setEmpty nameCmp
    }

  syn Attr loc +=
  | DeclaredHere (Thunk (InScopeAttr loc))

  sem newAttr label +=
  | DeclaredHere _ -> DeclaredHere (mkThunk label)

  sem attrKindToString +=
  | DeclaredHere _ -> "DeclaredHere"

  sem openInScopeAttr : all loc. Attr loc -> Thunk (InScopeAttr loc)
  sem openInScopeAttr =
  | DeclaredHere x -> x

  sem processAttrDecl env st loc +=
  | (DeclLet x, DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    (st, lam. writeHere (_scopeValues [x.ident]))
  | (DeclRecLets x, DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    (st, lam. writeHere (_scopeValues (map (lam b. b.ident) x.bindings)))
  | (DeclType x, DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    (st, lam. writeHere (_scopeTyConstructors [x.ident]))
  | (DeclConDef x, DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    (st, lam. writeHere (_scopeConstructors [x.ident]))
  | (DeclExt x, DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    (st, lam. writeHere (_scopeValues [x.ident]))
  | (DeclUtest _, DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    (st, lam. writeHere (_scopeEmpty ()))

  sem processDeclaredHerePat : all loc. loc -> Pat -> InScopeAttr loc -> InScopeAttr loc
  sem processDeclaredHerePat loc =
  | PatNamed {ident = PName n}
  | PatSeqEdge {middle = PName n} -> lam scope. _scopeMerge scope (_scopeValues [n])
  | PatNamed {ident = PWildcard _}
  | PatSeqTot _
  | PatSeqEdge {middle = PWildcard _}
  | PatRecord _
  | PatCon _
  | PatInt _
  | PatChar _
  | PatBool _
  | PatAnd _
  | PatNot _ -> lam x. x

  sem processAttrPat env st loc +=
  | pair & (PatOr x, attr & DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    match willRead st (openInScopeAttr (getAttrPat attr x.lpat)) with (st, readL) in
    match willRead st (openInScopeAttr (getAttrPat attr x.rpat)) with (st, readR) in
    ( st
    , lam.
      writeHere (_scopeIntersect (readL ()) (readR ()))
    )
  | pair & (pat, DeclaredHere _) ->
    simpleSynthesizedPat st
      pair
      openInScopeAttr
      (_scopeEmpty ())
      _scopeMerge
      (processDeclaredHerePat loc pat)

  sem processAttrType env st loc +=
  | (TyAll x, attr & DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    match willRead st (openInScopeAttr (getAttrType attr x.ty)) with (st, readTy) in
    ( st
    , lam.
      writeHere (_scopeMerge (readTy ()) (_scopeTyValues [x.ident]))
    )
  -- TODO(vipa, 2026-03-02): TyMeta and TyAlias?
  | (_, DeclaredHere here) ->
    match willWrite st here with (st, writeHere) in
    (st, lam. writeHere (_scopeEmpty ()))
end

lang InScopeAttr = AttributeGrammar + DeclaredHereAttr
  syn Attr loc +=
  | InScopeAttr (Thunk (InScopeAttr loc))

  sem newAttr label +=
  | InScopeAttr _ -> InScopeAttr (mkThunk label)

  sem attrKindToString +=
  | InScopeAttr _ -> "InScopeAttr"

  sem openInScopeAttr +=
  | InScopeAttr x -> x

  sem processAttrExpr env st loc +=
  | (TmLam x, attr & InScopeAttr here) ->
    match willRead st here with (st, readHere) in
    match willWrite st (openInScopeAttr (getAttrType attr x.tyAnnot)) with (st, writeTyAnnot) in
    match willWrite st (openInScopeAttr (getAttrExpr attr x.body)) with (st, writeBody) in
    ( st
    , lam.
      let here = readHere () in
      writeTyAnnot here;
      writeBody (_scopeMerge here (_scopeValues [x.ident]))
    )
  | (TmDecl x, attr & InScopeAttr here) ->
    match willRead st here with (st, readHere) in
    match willRead st (openInScopeAttr (getAttrDecl (DeclaredHere noThunk) x.decl)) with (st, readDecl) in
    match willWrite st (openInScopeAttr (getAttrDecl attr x.decl)) with (st, writeDecl) in
    match willWrite st (openInScopeAttr (getAttrExpr attr x.inexpr)) with (st, writeInexpr) in
    ( st
    , lam.
      let here = readHere () in
      writeDecl here;
      writeInexpr (_scopeMerge here (readDecl ()))
    )
  | (TmMatch x, attr & InScopeAttr here) ->
    match willRead st here with (st, readHere) in
    match willRead st (openInScopeAttr (getAttrPat (DeclaredHere noThunk) x.pat)) with (st, readPat) in
    match willWrite st (openInScopeAttr (getAttrPat attr x.pat)) with (st, writePat) in
    match willWrite st (openInScopeAttr (getAttrExpr attr x.thn)) with (st, writeThn) in
    match willWrite st (openInScopeAttr (getAttrExpr attr x.target)) with (st, writeTarget) in
    match willWrite st (openInScopeAttr (getAttrExpr attr x.els)) with (st, writeEls) in
    ( st
    , lam.
      let here = readHere () in
      writePat here;
      writeEls here;
      writeTarget here;
      writeThn (_scopeMerge here (readPat ()))
    )
  | pair & (_, InScopeAttr _) ->
    simpleInheritedExpr st pair openInScopeAttr (lam x. x)

  sem processAttrDecl env st loc +=
  | (DeclLet x, attr & InScopeAttr here) ->
    match willRead st here with (st, readHere) in
    match willRead st (openInScopeAttr (getAttrType (DeclaredHere noThunk) x.tyAnnot)) with (st, readTyAnnot) in
    match willWrite st (openInScopeAttr (getAttrType attr x.tyAnnot)) with (st, writeTyAnnot) in
    match willWrite st (openInScopeAttr (getAttrExpr attr x.body)) with (st, writeBody) in
    ( st
    , lam.
      let here = readHere () in
      writeTyAnnot here;
      writeBody (_scopeMerge here (readTyAnnot ()))
    )
  | (DeclRecLets x, attr & InScopeAttr here) ->
    match willRead st here with (st, readHere) in
    match willRead st (openInScopeAttr (getAttrEnv (DeclaredHere noThunk) env)) with (st, readDeclaredHere) in
    let f = lam st. lam b.
      match willRead st (openInScopeAttr (getAttrType (DeclaredHere noThunk) b.tyAnnot)) with (st, readTyAnnot) in
      match willWrite st (openInScopeAttr (getAttrType attr b.tyAnnot)) with (st, writeTyAnnot) in
      match willWrite st (openInScopeAttr (getAttrExpr attr b.body)) with (st, writeBody) in
      (st, {readTyAnnot = readTyAnnot, writeTyAnnot = writeTyAnnot, writeBody = writeBody}) in
    match mapAccumL f st x.bindings with (st, bs) in
    ( st
    , lam.
      let here = _scopeMerge (readHere ()) (readDeclaredHere ()) in
      for_ bs (lam b. b.writeTyAnnot here; b.writeBody (_scopeMerge here (b.readTyAnnot ())))
    )
  | (DeclType x, attr & InScopeAttr here) ->
    match willRead st here with (st, readHere) in
    match willWrite st (openInScopeAttr (getAttrType attr x.tyIdent)) with (st, writeTyIdent) in
    ( st
    , lam.
      writeTyIdent (_scopeMerge (readHere ()) (_scopeTyValues x.params))
    )
  | pair & (DeclConDef _ | DeclUtest _ | DeclExt _, InScopeAttr _) ->
    simpleInheritedDecl st pair openInScopeAttr (lam x. x)

  sem processAttrPat env st loc +=
  | pair & (_, InScopeAttr _) ->
    simpleInheritedPat st pair openInScopeAttr (lam x. x)

  sem processInScopeAttrType : all loc. loc -> Type -> InScopeAttr loc -> InScopeAttr loc
  sem processInScopeAttrType loc =
  | TyAll x -> lam scope. _scopeMerge scope (_scopeTyValues [x.ident])
  | _ -> lam x. x

  sem processAttrType env st loc +=
  | pair & (ty, InScopeAttr _) ->
    simpleInheritedType st pair openInScopeAttr (processInScopeAttrType loc ty)
end

lang UnboundErrorAttr = Invariant + InScopeAttr
  type UnboundErrorAttr loc = Map Name [loc]
  syn Attr loc +=
  | UnboundErrorAttr (Thunk (UnboundErrorAttr loc))

  sem newAttr label +=
  | UnboundErrorAttr _ -> UnboundErrorAttr (mkThunk label)

  sem attrKindToString +=
  | UnboundErrorAttr _ -> "UnboundErrorAttr"

  sem printInvariantSummary +=
  | UnboundErrorAttr x ->
    let start = wallTimeMs () in
    let x = x.read () in
    let timeMs = subf (wallTimeMs ()) start in
    let numUnbound = mapSize x in
    let numLocations = mapFoldWithKey (lam n. lam. lam locs. addi n (length locs)) 0 x in
    let examples =
      match mapFoldWithKey (lam acc. lam n. lam. if gti (length acc) 5 then acc else snoc acc n) [] x
      with names & ![] then join [" (e.g. ", seq2string nameGetStr names, ")"]
      else "" in
    printLn (join
      [ "  Unbound: ", int2string numUnbound, " unbound in "
      , int2string numLocations, " locations", examples
      , " (", float2string timeMs , "ms)."
      ])

  sem openUnboundErrorAttr : all loc. Attr loc -> Thunk (UnboundErrorAttr loc)
  sem openUnboundErrorAttr = | UnboundErrorAttr x -> x

  sem processUnboundErrorAttrExpr : all loc. InvEnv loc -> InvState -> loc -> Expr -> (InvState, UnboundErrorAttr loc -> UnboundErrorAttr loc)
  sem processUnboundErrorAttrExpr env st loc =
  | TmVar x ->
    match willRead st (openInScopeAttr (getAttrEnv (InScopeAttr noThunk) env)) with (st, readScope) in
    ( st
    , lam scope.
      if setMem x.ident (readScope ()).values
      then scope
      else mapInsertWith concat x.ident [loc] scope
    )
  | TmConApp x ->
    match willRead st (openInScopeAttr (getAttrEnv (InScopeAttr noThunk) env)) with (st, readScope) in
    ( st
    , lam scope.
      if setMem x.ident (readScope ()).constructors
      then scope
      else mapInsertWith concat x.ident [loc] scope
    )
  | _ -> (st, lam x. x)

  sem processUnboundErrorAttrType : all loc. InvEnv loc -> InvState -> loc -> Type -> (InvState, UnboundErrorAttr loc -> UnboundErrorAttr loc)
  sem processUnboundErrorAttrType env st loc =
  | TyCon x ->
    match willRead st (openInScopeAttr (getAttrEnv (InScopeAttr noThunk) env)) with (st, readScope) in
    ( st
    , lam scope.
      if setMem x.ident (readScope ()).tyConstructors
      then scope
      else mapInsertWith concat x.ident [loc] scope
    )
  | TyVar x ->
    match willRead st (openInScopeAttr (getAttrEnv (InScopeAttr noThunk) env)) with (st, readScope) in
    ( st
    , lam scope.
      if setMem x.ident (readScope ()).tyValues
      then scope
      else mapInsertWith concat x.ident [loc] scope
    )
  -- TODO(vipa, 2026-03-04): TyData and TyVariant?
  | _ -> (st, lam x. x)

  sem processUnboundErrorAttrPat : all loc. InvEnv loc -> InvState -> loc -> Pat -> (InvState, UnboundErrorAttr loc -> UnboundErrorAttr loc)
  sem processUnboundErrorAttrPat env st loc =
  | PatCon x ->
    match willRead st (openInScopeAttr (getAttrEnv (InScopeAttr noThunk) env)) with (st, readScope) in
    ( st
    , lam scope.
      if setMem x.ident (readScope ()).constructors
      then scope
      else mapInsertWith concat x.ident [loc] scope
    )
  | _ -> (st, lam x. x)

  sem processAttrDecl env st loc +=
  | pair & (x, UnboundErrorAttr _) ->
    simpleSynthesizedDecl st
      pair
      openUnboundErrorAttr
      (mapEmpty nameCmp)
      (mapUnionWith concat)
      (lam x. x)

  sem processAttrExpr env st loc +=
  | pair & (x, UnboundErrorAttr _) ->
    match processUnboundErrorAttrExpr env st loc x with (st, addHere) in
    simpleSynthesizedExpr st
      pair
      openUnboundErrorAttr
      (mapEmpty nameCmp)
      (mapUnionWith concat)
      addHere

  sem processAttrType env st loc +=
  | pair & (x, UnboundErrorAttr _) ->
    match processUnboundErrorAttrType env st loc x with (st, addHere) in
    simpleSynthesizedType st
      pair
      openUnboundErrorAttr
      (mapEmpty nameCmp)
      (mapUnionWith concat)
      addHere

  sem processAttrPat env st loc +=
  | pair & (x, UnboundErrorAttr _) ->
    match processUnboundErrorAttrPat env st loc x with (st, addHere) in
    simpleSynthesizedPat st
      pair
      openUnboundErrorAttr
      (mapEmpty nameCmp)
      (mapUnionWith concat)
      addHere
end

lang TestLang = UnboundErrorAttr + MExprCmp
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
  let attrs = [InScopeAttr (filledThunk (_scopeEmpty ())), UnboundErrorAttr (mkThunk (lazyPure "UnboundErrorAttr#root"))] in
  let res = processAst attrs ast in
  match getAttrEnv (UnboundErrorAttr noThunk) res with UnboundErrorAttr thunk in
  mapBindings (thunk.read ()) in


-- === Actual tests ===

utest check (utuple_ [var_ "x", conapp_ "C" unit_]) with
  [ (nameNoSym "C", [LocExpr (conapp_ "C" unit_)])
  , (nameNoSym "x", [LocExpr (var_ "x")])
  ] using eq in
utest check (bind_ (ulet_ "x" unit_) (conapp_ "x" (var_ "x"))) with
  [ (nameNoSym "x", [LocExpr (conapp_ "x" (var_ "x"))])
  ] using eq in
utest check
  (bind_
    (let_ "x" (tytuple_ [ity (tyvar_ "t"), tycon_ "T", tyall_ "t" (jty (tyvar_ "t"))])
      unit_)
    unit_)
with
  [ (nameNoSym "T", [LocType (tycon_ "T")])
  , (nameNoSym "t", [LocType (ity (tyvar_ "t"))])
  ] using eq in
utest check (match_ unit_ (pvar_ "x") (itm (var_ "x")) (jtm (var_ "x"))) with
  [ (nameNoSym "x", [LocExpr (jtm (var_ "x"))])
  ] using eq in
utest check
  (match_ unit_
    (por_ (pvar_ "x") (pvar_ "y"))
    (utuple_ [itm (var_ "x"), itm (var_ "y")])
    (utuple_ [jtm (var_ "x"), jtm (var_ "y")]))
with
  [ (nameNoSym "x", [LocExpr (itm (var_ "x")), LocExpr (jtm (var_ "x"))])
  , (nameNoSym "y", [LocExpr (itm (var_ "y")), LocExpr (jtm (var_ "y"))])
  ] using eq in

()
