-- This file provides an extensible language fragment for computing
-- attributes associated with each node in an AST, lazily.
--
-- The main entry point for computing attributes is `processAst`,
-- which takes a list of attributes to compute, and an AST to compute
-- over. The given attributes are considered associated with the root
-- of the AST. Note that attributes are currently not attached to the
-- AST after computation, i.e., the only meaningful use is to do
-- analyses over the entire tree in the form of attributes on the root
-- node.
--
-- The interface centers around the `Attr` type, which is meant to be
-- extended with one new constructor per attribute. Each attribute
-- should contain exactly a `Thunk a`, where `a` is the type of the
-- attribute. Values of this type is used in one of two ways:
-- * As a sort of key for getting the attribute with the same
--   constructor from somewhere else, e.g., `getAttrExpr (ExampleAttr
--   noThunk) x.body`. These uses only look at the constructor, not
--   the carried data, thus `noThunk` can be used safely.
-- * As a carrier for the thunk representing the attribute. These must
--   contain a real thunk, either from `mkThunk` or `filledThunk`.
--
-- Writing an attribute entails:
-- 1. Adding a constructor to `syn Attr loc`.
-- 2. Implementing `newAttr` and `attrKindToString.
-- 3. Implementing `processAttr*` for the desired AST types. This can
--    use some helpers:
--    * `getAttrEnv` for getting other attributes of the current node,
--      and `getAttr*` for getting attributes of children.
--    * `willWrite` and `willRead` to record which thunks (attributes)
--      will be written to and read from.
--    * `simpleSynthesized*` and `simpleInherited*` for simple AST
--      cases, i.e., those that would be covered by `smap` in other
--      semantic functions.
--
-- See `CountAttribute` in this file for a very simple synthesized
-- attribute, or `DeclaredHere` and `InScopeAttr` in
-- `invariants/in-scope.mc` for a mildly more complicated interplay
-- between a synthesized and inherited attribute.

include "mexpr/ast.mc"
include "mexpr/pprint.mc"
include "lazy.mc"
include "thunk.mc"
include "map.mc"
include "basic-types.mc"
include "seq.mc"
include "error.mc"
include "mexpr/ast-builder.mc"
include "mexpr/type.mc"
include "mlang/lazy-ast.mc"
include "string.mc"
include "set.mc"

lang AttributeGrammar = Ast + DeclAst + PrettyPrint + MetaVarTypeAst + LazyAst
  -- Each `Attr` is expected to contain exactly a `Thunk` of whatever
  -- the carried value is
  syn Attr loc =

  syn Loc =
  | LocExpr Expr
  | LocType Type
  | LocDecl Decl
  | LocPat Pat

  sem loc2str : Loc -> String
  sem loc2str =
  | LocExpr x -> expr2str x
  | LocType x -> type2str x
  | LocDecl x -> decl2str x
  | LocPat x -> pat2str x

  type InvEnv loc = Map Int (Attr loc)

  type InvState =
    { willWrite : [ThunkMeta]
    }

  -- === external interface ===

  -- Setup lazy computations in the given attributes to compute them
  -- as though they were attached to the root node of the given
  -- AST. Note that input attributes will be deduplicated, thus it's
  -- recommended to use `getAttrEnv` on the returned value rather than
  -- retain references to the original attributes, to make it easier
  -- to extensibly request which attributes should be computed.
  sem processAst : [Attr Loc] -> Expr -> InvEnv Loc
  sem processAst attrs = | tm ->
    let env = mapFromSeq subi (map (lam x. (constructorTag x, x)) attrs) in
    processExpr env tm;
    env

  -- === interface for implementing an attribute ===

  sem getAttrEnv : all loc. Attr loc -> InvEnv loc -> Attr loc
  sem getAttrEnv attr = | env ->
    -- TODO(vipa, 2026-03-02): Make a somewhat more informative error
    -- if this fails. That should only happen if the attribute wasn't
    -- propagated from above previously, which is a programmer error,
    -- but a relatively easy one to make.
    match mapLookup (constructorTag attr) env with Some attr in
    attr

  sem getAttrExpr : all loc. Attr loc -> Expr -> Attr loc
  sem getAttrExpr attr = | tm ->
    match tm with TmWithEnv x in
    let tag = constructorTag attr in
    -- NOTE(vipa, 2026-03-02): The type-variable `loc` will always be
    -- instantiated as `Loc`, it's quantified to ensure that no `Attr`
    -- may look at it directly, thus this `unsafeCoerce` is safe.
    let unwrapEnv : Ref (InvEnv Loc) -> Ref (InvEnv loc) = unsafeCoerce in
    let env = unwrapEnv x.env in
    match mapLookup tag (deref env) with Some found then found else
    let new = newAttr (lazy (lam. join [attrKindToString attr, "#", lazyForce x.label])) attr in
    (if neqi tag (constructorTag new) then
      error "Compiler error: newAttr returned different constructorTag"
     else ());
    modref env (mapInsert tag new (deref env));
    new

  sem getAttrType : all loc. Attr loc -> Type -> Attr loc
  sem getAttrType attr = | tm ->
    match tm with TyWithEnv x in
    let tag = constructorTag attr in
    -- NOTE(vipa, 2026-03-02): The type-variable `loc` will always be
    -- instantiated as `Loc`, it's quantified to ensure that no `Attr`
    -- may look at it directly, thus this `unsafeCoerce` is safe.
    let unwrapEnv : Ref (InvEnv Loc) -> Ref (InvEnv loc) = unsafeCoerce in
    let env = unwrapEnv x.env in
    match mapLookup tag (deref env) with Some attr then attr else
    let attr = newAttr (lazy (lam. join [attrKindToString attr, "#", lazyForce x.label])) attr in
    (if neqi tag (constructorTag attr) then
      error "Compiler error: newAttr returned different constructorTag"
     else ());
    modref env (mapInsert tag attr (deref env));
    attr

  sem getAttrDecl : all loc. Attr loc -> Decl -> Attr loc
  sem getAttrDecl attr = | tm ->
    match tm with DeclWithEnv x in
    let tag = constructorTag attr in
    -- NOTE(vipa, 2026-03-02): The type-variable `loc` will always be
    -- instantiated as `Loc`, it's quantified to ensure that no `Attr`
    -- may look at it directly, thus this `unsafeCoerce` is safe.
    let unwrapEnv : Ref (InvEnv Loc) -> Ref (InvEnv loc) = unsafeCoerce in
    let env = unwrapEnv x.env in
    match mapLookup tag (deref env) with Some attr then attr else
    let attr = newAttr (lazy (lam. join [attrKindToString attr, "#", lazyForce x.label])) attr in
    (if neqi tag (constructorTag attr) then
      error "Compiler error: newAttr returned different constructorTag"
     else ());
    modref env (mapInsert tag attr (deref env));
    attr

  sem getAttrPat : all loc. Attr loc -> Pat -> Attr loc
  sem getAttrPat attr = | tm ->
    match tm with PatWithEnv x in
    let tag = constructorTag attr in
    -- NOTE(vipa, 2026-03-02): The type-variable `loc` will always be
    -- instantiated as `Loc`, it's quantified to ensure that no `Attr`
    -- may look at it directly, thus this `unsafeCoerce` is safe.
    let unwrapEnv : Ref (InvEnv Loc) -> Ref (InvEnv loc) = unsafeCoerce in
    let env = unwrapEnv x.env in
    match mapLookup tag (deref env) with Some attr then attr else
    let attr = newAttr (lazy (lam. join [attrKindToString attr, "#", lazyForce x.label])) attr in
    (if neqi tag (constructorTag attr) then
      error "Compiler error: newAttr returned different constructorTag"
     else ());
    modref env (mapInsert tag attr (deref env));
    attr

  sem willWrite : all a. InvState -> Thunk a -> (InvState, a -> ())
  sem willWrite st = | thunk ->
    ( { st with willWrite = snoc st.willWrite {lazy = thunk.lazy, blackhole = thunk.blackhole} }
    , thunk.write
    )

  sem willRead : all a. InvState -> Thunk a -> (InvState, () -> a)
  sem willRead st = | thunk ->
    (st, thunk.read)

  -- === semantic functions to be implemented by each attribute ===

  sem newAttr : all loc. Lazy String -> Attr loc -> Attr loc
  sem attrKindToString : all loc. Attr loc -> String

  -- Each `processAttr*` is given:
  -- * An `env` containing the attributes to be computed for this
  --   node. `getAttrEnv` can be used to access other attributes here.
  -- * A `st`, which is used to record which attributes are
  --   read/written by this invocation.
  -- * An opaque `loc`, which can be stored in an attribute to record
  --   where in the AST the attribute was computed.
  -- * A pair of the current node and the attribute to be computed,
  --   used for dispatch.
  --
  -- `processAttr*` should then returned an updated `st` and the
  -- function that actually computes the attribute by reading/writing
  -- from/to the previously recorded attributes.
  sem processAttrExpr : all loc. InvEnv loc -> InvState -> loc -> (Expr, Attr loc) -> (InvState, () -> ())
  sem processAttrExpr env st loc =
  | (tm, attr) -> errorSingle [infoTm tm]
    (join ["Missing case in processAttrExpr for ", attrKindToString attr, " for: ", expr2str tm])
  sem processAttrDecl : all loc. InvEnv loc -> InvState -> loc -> (Decl, Attr loc) -> (InvState, () -> ())
  sem processAttrDecl env st loc =
  | (decl, attr) -> errorSingle [infoDecl decl]
    (join ["Missing case in processAttrDecl for ", attrKindToString attr, " for: ", decl2str decl])
  sem processAttrType : all loc. InvEnv loc -> InvState -> loc -> (Type, Attr loc) -> (InvState, () -> ())
  sem processAttrType env st loc =
  | (ty, attr) -> errorSingle [infoTy ty]
    (join ["Missing case in processAttrType for ", attrKindToString attr, " for: ", type2str ty])
  sem processAttrPat : all loc. InvEnv loc -> InvState -> loc -> (Pat, Attr loc) -> (InvState, () -> ())
  sem processAttrPat env st loc =
  | (pat, attr) -> errorSingle [infoPat pat]
    (join ["Missing case in processAttrPat for ", attrKindToString attr, " for: ", pat2str pat])

  -- === alternate interfaces === ---

  type SimpleSynthesizedF ast attr
    = all loc. InvState -- The current InvState value
    -> (ast, Attr loc) -- The current node and attribute to write
    -> (Attr loc -> Thunk attr) -- An accessor for the current attribute, can assume it's the correct type
    -> attr -- An empty attribute, should be an identity element for the next operation
    -> (attr -> attr -> attr) -- A merging operation, should *probably* be commutative, or at least that it doesn't matter if the argument order differs
    -> (attr -> attr) -- Add data from the current node, *after* reading from children
    -> (InvState, () -> ())

  type SimpleInheritedF ast attr
    = all loc. InvState -- The current InvState value
    -> (ast, Attr loc) -- The current node and attribute to read from
    -> (Attr loc -> Thunk attr) -- An accessor for the current attribute, can assume it's the correct type
    -> (attr -> attr) -- Add data from the current node, *before* pushing to children
    -> (InvState, () -> ())

  sem simpleSynthesizedExpr : all attr. SimpleSynthesizedF Expr attr
  sem simpleSynthesizedExpr st here openAttr zero plus = | addHere ->
    match here with (tm, attr) in
    match willWrite st (openAttr attr) with (st, writeHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, gets) in
      match willRead st (openAttr (getAttr x)) with (st, get) in
      (st, snoc gets get) in
    let acc = (st, []) in
    let acc = match tm with TmDecl x
      then f (getAttrDecl attr) acc x.decl
      else acc in
    -- NOTE: `TmLazy` (see `mlang/lazy-ast.mc`) has no usable
    -- `smapAccumL_Expr_Expr`, by design: descending into it would
    -- force (and thus materialize) its thunk. Treat it as having no
    -- Expr children instead of crashing; `addHere` below still runs
    -- against the `TmLazy` node itself, so attributes that only need
    -- e.g. its `info` field are unaffected.
    let acc = match tm with TmLazy _ then acc
      else sfold_Expr_Expr (f (getAttrExpr attr)) acc tm in
    let acc = sfold_Expr_Type (f (getAttrType attr)) acc tm in
    let acc = sfold_Expr_Pat (f (getAttrPat attr)) acc tm in
    match acc with (st, gets) in
    ( st
    , lam.
      let below = foldl (lam attr. lam f. plus attr (f ())) zero gets in
      writeHere (addHere below)
    )

  sem simpleSynthesizedDecl : all attr. SimpleSynthesizedF Decl attr
  sem simpleSynthesizedDecl st here openAttr zero plus = | addHere ->
    match here with (decl, attr) in
    match willWrite st (openAttr attr) with (st, writeHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, gets) in
      match willRead st (openAttr (getAttr x)) with (st, get) in
      (st, snoc gets get) in
    let acc = (st, []) in
    let acc = sfold_Decl_Expr (f (getAttrExpr attr)) acc decl in
    let acc = sfold_Decl_Type (f (getAttrType attr)) acc decl in
    match acc with (st, gets) in
    ( st
    , lam.
      writeHere (addHere (foldl (lam attr. lam f. plus attr (f ())) zero gets))
    )

  sem simpleSynthesizedType : all attr. SimpleSynthesizedF Type attr
  sem simpleSynthesizedType st here openAttr zero plus = | addHere ->
    match here with (ty, attr) in
    match willWrite st (openAttr attr) with (st, writeHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, gets) in
      match willRead st (openAttr (getAttr x)) with (st, get) in
      (st, snoc gets get) in
    let acc = (st, []) in
    let acc = sfold_Type_Type (f (getAttrType attr)) acc ty in
    match acc with (st, gets) in
    ( st
    , lam.
      writeHere (addHere (foldl (lam attr. lam f. plus attr (f ())) zero gets))
    )

  sem simpleSynthesizedPat : all attr. SimpleSynthesizedF Pat attr
  sem simpleSynthesizedPat st here openAttr zero plus = | addHere ->
    match here with (pat, attr) in
    match willWrite st (openAttr attr) with (st, writeHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, gets) in
      match willRead st (openAttr (getAttr x)) with (st, get) in
      (st, snoc gets get) in
    let acc = (st, []) in
    let acc = sfold_Pat_Pat (f (getAttrPat attr)) acc pat in
    match acc with (st, gets) in
    ( st
    , lam.
      writeHere (addHere (foldl (lam attr. lam f. plus attr (f ())) zero gets))
    )

  sem simpleInheritedExpr : all attr. SimpleInheritedF Expr attr
  sem simpleInheritedExpr st here openAttr = | addHere ->
    match here with (tm, attr) in
    match willRead st (openAttr attr) with (st, readHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, writes) in
      match willWrite st (openAttr (getAttr x)) with (st, write) in
      (st, snoc writes write) in
    let acc = (st, []) in
    let acc = match tm with TmDecl x
      then f (getAttrDecl attr) acc x.decl
      else acc in
    -- NOTE: see the matching comment in `simpleSynthesizedExpr` above
    -- for why `TmLazy` is skipped here rather than folded over.
    let acc = match tm with TmLazy _ then acc
      else sfold_Expr_Expr (f (getAttrExpr attr)) acc tm in
    let acc = sfold_Expr_Type (f (getAttrType attr)) acc tm in
    let acc = sfold_Expr_Pat (f (getAttrPat attr)) acc tm in
    match acc with (st, writes) in
    ( st
    , lam.
      let data = addHere (readHere ()) in
      for_ writes (lam w. w data)
    )

  sem simpleInheritedDecl : all attr. SimpleInheritedF Decl attr
  sem simpleInheritedDecl st here openAttr = | addHere ->
    match here with (decl, attr) in
    match willRead st (openAttr attr) with (st, readHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, writes) in
      match willWrite st (openAttr (getAttr x)) with (st, write) in
      (st, snoc writes write) in
    let acc = (st, []) in
    let acc = sfold_Decl_Expr (f (getAttrExpr attr)) acc decl in
    let acc = sfold_Decl_Type (f (getAttrType attr)) acc decl in
    match acc with (st, writes) in
    ( st
    , lam.
      let data = addHere (readHere ()) in
      for_ writes (lam w. w data)
    )

  sem simpleInheritedType : all attr. SimpleInheritedF Type attr
  sem simpleInheritedType st here openAttr = | addHere ->
    match here with (ty, attr) in
    match willRead st (openAttr attr) with (st, readHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, writes) in
      match willWrite st (openAttr (getAttr x)) with (st, write) in
      (st, snoc writes write) in
    let acc = (st, []) in
    let acc = sfold_Type_Type (f (getAttrType attr)) acc ty in
    match acc with (st, writes) in
    ( st
    , lam.
      let data = addHere (readHere ()) in
      for_ writes (lam w. w data)
    )

  sem simpleInheritedPat : all attr. SimpleInheritedF Pat attr
  sem simpleInheritedPat st here openAttr = | addHere ->
    match here with (pat, attr) in
    match willRead st (openAttr attr) with (st, readHere) in
    let f = lam getAttr. lam acc. lam x.
      match acc with (st, writes) in
      match willWrite st (openAttr (getAttr x)) with (st, write) in
      (st, snoc writes write) in
    let acc = (st, []) in
    let acc = sfold_Pat_Pat (f (getAttrPat attr)) acc pat in
    match acc with (st, writes) in
    ( st
    , lam.
      let data = addHere (readHere ()) in
      for_ writes (lam w. w data)
    )

  -- === Internals ===

  syn Expr += | TmWithEnv {env : Ref (InvEnv Loc), label : Lazy String}
  syn Decl += | DeclWithEnv {env : Ref (InvEnv Loc), label : Lazy String}
  syn Type += | TyWithEnv {env : Ref (InvEnv Loc), label : Lazy String}
  syn Pat += | PatWithEnv {env : Ref (InvEnv Loc), label : Lazy String}

  sem pprintCode indent env += | TmWithEnv x -> (env, join ["<omitted tm, ", lazyForce x.label, ">"])
  sem getTypeStringCode indent env += | TyWithEnv x -> (env, join ["<omitted ty, ", lazyForce x.label, ">"])
  sem getPatStringCode indent env += | PatWithEnv x -> (env, join ["<omitted pat, ", lazyForce x.label, ">"])
  sem pprintDeclCode indent env += | DeclWithEnv x -> (env, join ["<omitted decl, ", lazyForce x.label, ">"])

  -- NOTE: `pprintCode` has no default case, and `TmLazy` (see
  -- `mlang/lazy-ast.mc`) deliberately has no real one either, since
  -- printing its expanded contents would require forcing (and thus
  -- materializing) the thunk. This prints a placeholder from the
  -- metadata already sitting on the node instead.
  sem pprintCode indent env +=
  | TmLazy t ->
    (env, join
      [ "<lazy: ", int2string (setSize t.freeVars), " free var(s)"
      , (if t.sideEffect then ", side-effecting" else "")
      , ">"
      ])

  -- sem infoTm = | TmWithEnv _ -> NoInfo ()
  -- sem infoTy = | TyWithEnv _ -> NoInfo ()
  -- sem infoDecl = | DeclWithEnv _ -> NoInfo ()
  -- sem infoPat = | PatWithEnv _ -> NoInfo ()

  sem processExpr : InvEnv Loc -> Expr -> ()
  sem processExpr env = | tm ->
    let loc = LocExpr tm in
    -- NOTE(vipa, 2026-02-25): Prepare, insert environments in place
    -- of expressions, prepare closures for the recursive calls
    let toCall = [] in

    let prepareDecl = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processDecl (deref localEnv) x)
      , DeclWithEnv {label = lazy (lam. decl2str x), env = localEnv}
      ) in
    -- NOTE(vipa, 2026-03-02): This takes the place of an explicit
    -- smapAccumL_Expr_Decl. Note also that it swaps out the `Decl`
    -- for one that has no children, thus the default
    -- `smapAccumL_Expr_*` for `TmDecl` (which traverses through the
    -- corresponding `smapAccumL_Decl_*`) doesn't apply after this,
    -- i.e., it's important we deal with `Decl` *first*.
    match
      match tm with TmDecl x then
        match prepareDecl toCall x.decl with (toCall, decl) in
        (toCall, TmDecl {x with decl = decl})
      else (toCall, tm)
    with (toCall, tm) in

    let prepareExpr = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processExpr (deref localEnv) x)
      , TmWithEnv {label = lazy (lam. expr2str x), env = localEnv}
      ) in
    match
      match tm with TmOpaque x then
        match prepareExpr toCall x.body with (toCall, body) in
        (toCall, TmOpaque {x with body = body})
      -- NOTE: `TmLazy` (see `mlang/lazy-ast.mc`) must not be forced
      -- here: leave it untouched and schedule no recursive call for
      -- its thunk. `processAttrExpr` still runs against the raw
      -- `TmLazy` node below, so per-node checks (e.g. its `info`
      -- field) still apply; `simpleSynthesizedExpr` /
      -- `simpleInheritedExpr` know to skip folding over its
      -- (unreachable) children.
      else match tm with TmLazy _ then (toCall, tm)
      else smapAccumL_Expr_Expr prepareExpr toCall tm
    with (toCall, tm) in

    let prepareType = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processType (deref localEnv) x)
      , TyWithEnv {label = lazy (lam. type2str x), env = localEnv}
      ) in
    match smapAccumL_Expr_Type prepareType toCall tm with (toCall, tm) in

    let preparePat = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processPat (deref localEnv) x)
      , PatWithEnv {label = lazy (lam. pat2str x), env = localEnv}
      ) in
    match smapAccumL_Expr_Pat preparePat toCall tm with (toCall, tm) in

    -- NOTE(vipa, 2026-02-25): Do processing of attributes here
    let st = {willWrite = []} in
    let fsPerAttr = mapMap (lam attr. processAttrExpr env st loc (tm, attr)) env in

    -- NOTE(vipa, 2026-02-25): Record connections between thunks and
    -- their update functions
    let f = lam pair.
      match pair with (st, f) in
      let f = lam.
        for_ st.willWrite (lam ww. ww.blackhole ());
        f () in
      for_ st.willWrite (lam ww. ww.lazy f) in
    mapMap f fsPerAttr;

    -- NOTE(vipa, 2026-02-25): Do recursive calls
    for_ toCall (lam f. f ())

  sem processDecl : InvEnv Loc -> Decl -> ()
  sem processDecl env = | decl ->
    let loc = LocDecl decl in
    -- NOTE(vipa, 2026-02-25): Prepare, insert environments in place
    -- of expressions, prepare closures for the recursive calls
    let toCall = [] in

    let prepareExpr = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processExpr (deref localEnv) x)
      , TmWithEnv {label = lazy (lam. expr2str x), env = localEnv}
      ) in
    match smapAccumL_Decl_Expr prepareExpr toCall decl with (toCall, decl) in

    let prepareType = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processType (deref localEnv) x)
      , TyWithEnv {label = lazy (lam. type2str x), env = localEnv}
      ) in
    match smapAccumL_Decl_Type prepareType toCall decl with (toCall, decl) in

    -- NOTE(vipa, 2026-02-25): Do processing of attributes here
    let st = {willWrite = []} in
    let fsPerAttr = mapMap (lam attr. processAttrDecl env st loc (decl, attr)) env in

    -- NOTE(vipa, 2026-02-25): Record connections between thunks and
    -- their update functions
    let f = lam pair.
      match pair with (st, f) in
      let f = lam.
        for_ st.willWrite (lam ww. ww.blackhole ());
        f () in
      for_ st.willWrite (lam ww. ww.lazy f) in
    mapMap f fsPerAttr;

    -- NOTE(vipa, 2026-02-25): Do recursive calls
    for_ toCall (lam f. f ())

  sem processType : InvEnv Loc -> Type -> ()
  sem processType env =
  | TyMetaVar x ->
    switch deref x.contents
    case Link ty then processType env ty
    case Unbound u then
      -- NOTE(vipa, 2026-08-19): Disconnect the TyMetaVar from others,
      -- which means that `smapAccumL_Type_Type` won't mutate what's
      -- visible elsewhere.
      let ty = TyMetaVar {x with contents = ref (Unbound u)} in
      let loc = LocType ty in
      -- NOTE(vipa, 2026-02-25): Prepare, insert environments in place
      -- of expressions, prepare closures for the recursive calls
      let toCall = [] in

      let prepareType = lam toCall. lam x.
        let localEnv = ref (mapEmpty subi) in
        ( snoc toCall (lam. processType (deref localEnv) x)
        , TyWithEnv {label = lazy (lam. type2str x), env = localEnv}
        ) in
      match smapAccumL_Type_Type prepareType toCall ty with (toCall, ty) in

      -- NOTE(vipa, 2026-02-25): Do processing of attributes here
      let st = {willWrite = []} in
      let fsPerAttr = mapMap (lam attr. processAttrType env st loc (ty, attr)) env in

      -- NOTE(vipa, 2026-02-25): Record connections between thunks and
      -- their update functions
      let f = lam pair.
        match pair with (st, f) in
        let f = lam.
          for_ st.willWrite (lam ww. ww.blackhole ());
          f () in
        for_ st.willWrite (lam ww. ww.lazy f) in
      mapMap f fsPerAttr;

      -- NOTE(vipa, 2026-02-25): Do recursive calls
      for_ toCall (lam f. f ())
    end
  | ty ->
    let loc = LocType ty in
    -- NOTE(vipa, 2026-02-25): Prepare, insert environments in place
    -- of expressions, prepare closures for the recursive calls
    let toCall = [] in

    let prepareType = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processType (deref localEnv) x)
      , TyWithEnv {label = lazy (lam. type2str x), env = localEnv}
      ) in
    match smapAccumL_Type_Type prepareType toCall ty with (toCall, ty) in

    -- NOTE(vipa, 2026-02-25): Do processing of attributes here
    let st = {willWrite = []} in
    let fsPerAttr = mapMap (lam attr. processAttrType env st loc (ty, attr)) env in

    -- NOTE(vipa, 2026-02-25): Record connections between thunks and
    -- their update functions
    let f = lam pair.
      match pair with (st, f) in
      let f = lam.
        for_ st.willWrite (lam ww. ww.blackhole ());
        f () in
      for_ st.willWrite (lam ww. ww.lazy f) in
    mapMap f fsPerAttr;

    -- NOTE(vipa, 2026-02-25): Do recursive calls
    for_ toCall (lam f. f ())

  sem processPat : InvEnv Loc -> Pat -> ()
  sem processPat env = | pat ->
    let loc = LocPat pat in
    -- NOTE(vipa, 2026-02-25): Prepare, insert environments in place
    -- of expressions, prepare closures for the recursive calls
    let toCall = [] in

    let preparePat = lam toCall. lam x.
      let localEnv = ref (mapEmpty subi) in
      ( snoc toCall (lam. processPat (deref localEnv) x)
      , PatWithEnv {label = lazy (lam. pat2str x), env = localEnv}
      ) in
    match smapAccumL_Pat_Pat preparePat toCall pat with (toCall, pat) in

    -- NOTE(vipa, 2026-02-25): Do processing of attributes here
    let st = {willWrite = []} in
    let fsPerAttr = mapMap (lam attr. processAttrPat env st loc (pat, attr)) env in

    -- NOTE(vipa, 2026-02-25): Record connections between thunks and
    -- their update functions
    let f = lam pair.
      match pair with (st, f) in
      let f = lam.
        for_ st.willWrite (lam ww. ww.blackhole ());
        f () in
      for_ st.willWrite (lam ww. ww.lazy f) in
    mapMap f fsPerAttr;

    -- NOTE(vipa, 2026-02-25): Do recursive calls
    for_ toCall (lam f. f ())
end

lang CountAttr = AttributeGrammar + MExprAst
  type CountAttr loc =
    { tm : Int
    , decl : Int
    , ty : Int
    , pat : Int
    }

  syn Attr loc +=
  | CountAttr (Thunk (CountAttr loc))

  sem newAttr label +=
  | CountAttr _ -> CountAttr (mkThunk label)

  sem attrKindToString +=
  | CountAttr _ -> "CountAttr"

  sem openCountAttr : all loc. Attr loc -> Thunk (CountAttr loc)
  sem openCountAttr =
  | CountAttr x -> x

  sem mergeCount : all loc. CountAttr loc -> CountAttr loc -> CountAttr loc
  sem mergeCount a = | b ->
    { tm = addi a.tm b.tm
    , decl = addi a.decl b.decl
    , ty = addi a.ty b.ty
    , pat = addi a.pat b.pat
    }

  sem processAttrDecl env st loc +=
  | pair & (_, CountAttr _) ->
    simpleSynthesizedDecl st
      pair
      openCountAttr
      {tm = 0, decl = 0, ty = 0, pat = 0}
      mergeCount
      (lam x. {x with decl = addi x.decl 1})

  sem processAttrExpr env st loc +=
  | pair & (_, CountAttr _) ->
    simpleSynthesizedExpr st
      pair
      openCountAttr
      {tm = 0, decl = 0, ty = 0, pat = 0}
      mergeCount
      (lam x. {x with tm = addi x.tm 1})

  sem processAttrType env st loc +=
  | pair & (_, CountAttr _) ->
    simpleSynthesizedType st
      pair
      openCountAttr
      {tm = 0, decl = 0, ty = 0, pat = 0}
      mergeCount
      (lam x. {x with ty = addi x.ty 1})

  sem processAttrPat env st loc +=
  | pair & (_, CountAttr _) ->
    simpleSynthesizedPat st
      pair
      openCountAttr
      {tm = 0, decl = 0, ty = 0, pat = 0}
      mergeCount
      (lam x. {x with pat = addi x.pat 1})
end

mexpr

use CountAttr in

let count = lam ast.
  match getAttrEnv (CountAttr noThunk) (processAst [CountAttr (mkThunk (lazyPure "CountAttr#root"))] ast)
    with CountAttr thunk in
  thunk.read () in

utest count unit_ with {decl = 0, pat = 0, ty = 0, tm = 1} in
utest count (ulam_ "a" (var_ "a")) with {decl = 0, pat = 0, ty = 1, tm = 2} in
utest count (match_ (int_ 1) (pint_ 2) true_ false_) with {decl = 0, pat = 1, ty = 0, tm = 4} in
utest count (bind_ (ulet_ "x" (int_ 1)) (var_ "x")) with {decl = 1, pat = 0, ty = 1, tm = 3} in

()
