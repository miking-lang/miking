include "mexpr/pprint.mc"
/-

NOTE(vipa, 2022-05-20): This file decomposes nested patterns into a
series of nested matches, where each match uses a shallow pattern.

The central observation we use is that a nested pattern is a couple of
simpler patterns "and"ed together. For example:

`[1, x]` = `[_, _] & [1, _] & [_, x]`

One pattern for the top-level structure, followed by one pattern for
each direct child.

The idea is to insert a match for `[x1, x2]` (with fresh names `x1`
and `x2`), then recursively examine `x1` and `x2` with their
corresponding patterns. This means that when we've matched on the
top-level structure of a `Pat` we're left with a `Map Name Pat` of
further things to match on.

In the example above, `[1, x]`, we must also record that we can find
the value that `x` should refer to in `x2`, which we do in the form of
a `Map Name Name`. To put things in this `Map` we need the `Name`
we're currently matching against.

Thus far we seem to need a function of type `Name -> SPat -> Pat ->
(Map Name Pat, Map Name Name)` (where `SPat` represents a shallow
pattern). However, the `SPat` might not be compatible with the current
pattern, e.g., if `[_, _]` matches then `[1]` can never
match. Furthermore, to filter out irrelevant patterns in the else
branch we also need to know if the nested pattern is still relevent
when the shallow pattern fails. This suggests `Name -> SPat -> Pat ->
(Option (Map Name Pat, Map Name Name), Bool)`.

The final complication comes from our boolean patterns: we might have
updated information if the pattern fails, and the pattern can succeed
in multiple ways, whereby we land on this type signature:

```
sem decompose
  : Name
  -> (SPat, Pat)  -- We pair these to match on both in the `sem`
  -> ([(Map Name Pat, Map Name Name)], Option Pat)
```

Laws:
1. !!p = p
2. !(p & p') = !p | !p'
3. !(p | p') = !p & !p'
4. a & (b | c) = (a & b) | (a & c)
5. Forall shallow patterns s, s',
   we have s & s' = empty
   \/ s \subseteq s'
   \/ s' \subseteq s
6. If `p` isn't a regular pattern or a wildcard
   (i.e., `!`, `|`, `&`, or `_`), then
   `collectShallows p` is a singleton set.
7. If `decompose _ (s, p) = (_, p')`, then
   `!s & p' = !s & p`. Furthermore, if
   `!s & p = !_`, then `p' = !_`.
8. If `decompose x (s, p) = (p', _)` and `s` is not `_`,
   then `x` must not appear anywhere in `p'`.

1-4 follow from the semantics of pattern matching.
5-6 defines shallow patterns and must be upheld by an implementation.
7 forms the contract for pattern failure, to ensure that patterns
  never grow.

In particular, law 6 is a weakening of `p' = !s & p`, using the fact
that no efficient pattern compilation will check the same shallow
pattern twice (since it would be redundant), thus we don't need to
update `p'` such that it no longer matches `s`. The final clause means
that the implementation must identify the cases where the pattern is
dead.

-/

include "ast.mc"
include "ast-builder.mc"
include "common.mc"
include "seq.mc"
include "set.mc"

let _empty : all v. Map Name v = mapEmpty nameCmp
let _singleton : all v. Name -> v -> Map Name v = lam n. lam p. mapInsert n p _empty

lang ShallowBase = Ast + NamedPat
  syn SPat =
  | SPatWild ()

  -- Names that still need to be examined. A `Map Name Pat`
  -- essentially represents a match on each `Name` with the
  -- corresponding `Pat`. The `Map Name Name` is a mapping from
  -- pattern names to names introduced by previous patterns.
  type BranchInfo = (Map Name Pat, Map Name Name)

  type LiveBranch res =
    -- The possible ways to continue matching to reach this branch.
    -- Essentially, this is one big "or"; the pattern is in something
    -- like disjunctive normal form.
    { alts : [BranchInfo]
    -- Given a mapping from names in the pattern to the name of the
    -- matched value, construct an expression that executes the
    -- branch, currently through a function call to an earlier
    -- `let`-expression.
    , branchFunc : Map Name Name -> res
    }
  -- A pair of new names to examine, along with the names that were
  -- bound.
  type PatUpdate = [BranchInfo]

  -- # Interface to implement

  sem decompose : Name -> (SPat, Pat) -> (PatUpdate, Option Pat)
  sem decompose name =
  | (_, PatNamed {ident = PName patName}) ->
    ([(_empty, _singleton patName name)], None ())
  | (_, PatNamed {ident = PWildcard _}) ->
    ([(_empty, _empty)], None ())
  | (shallow, pat) ->
    match shallow with SPatWild _
    then ([(_singleton name pat, _empty)], None ())
    else defaultDecomposition pat

  sem shallowMinusIsEmpty : (SPat, SPat) -> Bool
  sem shallowMinusIsEmpty =
  | x -> if shallowIsInfallible x.1 then true else eqi 0 (shallowCmp x)

  sem shallowIsInfallible : SPat -> Bool
  sem shallowIsInfallible =
  | SPatWild _ -> true
  | _ -> false

  sem collectShallows : Pat -> Set SPat
  sem collectShallows =
  -- | PatNamed _ -> _ssingleton (SPatWild ())
  | shallow -> sfold_Pat_Pat (lam acc. lam p. setUnion acc (collectShallows p)) (_sempty ()) shallow

  sem spatToPat : SPat -> Pat
  sem spatToPat =
  | SPatWild _ -> pvarw_

  -- The singular SPat is just there to choose the implementation,
  -- its contents should be ignored; it's also present in the set.
  sem processSPats : Set SPat -> SPat -> [SPat]
  sem processSPats spats = | _ -> setToSeq spats

  sem shallowCmp : (SPat, SPat) -> Int
  sem shallowCmp =
  | (l, r) -> subi (constructorTag l) (constructorTag r)

  -- # Helpers

  sem defaultDecomposition : Pat -> (PatUpdate, Option Pat)
  sem defaultDecomposition =
  | pat -> ([], Some pat)

  sem _ssingleton : SPat -> Set SPat
  sem _ssingleton =
  | p -> setInsert p (_sempty ())

  sem _sempty : () -> Set SPat
  sem _sempty = | _ -> setEmpty (lam l. lam r. shallowCmp (l, r))

  sem _processSPats : Set SPat -> [SPat]
  sem _processSPats = | spats -> processSPats spats (setChooseExn spats)

  -- Discharge patterns that do not care about the shallow pattern, e.g.,
  -- named patterns, wildcards, and `&` and `|` patterns.
  sem decomposeNorm : Name -> (SPat, Pat) -> (PatUpdate, Option Pat)
  sem decomposeNorm name = | x ->
    match decompose name x with (update, neg) in
    let andBranchInfo : BranchInfo -> BranchInfo -> BranchInfo = lam l. lam r.
      (mapUnionWith pand_ l.0 r.0, mapUnion l.1 r.1) in
    let normalize : BranchInfo -> PatUpdate = lam binfo.
      match binfo with (decomposed, names) in
      let decomposed : [(Name, Pat)] =
        mapBindings decomposed in
      let decomposed : [[BranchInfo]] =
        -- NOTE(vipa, 2022-05-23): SPatWild () is infallible, thus we
        -- can safely discard the pattern for the `else` branch
        seqMapM (lam dec. (decompose dec.0 (SPatWild (), dec.1)).0) decomposed in
      -- NOTE(vipa, 2022-05-23): Each inner list now contains the
      -- things that should be `and`ed together, thanks to mapM
      map (foldl andBranchInfo (_empty, _empty)) decomposed
    in
    (join (map normalize update), neg)

  -- Find the shallow patterns that can make progress, grouped by
  -- the `Name` they examine.
  sem collectAllShallows : all res. [LiveBranch res] -> Map Name (Set SPat)
  sem collectAllShallows =
  | branches ->
    let for = lam xs. lam f. map f xs in
    let flatFor = lam xs. lam f. join (map f xs) in
    let mergeMaps = foldl (mapUnionWith setUnion) _empty in
    mergeMaps
      (flatFor branches
        (lam branch.
          (for branch.alts
            (lam info. mapMap collectShallows info.0))))

  sem updateBranch
    : all res. Name
    -> SPat
    -> LiveBranch res
    -> (Option (LiveBranch res), Option (LiveBranch res))
  sem updateBranch scrutinee spat = | branch ->
    let work : ([BranchInfo], [BranchInfo]) -> BranchInfo -> ([BranchInfo], [BranchInfo])
      = lam acc. lam info.
        match acc with (passes, fails) in
        match info with (pats, names) in
        match mapLookup scrutinee pats with Some pat then
          let pats = mapRemove scrutinee pats in
          match decomposeNorm scrutinee (spat, pat) with (passUpdate, failPat) in
          let newPasses = map
            (lam update. (mapUnionWith pand_ pats update.0, mapUnion names update.1))
            passUpdate in
          let newFails = match failPat with Some p
            then [(mapInsert scrutinee p pats, names)]
            else [] in
          (concat passes newPasses, concat fails newFails)
        else (snoc passes info, snoc fails info)
    in
    match foldl work ([], []) branch.alts with (passes, fails) in
    ( if null passes then None () else Some {branch with alts = passes}
    , if null fails then None () else Some {branch with alts = fails}
    )

  sem lower
    : all res. Name
    -> [(Pat, Map Name Name -> res)]
    -> res
    -> (Name -> SPat -> res -> res -> res)
    -> res
  sem lower scrutinee branches default = | mkMatch ->
    let mkBranch = lam pair. match pair with (pat, branchFunc) in
      { branchFunc = branchFunc, alts = (decompose scrutinee (SPatWild (), pat)).0 } in
    let branches = filter (lam b. not (null b.alts)) (map mkBranch branches) in

    recursive let work : Name -> [SPat] -> [LiveBranch res] -> res
      = lam scrutinee. lam spats. lam branches.
        switch branches
        case [] then default
        case [h] ++ _ then
          match find (lam alt. mapIsEmpty alt.0) h.alts
            -- First branch is satisfied
            with Some (_, bindings) then h.branchFunc bindings
          else

          match spats with [spat] ++ spats then
            match unzip (map (updateBranch scrutinee spat) branches) with (passes, fails) in
            let passRes = work scrutinee [] (mapOption identity passes) in
            let failRes = work scrutinee spats (mapOption identity fails) in
            mkMatch scrutinee spat passRes failRes
          else

          -- NOTE(vipa, 2022-08-12): The current scrutinee has no more info,
          -- but we're not done, find a new scrutinee
          match mapChooseExn (collectAllShallows branches) with (scrutinee, spats) in
          work scrutinee (_processSPats spats) branches
        end
    in work (nameNoSym "") [] branches
end

lang ShallowAnd = ShallowBase + AndPat
  sem decompose name =
  | (shallow, PatAnd x) ->
    match decompose name (shallow, x.lpat) with (lPass, lFail) in
    match decompose name (shallow, x.rpat) with (rPass, rFail) in
    let mkAnd = lam l. lam r. PatAnd {{x with lpat = l} with rpat = r} in
    let mergeOnePass : BranchInfo -> BranchInfo -> BranchInfo
      = lam l. lam r. (mapUnionWith mkAnd l.0 r.0, mapUnion l.1 r.1) in
    (seqLiftA2 mergeOnePass lPass rPass, optionZipWith mkAnd lFail rFail)
end

lang ShallowOr = ShallowBase + OrPat
  sem decompose name =
  | (shallow, PatOr x) ->
    match decompose name (shallow, x.lpat) with (lPass, lFail) in
    match decompose name (shallow, x.rpat) with (rPass, rFail) in
    let patFail = switch (lFail, rFail)
      case (Some l, Some r) then Some (PatOr {{x with lpat = l} with rpat = r})
      case (l & Some _, None ()) then l
      case (None (), r & Some _) then r
      case (None (), None ()) then None ()
      end in
    (concat lPass rPass, patFail)
end

lang ShallowNot = ShallowBase + NotPat + OrPat + AndPat
  sem decompose name =
  | (shallow, PatNot {subpat = PatNot x}) ->
    decompose name (shallow, x.subpat)
  | (shallow, PatNot {subpat = PatOr x}) ->
    decompose name (shallow, pand_ (pnot_ x.lpat) (pnot_ x.rpat))
  | (shallow, PatNot {subpat = PatAnd x}) ->
    decompose name (shallow, por_ (pnot_ x.lpat) (pnot_ x.rpat))
  | (shallow, pat & PatNot x) ->
    -- NOTE(vipa, 2022-05-20): A normal nested pattern can be
    -- decomposed into a large and-pattern, e.g., `[1, a]` is the same
    -- as `[_, _] & [1, _] & [_, a]`.

    -- Note also that intersecting with `shallow` does one of two things:
    -- * Produces the empty pattern, e.g., `[] & [_, _] = !_`
    -- * Leaves each sub-pattern unchanged, e.g., `[_, _] & [1, _] = [1, _]`

    -- `decompose _ (s, p)` returns two "patterns":
    -- * `s & p` as a conjunction of the sub-patterns, e.g., `[1, _] &
    --   [_, a]`. Note that `s` has disappeared, as has `[_, _]`.
    -- * `!s & p` as an `Option Pat`, where `None` means the empty pattern.

    -- Following the same example (i.e., `![1, a]`), we want to compute two
    -- patterns:

    -- Positive "pattern":
    -- `shallow & ![1, a]`
    -- = `shallow & (![_, _] | [!1, _] | [_, !a])`
    -- = `(shallow & ![_, _]) | (shallow & [_, _] & ([!1, _] | [_, !a]))`
    -- If the first thing is non-empty and `shallow` isn't `_` we don't need
    -- to examine any further values, since neither `shallow` nor `![_, _]`
    -- have any sub-patterns.
    -- Otherwise we just need to return `[!1, _] | [_, !a]`.

    -- Negative pattern:
    -- Some `p'` such that `!shallow & p' = !shallow & ![1, a]`, and
    -- if `!shallow & ![1, a] = empty` then `p' = empty`.
    -- If `!shallow & [1, a]` is empty then `[1, a]` is a subset of `shallow`,
    -- whereby `!shallow` is a subset of `![1, a]`, thus their intersection is
    -- just `!shallow`. In this case the simplest pattern to return is `_`.
    -- Otherwise we merely return `![1, a]` unchanged, to ensure that the
    -- pattern doesn't grow, which could happen if we used the return from
    -- the recursive call to `decompose`.

    -- We can obtain the positive shallow pattern through `collectShallows`:
    let subShallow = setChoose (collectShallows x.subpat) in
    -- The nested ones come through `decompose`:
    match decompose name (shallow, x.subpat) with (subPass, subFail) in
    -- Discard bound names
    let subPass : [Map Name Pat] = map (lam x. x.0) subPass in
    -- We now have three pieces of information:
    -- `subShallow` is the positive shallow pattern, e.g., `[_, _]`
    -- `subPass` corresponds to the positive subpatterns, e.g.,
    --   `[1, _] | [_, a]`
    --   Note that `shallow` isn't present, since it by definition
    --   only has wildcards for sub-expressions.
    -- `subFail` is `None ()` iff `!shallow & [1, a]` is empty

    let negSubPatterns =
      match (shallow, optionMap (lam xshallow. shallowMinusIsEmpty (shallow, xshallow)) subShallow)
        with (!SPatWild _, Some false) then [(_empty, _empty)]
      else

      -- Helpers
      -- `&` two sets of matches on sub-expressions
      let andDecomposed : Map Name Pat -> Map Name Pat -> Map Name Pat = mapUnionWith pand_ in
      -- `!` a set of matches on sub-expressions. This turns `p1 & p2 & ...` to `!p1 | !p2 | ...`
      let notDecomposed : Map Name Pat -> [Map Name Pat] = lam dec.
        map (lam dec. _singleton dec.0 (pnot_ dec.1)) (mapBindings dec) in

      -- Note that `subPass` is a list (representing `|`s) of `Map`s (representing `&`s)
      -- We want to negate this and turn it into disjunctive normal form again.
      -- `map notDecomposed` gives a
      --   list (`&`) of lists (`|`) of `Map`s (`&`).
      -- `seqMapM` instead of `map` flips the order of the outer lists, i.e.,
      --   list (`|`) of lists (`&`) of `Map`s (`&`)
      let negSubPatterns : [[Map Name Pat]] = seqMapM notDecomposed subPass in
      -- Finally, and-ing the second level together (via `map`) gives us
      -- disjunctive normal form.
      map (lam pats. (foldl andDecomposed _empty pats, _empty)) negSubPatterns
    in

    let failPat =
      match shallow with SPatWild _ then None () else
      if optionIsSome subFail then Some pat else Some pvarw_ in

    (negSubPatterns, failPat)
end

lang ShallowInt = ShallowBase + IntPat
  syn SPat =
  | SPatInt Int

  sem decompose name =
  | (SPatInt i, pat & PatInt x) ->
    -- TODO(vipa, 2022-05-20): Ideally we'd have a guard instead here
    if eqi i x.val
    then ([(_empty, _empty)], None ())
    else defaultDecomposition pat

  sem collectShallows =
  | PatInt x -> _ssingleton (SPatInt x.val)

  sem spatToPat =
  | SPatInt i -> pint_ i

  sem shallowCmp =
  | (SPatInt l, SPatInt r) -> subi l r
end

lang ShallowChar = ShallowBase + CharPat
  syn SPat =
  | SPatChar Char

  sem decompose name =
  | (SPatChar i, pat & PatChar x) ->
    -- TODO(vipa, 2022-05-20): Ideally we'd have a guard instead here
    if eqc i x.val
    then ([(_empty, _empty)], None ())
    else defaultDecomposition pat

  sem collectShallows =
  | PatChar x -> _ssingleton (SPatChar x.val)

  sem spatToPat =
  | SPatChar c -> pchar_ c

  sem shallowCmp =
  | (SPatChar l, SPatChar r) -> cmpChar l r
end

lang ShallowBool = ShallowBase + BoolPat
  syn SPat =
  | SPatBool Bool

  sem decompose name =
  | (SPatBool i, pat & PatBool x) ->
    -- TODO(vipa, 2022-05-20): Ideally we'd have a guard instead here
    if not (xor i x.val)
    then ([(_empty, _empty)], None ())
    else defaultDecomposition pat

  sem collectShallows =
  | PatBool x -> _ssingleton (SPatBool x.val)

  sem spatToPat =
  | SPatBool v -> pbool_ v

  sem shallowCmp =
  | (SPatBool true, SPatBool true) -> 0
  | (SPatBool true, SPatBool false) -> negi 1
  | (SPatBool false, SPatBool true) -> 1
  | (SPatBool false, SPatBool false) -> 0
end

lang ShallowRecord = ShallowBase + RecordPat + RecordTypeAst
  syn SPat =
  | SPatRecord (Map SID Name)

  sem decompose name =
  | (SPatRecord bindings, PatRecord x) ->
    -- NOTE(vipa, 2022-05-20): This can only break if there's a
    -- missing name in SPatRecord, but we should have all the fields
    -- based on typechecking earlier
    let fields = map (lam pair. (mapFindExn pair.0 bindings, pair.1)) (mapBindings x.bindings)
    in ([(mapFromSeq nameCmp fields, _empty)], None ())

  sem collectShallows =
  | PatRecord x ->
    -- TODO(vipa, 2022-05-26): This needs to resolve links and aliases :(
    match x.ty with TyRecord x then
      _ssingleton (SPatRecord (mapMap (lam. nameSym "field") x.fields))
    else never

  sem spatToPat =
  | SPatRecord fields ->
    PatRecord
    { bindings = mapMap npvar_ fields
    , ty = TyRecord
      { fields = mapMap (lam. tyunknown_) fields
      , info = NoInfo ()
      }
    , info = NoInfo ()
    }

  sem shallowIsInfallible =
  | SPatRecord _ -> true
end

lang ShallowSeq = ShallowBase + SeqTotPat + SeqEdgePat
  syn SPat =
  | SPatSeqTot [Name]
  -- NOTE(vipa, 2022-05-26): We assume that the translation strategy
  -- we use only uses a GE pattern when it's long enough to
  -- accomodate all Edge patterns
  | SPatSeqGE {minLength : Int, prefix : Ref [Name], postfix : Ref [Name]}

  sem decompose name =
  | (SPatSeqTot elements, pat & PatSeqTot x) ->
    if neqi (length elements) (length x.pats) then defaultDecomposition pat else
    ([(mapFromSeq nameCmp (zip elements x.pats), _empty)], None ())
  | (SPatSeqTot elements, pat & PatSeqEdge x) ->
    if lti (length elements) (addi (length x.prefix) (length x.postfix))
    then defaultDecomposition pat
    else
      -- TODO(vipa, 2022-05-24): I need to make a name for the middle
      -- thing if it's present
      let pres = zip elements x.prefix in
      let posts = zip (reverse elements) (reverse x.postfix) in
      -- TODO(vipa, 2022-05-24): Is it enough to return pat or should I intersect with inverted shallow?
      ([(mapFromSeq nameCmp (concat pres posts), _empty)], Some pat)
  | (SPatSeqGE shallow, pat & PatSeqEdge x) ->
    let extendUsing
      : ([Name] -> [Name] -> [Name]) -> Ref [Name] -> Int -> ()
      = lam f. lam names. lam count.
        let nLen = length (deref names) in
        if lti nLen count then
          modref names (f (deref names) (create (subi count nLen) (lam. nameSym "elem")))
        else () in
    extendUsing concat shallow.prefix (length x.prefix);
    extendUsing (lam old. lam new. concat new old) shallow.postfix (length x.postfix);
    let pres = zip (deref shallow.prefix) x.prefix in
    let posts = zip (reverse (deref shallow.postfix)) (reverse x.postfix) in
    -- TODO(vipa, 2022-05-26): Need to bind the middle part to a name
    ([(mapFromSeq nameCmp (concat pres posts), _empty)], None ())

  sem shallowMinusIsEmpty =
  | (SPatSeqTot es, SPatSeqGE x) -> leqi x.minLength (length es)
  | (SPatSeqGE _, SPatSeqTot _) -> false
  | (SPatSeqGE x1, SPatSeqGE x2) -> geqi x1.minLength x2.minLength

  sem processSPats spats =
  -- TODO(vipa, 2022-08-12): Create a sequence of 'tot' patterns, possibly followed
  -- by a 'ge' pattern. There should be 'tot' patterns up to and including the
  -- longest 'tot' pattern in spats, or the longest 'ge' pattern minus one, whichever is
  -- longest. The 'ge' pattern should be present iff there is a 'ge' pattern in spats.
  -- There's likely space for optimization here, omitting some of the 'tot' patterns.
  | SPatSeqTot _ | SPatSeqGE _ -> never

  sem collectShallows =
  | PatSeqTot x -> _ssingleton (SPatSeqTot (map (lam. nameSym "elem") x.pats))
  | PatSeqEdge x -> _ssingleton (SPatSeqGE { minLength = addi (length x.prefix) (length x.postfix), prefix = ref [], postfix = ref [] })

  sem spatToPat =
  | SPatSeqTot x -> pseqtot_ (map npvar_ x)
  -- TODO(vipa, 2022-08-12): processSpats should ensure that a 'ge' pattern
  -- always happens in an infallible case, thus we don't need to check anything.
  -- However, we do need to bind the pre and post names, and possibly one or
  -- more middle segments
  | SPatSeqGE x -> never

  sem shallowIsInfallible =
  | SPatSeqGE x -> eqi x.minLength 0

  sem shallowCmp =
  | (SPatSeqTot l, SPatSeqTot r) -> subi (length l) (length r)
  | (SPatSeqGE l, SPatSeqGE r) -> subi l.minLength r.minLength
end

lang ShallowCon = ShallowBase + DataPat
  syn SPat =
  | SPatCon {conName : Name, subName : Name}

  sem decompose name =
  | (SPatCon shallow, pat & PatCon x) ->
    if nameEq shallow.conName x.ident then
      ([(_singleton shallow.subName x.subpat, _empty)], None ())
    else defaultDecomposition pat

  sem collectShallows =
  | PatCon x -> _ssingleton (SPatCon {conName = x.ident, subName = nameSym "carried"})

  sem spatToPat =
  | SPatCon x -> npcon_ x.conName (npvar_ x.subName)

  sem shallowCmp =
  | (SPatCon l, SPatCon r) -> nameCmp l.conName r.conName
end

lang ShallowMExpr = MExprAst + ShallowRecord + ShallowInt + ShallowOr + ShallowAnd + ShallowNot + ShallowSeq + ShallowCon + ShallowChar + ShallowBool
end

mexpr

use ShallowMExpr in

let scrutinee = nameSym "scrutinee" in
let x = npvar_ (nameSym "x") in
let y = npvar_ (nameSym "y") in
let bx = nameSym "bx" in
let patToBranch = lam label : String. lam pat.
  let label = str_ label in
  let mk = lam names : Map Name Name.
    let bindings = map (lam pair. nulet_ pair.0 (nvar_ pair.1)) (mapBindings names) in
    bindall_ (snoc bindings label) in
  (pat, mk) in
let mkMatch : Name -> SPat -> Expr -> Expr -> Expr = lam scrutinee. lam spat. lam t. lam e.
  match_ (nvar_ scrutinee) (spatToPat spat) t e in
let sprec_ = lam bindings: [(String, Name)]. SPatRecord (mapFromSeq cmpSID (map (lam b. (stringToSid b.0, b.1)) bindings)) in
let stot_ = lam n: Int. SPatSeqTot (create n (lam. nameSym "elem")) in
let sge_ = lam n: Int. SPatSeqGE { prefix = ref [], postfix = ref [], minLength = n } in
-- printLn "case";
-- dprintLn (decomposeNorm scrutinee (SPatWild (), pnot_ (por_ (pint_ 1) (pint_ 2))));
-- printLn "case";
-- dprintLn (decomposeNorm scrutinee (stot_ 1, pand_ (pseqedgew_ [x] []) (pnot_ (pseqedgew_ [pvarw_, pvarw_] []))));
-- printLn "case";
-- dprintLn (decomposeNorm scrutinee (sge_ 2, pand_ (pseqedgew_ [x] []) (pnot_ (pseqedgew_ [pvarw_, pvarw_] []))));
-- printLn "case";
-- let branches =
--   [ patToBranch (pseqtot_ [pint_ 1, pint_ 2])
--   , patToBranch (pand_ (pseqedgew_ [pint_ 1] []) (pand_ (pnot_ (pseqedgew_ [pvarw_, pvarw_, pvarw_] [])) x))
--   ] in
-- dprintLn (collectAllShallows branches);
let psome_ =
  let name = nameSym "Some" in
  npcon_ name in
let branches =
  [ patToBranch "a" (pstr_ "foo")
  , patToBranch "b" (pstr_ "foox")
  , patToBranch "c" (pstr_ "bar")
  , patToBranch "d" (pstr_ "bax")
  ] in
use MExprPrettyPrint in
printLn (expr2str (lower (nameSym "scrutinee") branches never_ mkMatch));
()
