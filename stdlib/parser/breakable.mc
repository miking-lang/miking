-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

/-

This file contains support for parsing operator expressions with
precedence and shallow forbids/allows. We support ambiguities
properly; the parsing procedure produces a shared packed parse forest
(SPPF), which can then be analyzed to determine the exact scope of any
ambiguities involved.

# Left-open, right-open, left-closed, and right-closed

A central concept herein is whether a "thing" (an operator or an
expression) is open or closed on either side. For example, the infix
operator `+` is both left-open and right-open, while the atomic
expression `7` is both left-closed and right-closed. These properties
transfer to partially constructed ASTs as well, `(_ + 4)` is left-open
but right-closed, while `(1 + 2)` is both left-closed and
right-closed.

# Precedence

The precedence definition used herein is less strict than the
conventional definition; it need not be total, nor transitive.
Instead, it is defined as follows: given a right-open operator `a` and
a left-open operator `b`, if we had a fully closed thing between them,
would it be permissible to group it

- only to the left, written as `a` <- `b`,
- only to the right, written as `a` -> `b`,
- either, written as `a` <-> `b`, or
- neither, written as `a` - `b`?

For example, we would likely give the following definitions for
addition and multiplication:

- `+` -> `*` (normal precedence)
- `*` <- `+` (normal precedence)
- `+` <- `+` (left-associative)
- `*` <- `*` (left-associative)

# Shallow forbids/allows

Operators may also pose restrictions on which other operators are
allowed to be their direct children. This is used to allow breaking
other kinds of productions into operators that are then limited to the
normal interactions. The canonical example is `if then else` (where
`else` is optional), which can be specified as follows:

- Prefix `if condition then`
- Infix `else`, where the left child must be exactly `if condition
  then`

This means that each `else` must have a corresponding `if condition
then`, but we can handle any ambiguities that arise
(e.g. dangling-`else`) using the same approach as for operators, i.e.,
we can resolve them with grouping parentheses.

As a consequence, the only ambiguities that can arise when using this
approach are those where it is unclear how things in the input
connect, as opposed to what their fundamental meaning is, which I
(vipa) hypothesize is quite helpful for the understandability of
ambiguities.

# Mid-level usage instructions

1. Create a value of the `BreakableGrammar` type. See the tests at the
end of the file for examples.
2. Call `breakableGenGrammar`. You can now query the result for the
value the parser expects you to supply when each operator is parsed in step 4.
3. Call `breakableInitState` to start parsing an expression. Values of
type `State` are mutable and should never be reused, consider them
consumed when they are passed to a function.
4. Call `breakableAddAtom`, `breakableAddPrefix`, `breakableAddInfix`,
and `breakableAddPostfix` repeatedly to add one "thing" at a time to
the parse. Note that these functions are quite strongly typed, e.g.,
you cannot call `breakableAddAtom` when the currently parsed
expression is already right-closed. See the tests for an example of
how to handle this when the calling code does not have the same
strictness in its types.
5. Call `breakableFinalizeParse` to create an SPPF of the parse.
6. Call `breakableConstructResult` to extract the single unambiguous
parse, or an ambiguity error.

-/

include "map.mc"
include "either.mc"
include "common.mc"
include "string.mc"  -- NOTE(vipa, 2021-02-15): This is only required for the tests, but we can't put an include only there

type AllowSet id
con AllowSet : Map id () -> AllowSet id
con DisallowSet : Map id () -> AllowSet id

type BreakableProduction prodLabel res self
con BreakableAtom :
  { label : prodLabel
  , construct : self -> res
  } -> BreakableProduction prodLabel res self
con BreakableInfix :
  { label : prodLabel
  , construct : self -> res -> res -> res
  , leftAllow : AllowSet prodLabel
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel res self
con BreakablePrefix :
  { label : prodLabel
  , construct : self -> res -> res
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel res self
con BreakablePostfix :
  { label : prodLabel
  , construct : self -> res -> res
  , leftAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel res self

type OpGrouping = {mayGroupLeft : Bool, mayGroupRight : Bool}

type BreakableGrammar prodLabel res self =
  { productions : [BreakableProduction prodLabel res self]
  , precedences : [((prodLabel, prodLabel), OpGrouping)]
  }

-- Each operator is uniquely identifiable by its ID, which is used to
-- look up precedence and the like
type OpId = Int

-- Each node in the parsed SPPF has a unique ID via `gensym`.
type PermanentId = Symbol

-- This is the type that is used to describe an item to be added to the parse
type LOpen
type LClosed
type ROpen
type RClosed
type BreakableInput res self lstyle rstyle
con AtomI :
  { id : OpId
  , construct : self -> res
  } -> BreakableInput res self LClosed RClosed
con InfixI :
  { id : OpId
  , leftAllow : AllowSet OpId
  , rightAllow : AllowSet OpId
  , precWhenThisIsRight : Map OpId OpGrouping
  , construct : self -> res -> res -> res
  } -> BreakableInput res self LOpen ROpen
con PrefixI :
  { id : OpId
  , rightAllow : AllowSet OpId
  , construct : self -> res -> res
  } -> BreakableInput res self LClosed ROpen
con PostfixI :
  { id : OpId
  , leftAllow : AllowSet OpId
  , precWhenThisIsRight : Map OpId OpGrouping
  , construct : self -> res -> res
  } -> BreakableInput res self LOpen RClosed

-- This describes a generated breakable grammar that is ready for parsing with
type BreakableGenGrammar prodLabel self res =
  { atoms : Map prodLabel (BreakableInput res self LClosed RClosed)
  , prefixes : Map prodLabel (BreakableInput res self LClosed ROpen)
  , infixes : Map prodLabel (BreakableInput res self LOpen ROpen)
  , postfixes : Map prodLabel (BreakableInput res self LOpen RClosed)
  }

-- NOTE(vipa, 2021-02-12): Many sequences in this file have an extra comment after them: NonEmpty. In the original implementation this was the type of a non-empty list, but we don't have one of those here, so for now I'm just recording that knowledge in comments, then we'll see what we do about it later.

-- This is the type of a node in an SPPF.
type PermanentNode res self
con AtomP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput res self LClosed RClosed
  , self : self
  } -> PermanentNode res self
con InfixP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput res self LOpen ROpen
  , self : self
  , leftChildAlts : [PermanentNode res self] -- NonEmpty
  , rightChildAlts : [PermanentNode res self] -- NonEmpty
  } -> PermanentNode res self
con PrefixP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput res self LClosed ROpen
  , self : self
  , rightChildAlts : [PermanentNode res self] -- NonEmpty
  } -> PermanentNode res self
con PostfixP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput res self LOpen RClosed
  , self : self
  , leftChildAlts : [PermanentNode res self] -- NonEmpty
  } -> PermanentNode res self

-- This is the data carried by tentative nodes, nodes that don't yet
-- have all their children known
type TentativeData res self
con InfixT :
  { input : BreakableInput res self LOpen ROpen
  , idx : Int
  , self : self
  , leftChildAlts : [PermanentNode res self] -- NonEmpty
  } -> TentativeData res self
con PrefixT :
  { input : BreakableInput res self LClose ROpen
  , idx : Int
  , self : self
  } -> TentativeData res self

-- As an optimization we keep track of a kind of "current" time, all
-- data from older timesteps is considered to be empty. The time is
-- essentially just which BreakableInput we're processing currently in
-- the sequence of input.
type TimeStep = Int

-- NOTE(vipa, 2021-02-12): This is the type of a node that may or may
-- not be in the final SPPF, we haven't seen enough of the input to
-- determine which yet. Note that there are references in the types,
-- i.e., they're not pure data. These references are used to optimize
-- knowledge of how new nodes are supposed to be added. Each of these
-- references also have an attached time step; if the timestep is
-- older than the current time in the algorithm then the reference
-- should be considered as unset (i.e., we don't have to clear all
-- references each iteration of the algorithm). We parse left to
-- right, thus all tentative nodes are left-closed
type TentativeNode res self rstyle
con TentativeLeaf :
  { parents : [TentativeNode res self ROpen] -- NonEmpty
  , node : PermanentNode res self
  } -> TentativeNode res self RClosed
con TentativeMid :
  { addedNodesLeftChildren : Ref (TimeStep, Ref [PermanentNode])
  , addedNodesRightChildren : Ref (TimeStep, [PermanentNode])
  , parents : [TentativeNode res self ROpen] -- NonEmpty
  , tentativeData : TentativeData res self
  , maxDistanceFromRoot : Int
  } -> TentativeNode res self ROpen
con TentativeRoot :
  { addedNodesLeftChildren : Ref (TimeStep, Ref [PermanentNode])
  , addedNodesRightChildren : Ref (TimeStep, [PermanentNode])
  } -> TentativeNode res self ROpen

-- The data we carry along while parsing
type State res self rstyle =
  { timestep : Ref TimeStep
  , nextIdx : Ref Int
  , frontier : [TentativeNode res self rstyle]
  }

let _firstTimeStep : TimeStep = 0
let _isBefore : TimeStep -> TimeStep -> Bool = lti
let _eqOpId : OpId -> OpId -> Bool = eqi
let _cmpOpId : OpId -> OpId -> Int = subi
let _rootID : OpId = negi 1
let _firstOpId : OpId = 0
let _nextOpId : OpId -> OpId = addi 1
let _uniqueID : () -> PermanentId = gensym
let _getParents
  : TentativeNode res self rstyle
  -> Option [TentativeNode res self ROpen] -- NonEmpty
  = lam n.
    match n with TentativeLeaf{parents = ps} | TentativeMid{parents = ps} then Some ps else
    match n with TentativeRoot _ then None () else
    never
let _opIdI
  : BreakableInput res self lstyle rstyle
  -> OpId
  = lam input.
    match input with
      AtomI {id = id}
      | InfixI {id = id}
      | PrefixI {id = id}
      | PostfixI {id = id}
      then id
    else never
let _opIdP
  : PermanentNode res self
  -> OpId
  = lam node.
    match node with AtomP {input = input} then _opIdI input else
    match node with InfixP {input = input} then _opIdI input else
    match node with PrefixP {input = input} then _opIdI input else
    match node with PostfixP {input = input} then _opIdI input else
    never
let _opIdxP
  : PermanentNode res self
  -> Int
  = lam node.
    match node with AtomP {idx = idx} then idx else
    match node with InfixP {idx = idx} then idx else
    match node with PrefixP {idx = idx} then idx else
    match node with PostfixP {idx = idx} then idx else
    never
let _opIdTD
  : TentativeData res self
  -> OpId
  = lam data.
    match data with InfixT {input = input} | PrefixT {input = input} then _opIdI input else
    never
let _opIdT
  : TentativeNode res self lstyle rstyle
  -> OpId
  = lam node.
    match node with TentativeLeaf{node = node} then _opIdP node else
    match node with TentativeMid{tentativeData = data} then _opIdTD data else
    match node with TentativeRoot _ then _rootID else
    never
let _addedNodesLeftChildren
  : TentativeNode res self ROpen
  -> [TentativeNode res self ROpen] -- NonEmpty
  = lam node.
    match node with TentativeRoot{addedNodesLeftChildren = x} | TentativeMid{addedNodesLeftChildren = x}
    then x
    else never
let _addedNodesRightChildren
  : TentativeNode res self ROpen
  -> [TentativeNode res self ROpen] -- NonEmpty
  = lam node.
    match node with TentativeRoot{addedNodesRightChildren = x} | TentativeMid{addedNodesRightChildren = x}
    then x
    else never

let breakableInAllowSet
  : id
  -> AllowSet id
  -> Bool
  = lam id. lam set.
    match set with AllowSet s then mapMem id s else
    match set with DisallowSet s then not (mapMem id s) else
    never

let breakableInsertAllowSet
  : id
  -> AllowSet id
  -> AllowSet id
  = lam id. lam set.
    match set with AllowSet s then AllowSet (mapInsert id () s) else
    match set with DisallowSet s then DisallowSet (mapRemove id s) else
    never

let breakableRemoveAllowSet
  : id
  -> AllowSet id
  -> AllowSet id
  = lam id. lam set.
    match set with AllowSet s then AllowSet (mapRemove id s) else
    match set with DisallowSet s then DisallowSet (mapInsert id () s) else
    never

let breakableMapAllowSet
  : (a -> b)
  -> (b -> b -> Int)
  -> AllowSet a
  -> AllowSet b
  = lam f. lam newCmp. lam s.
    let convert = lam s. mapFromSeq newCmp (map (lam x: (a, ()). (f x.0, ())) (mapBindings s)) in
    match s with AllowSet s then AllowSet (convert s) else
    match s with DisallowSet s then DisallowSet (convert s) else
    never

let breakableGenGrammar
  : (prodLabel -> prodLabel -> Int)
  -> BreakableGrammar prodLabel res self
  -> BreakableGenGrammar prodLabel res self
  = lam cmp. lam grammar.
    let nOpId : Ref OpId = ref _firstOpId in
    let newOpId : () -> OpId = lam.
      let res = deref nOpId in
      modref nOpId (_nextOpId res);
      res in

    let label
      : BreakableProduction prodLabel res self
      -> prodLabel
      = lam prod.
        match prod with BreakableAtom {label = label} then label else
        match prod with BreakablePrefix {label = label} then label else
        match prod with BreakableInfix {label = label} then label else
        match prod with BreakablePostfix {label = label} then label else
        never
    in

    let prodLabelToOpId : Map prodLabel OpId =
      mapFromSeq cmp (map (lam prod. (label prod, newOpId ())) grammar.productions) in
    let toOpId : prodLabel -> OpId = lam label. mapFindExn label prodLabelToOpId in

    -- TODO(vipa, 2021-02-15): This map can contain more entries than
    -- required; the inner map should only ever have entries where the
    -- key represents a right-open operator, but we here retain all
    -- operators from the outside, which could have more (redundant)
    -- entries
    let groupingByRightOp : Map OpId (Map OpId OpGrouping) =
      foldl
        (lam acc. lam grouping.
          match grouping with ((lplab, rplab), grouping) then
           let lid = toOpId lplab in
           let rid = toOpId rplab in
           let prev = match mapLookup rid acc
             with Some prev then prev
             else mapEmpty _cmpOpId in
           mapInsert rid (mapInsert lid grouping prev) acc
          else never)
        (mapEmpty _cmpOpId)
        grammar.precedences
    in
    let getGroupingByRight : OpId -> Map OpId OpGrouping = lam opid.
      match mapLookup opid groupingByRightOp with Some res then res
      else mapEmpty _cmpOpId
    in

    let atoms : Ref [(prodLabel, BreakableInput res self LClosed RClosed)] = ref [] in
    let prefixes : Ref [(prodLabel, BreakableInput res self LClosed ROpen)] = ref [] in
    let infixes : Ref [(prodLabel, BreakableInput res self LOpen ROpen)] = ref [] in
    let postfixes : Ref [(prodLabel, BreakableInput res self LOpen RClosed)] = ref [] in
    let updateRef : Ref a -> (a -> a) -> ()
      = lam ref. lam f. modref ref (f (deref ref)) in

    for_ grammar.productions
      (lam prod.
        let label = label prod in
        let id = toOpId label in
        match prod with BreakableAtom {construct = construct} then
          updateRef atoms (cons (label, AtomI {id = id, construct = construct}))
        else match prod with BreakablePrefix {construct = c, rightAllow = r} then
          let r = breakableMapAllowSet toOpId _cmpOpId r in
          updateRef prefixes (cons (label, PrefixI {id = id, construct = c, rightAllow = r}))
        else match prod with BreakableInfix {construct = c, leftAllow = l, rightAllow = r} then
          let l = breakableMapAllowSet toOpId _cmpOpId l in
          let r = breakableMapAllowSet toOpId _cmpOpId r in
          let p = getGroupingByRight id in
          updateRef infixes (cons (label, InfixI {id = id, construct = c, leftAllow = l, rightAllow = r, precWhenThisIsRight = p}))
        else match prod with BreakablePostfix {construct = c, leftAllow = l} then
          let l = breakableMapAllowSet toOpId _cmpOpId l in
          let p = getGroupingByRight id in
          updateRef postfixes (cons (label, PostfixI {id = id, construct = c, leftAllow = l, precWhenThisIsRight = p}))
        else never);

    { atoms = mapFromSeq cmp (deref atoms)
    , prefixes = mapFromSeq cmp (deref prefixes)
    , infixes = mapFromSeq cmp (deref infixes)
    , postfixes = mapFromSeq cmp (deref postfixes)
    }

let breakableInitState : () -> State res self ROpen
  = lam grammar.
    let timestep = ref _firstTimeStep in
    let nextIdx = ref 0 in
    let addedLeft = ref (_firstTimeStep, ref []) in
    let addedRight = ref (_firstTimeStep, []) in
    { timestep = timestep
    , nextIdx = nextIdx
    , frontier =
      [ TentativeRoot { addedNodesLeftChildren = addedLeft, addedNodesRightChildren = addedRight } ]
    }

recursive let _maxDistanceFromRoot
  : TentativeNode res self rstyle
  -> Int
  = lam n.
    match n with TentativeMid {maxDistanceFromRoot = r} then r else
    match n with TentativeRoot _ then 0 else
    match n with TentativeLeaf {parents = parents} then maxOrElse (lam. 0) subi (map _maxDistanceFromRoot parents) else
    dprintLn n;
    never
end

let _shallowAllowedLeft
  : BreakableInput res self LOpen rstyle
  -> TentativeNode res self RClosed
  -> Option (PermanentNode res self)
  = lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      match parent with InfixI {leftAllow = s} | PostfixI {leftAllow = s} then
        if breakableInAllowSet (_opIdP node) s then Some node else None ()
      else never
    else never

let _shallowAllowedRight
  : TentativeNode s res self ROpen
  -> TentativeNode res self RClosed
  -> Option (PermanentNode res self)
  = lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      match parent with TentativeRoot _ then Some node else
      match parent with TentativeMid {tentativeData = (InfixT {input = InfixI {rightAllow = s}} | PrefixT {input = PrefixI {rightAllow = s}})} then
        if breakableInAllowSet (_opIdP node) s then Some node else None ()
      else dprintLn parent; never
    else never

let _addRightChildren
  : State res self rstyle
  -> TentativeNode res self ROpen
  -> [PermanentNode res self] -- NonEmpty
  -> TentativeNode s res self RClosed
  = lam st. lam parent. lam children.
    match parent with TentativeMid {parents = parents, tentativeData = data} then
      let id = _uniqueID () in
      let node =
        match data with InfixT {input = input, idx = idx, self = self, leftChildAlts = l} then
          InfixP {id = id, idx = idx, input = input, self = self, leftChildAlts = l, rightChildAlts = children}
        else match data with PrefixT {input = input, idx = idx, self = self} then
          PrefixP {id = id, idx = idx, input = input, self = self, rightChildAlts = children}
        else never in
      TentativeLeaf {parents = parents, node = node}
    else match parent with TentativeRoot _ then
      error "Unexpectedly tried to add right children to the root"
    else never

let _addLeftChildren
  : State res self rstyle2
  -> BreakableInput res self LOpen rstyle
  -> self
  -> [PermanentNode res self] -- NonEmpty
  -> [TentativeNode res self ROpen] -- NonEmpty
  -> TentativeNode res self rstyle
  = lam st. lam input. lam self. lam leftChildren. lam parents.
    let idx = deref st.nextIdx in
    match input with InfixI _ then
      let time = deref st.timestep in
      let addedLeft = ref (_firstTimeStep, ref []) in
      let addedRight = ref (_firstTimeStep, []) in
      TentativeMid
        { parents = parents
        , addedNodesLeftChildren = addedLeft
        , addedNodesRightChildren = addedRight
        , maxDistanceFromRoot = addi 1 (maxOrElse (lam. 0) subi (map _maxDistanceFromRoot parents))
        , tentativeData = InfixT {input = input, idx = idx, self = self, leftChildAlts = leftChildren}
        }
    else match input with PostfixI _ then
      let id = _uniqueID () in
      TentativeLeaf
        { parents = parents
        , node = PostfixP {id = id, idx = idx, input = input, self = self, leftChildAlts = leftChildren}
        }
    else never

let _addRightChildToParent
  : TimeStep
  -> PermanentNode res self
  -> TentativeNode res self ROpen
  -> Option (TentativeNode res self ROpen)
  = lam time. lam child. lam parent.
    let target = _addedNodesRightChildren parent in
    match deref target with (lastUpdate, prev) then
      if _isBefore lastUpdate time then
        modref target (time, [child]);
        Some parent
      else
        modref target (time, cons child prev);
        None ()
    else never

let _addLeftChildToParent
  : TimeStep
  -> PermanentNode res self
  -> [TentativeNode res self ROpen] -- NonEmpty
  -> Option (NonEmpty (TentativeNode res self ROpen))
  = lam time. lam child. lam parents.
    match parents with [p] ++ _ then
      let target = _addedNodesLeftChildren p in
      match deref target with (lastUpdate, prev) then
        if _isBefore lastUpdate time then
          let leftChildrenHere = ref [child] in
          for_ parents (lam p. modref (_addedNodesLeftChildren p) (time, leftChildrenHere));
          Some parents
        else
          modref prev (cons child (deref prev));
          None ()
      else never
    else never -- TODO(vipa, 2021-02-12): this isn't technically never for the typesystem, since we're matching against a possibly empty list. However, the list will never be empty, by the comment about NonEmpty above

let _getOpGroup
  : BreakableInput res self LOpen rstyle
  -> OpId
  -> OpGrouping
  = lam input. lam id.
    if _eqOpId id _rootID then {mayGroupLeft = false, mayGroupRight = true} else
    match input with InfixI {precWhenThisIsRight = prec} | PostfixI {precWhenThisIsRight = prec} then
      match mapLookup id prec with Some res
      then res
      else {mayGroupLeft = true, mayGroupRight = true}
    else never

let _mayGroupRight
  : TentativeNode res self ROpen
  -> BreakableInput res self LOpen rstyle
  -> Bool
  = lam l. lam r.
    (_getOpGroup r (_opIdT l)).mayGroupRight

let _mayGroupLeft
  : TentativeNode res self ROpen
  -> BreakableInput res self LOpen rstyle
  -> Bool
  = lam l. lam r.
    (_getOpGroup r (_opIdT l)).mayGroupLeft

-- NOTE(vipa, 2021-02-15): This should be a private type, and/or replaced with some standard library type at a later point in time
type BreakableQueue res self = [Ref [TentativeNode res self ROpen]]
let _newQueueFromFrontier
  : [TentativeNode res self rstyle]
  -> BreakableQueue res self
  = lam frontier.
    -- TODO(vipa, 2021-02-12): This could use a `make : (Int -> a) -> Int -> [a]` that we discussed a while back
    map
      (lam. ref [])
      (create
        (addi 1 (maxOrElse (lam. 0) subi (map _maxDistanceFromRoot frontier)))
        (lam. ()))
let _addToQueue
  : TentativeNode res self ROpen
  -> BreakableQueue res self
  -> ()
  = lam node. lam queue.
    let dist = _maxDistanceFromRoot node in
    let target = get queue dist in
    modref target (snoc (deref target) node)
recursive let _popFromQueue
  : BreakableQueue
  -> Option (TentativeNode res self ROpen)
  = lam queue.
    match queue with queue ++ [target] then
      let nodes = deref target in
      match nodes with [node] ++ nodes then
        modref target nodes;
        Some node
      else _popFromQueue queue
    else None ()
end

-- NOTE(vipa, 2021-02-12): The type signatures in this function assume
-- that type variables are scoped, e.g., `rstyle` on `makeNewParents`
-- is the same `rstyle` as the one in the top-level type-signature
let _addLOpen
  : BreakableInput res self LOpen rstyle
  -> self
  -> State res self RClosed
  -> Option (State res self rstyle)
  = lam input. lam self. lam st.
    let time = addi 1 (deref st.timestep) in
    modref st.timestep time;

    let makeNewParents
      : [TentativeNode res self ROpen] -- NonEmpty
      -> TentativeNode res self rstyle
      = lam parents.
        match parents with [p] ++ _ then
          let snd: (a, b) -> b = lam x. x.1 in
          let cs = deref (snd (deref (_addedNodesLeftChildren p))) in
          match cs with [_] ++ _ then
            _addLeftChildren st input self cs parents
          else error "Somehow thought that a node would be a new parent, but it had no added children"
        else never -- TODO(vipa, 2021-02-12): this isn't technically never by for the typesystem, since we're matching against a possibly empty list. However, the list will never be empty, by the comment about NonEmpty above
    in

    let handleLeaf
      : BreakableQueue res self
      -> TentativeNode res self RClosed
      -> Option [TentativeNode res self ROpen] -- NonEmpty
      = lam queue. lam child.
        match _getParents child with Some parents then
          for_ parents
            (lam parent.
              if not (_mayGroupLeft parent input) then () else
              match _shallowAllowedRight parent child with Some child then
                match _addRightChildToParent time child parent with Some parent then
                  _addToQueue parent queue
                else ()
              else ());
          match (_shallowAllowedLeft input child, filter (lam l. _mayGroupRight l input) parents)
          with (Some child, parents & [_] ++ _) then
            _addLeftChildToParent time child parents
          else None ()
        else never
    in

    recursive let work
      : BreakableQueue res self
      -> [[TentativeNode res self ROpen]] -- The inner sequence is NonEmpty
      -> [[TentativeNode res self ROpen]] -- The inner sequence is NonEmpty
      = lam queue. lam acc.
        match _popFromQueue queue with Some (parent & TentativeMid{addedNodesRightChildren = addedRight}) then
          match deref addedRight with (_, children & [_] ++ _) then
            let acc = match handleLeaf queue (_addRightChildren st parent children)
              with Some n then cons n acc
              else acc in
            work queue acc
          else error "Somehow reached a parent without right children that was still added to the queue"
        else acc
    in

    let frontier = st.frontier in
    let queue = _newQueueFromFrontier frontier in
    let newParents = mapOption (handleLeaf queue) frontier in
    let newParents = work queue newParents in
    match map makeNewParents newParents with frontier & ([_] ++ _) then
      Some {st with frontier = frontier}
    else
      None ()

let breakableAddPrefix
  : BreakableInput res self LClosed ROpen
  -> self
  -> State res self ROpen
  -> State res self ROpen
  = lam input. lam self. lam st.
    let frontier = st.frontier in
    let time = deref st.timestep in
    let idx = deref st.nextIdx in
    modref st.nextIdx (addi 1 idx);
    let addedLeft = ref (_firstTimeStep, ref []) in
    let addedRight = ref (_firstTimeStep, []) in
    { st with frontier =
      [ TentativeMid
        { parents = frontier
        , addedNodesLeftChildren = addedLeft
        , addedNodesRightChildren = addedRight
        , maxDistanceFromRoot = addi 1 (maxOrElse (lam. 0) subi (map _maxDistanceFromRoot frontier))
        , tentativeData = PrefixT {input = input, idx = idx, self = self}
        }
      ]
    }

let breakableAddInfix
  : BreakableInput res self LOpen ROpen
  -> self
  -> State res self RClosed
  -> Option (State res self ROpen)
  = lam input. lam self. lam st.
    let res = _addLOpen input self st in
    modref st.nextIdx (addi 1 (deref st.nextIdx));
    res

let breakableAddPostfix
  : BreakableInput res self LOpen RClosed
  -> self
  -> State res self RClosed
  -> Option (State res self RClosed)
  = lam input. lam self. lam st.
    let res = _addLOpen input self st in
    modref st.nextIdx (addi 1 (deref st.nextIdx));
    res

let breakableAddAtom
  : BreakableInput res self LClosed RClosed
  -> self
  -> State res self ROpen
  -> State res self RClosed
  = lam input. lam self. lam st.
    let idx = deref st.nextIdx in
    modref st.nextIdx (addi 1 idx);
    let id = _uniqueID () in
    { st with frontier =
      [ TentativeLeaf
        { parents = st.frontier
        , node = AtomP {id = id, idx = idx, input = input, self = self}
        }
      ]
    }

-- TODO(vipa, 2021-02-15): There should be more information in case of
-- a parse failure, but it's not obvious precisely how the information
-- should be presented, it's not obvious to me that there will always
-- be a single cause of the failure that is easy to find
-- algorithmically
let breakableFinalizeParse
  : State res self RClosed
  -> Option [PermanentNode res self] -- NonEmpty
  = lam st.
    let time = addi 1 (deref st.timestep) in
    modref st.timestep time;

    let handleLeaf
      : BreakableQueue res self
      -> TentativeNode res self RClosed
      -> ()
      = lam queue. lam child.
        match _getParents child with Some parents then
          for_ parents
            (lam parent.
              match _shallowAllowedRight parent child with Some child then
                match _addRightChildToParent time child parent with Some parent then
                  _addToQueue parent queue
                else ()
              else ())
        else never
    in

    recursive let work
      : BreakableQueue res self
      -> [PermanentNode res self]
      = lam queue.
        match _popFromQueue queue with Some p then
          let snd: (a, b) -> b = lam x. x.1 in
          let children = (snd (deref (_addedNodesRightChildren p))) in
          match p with TentativeRoot _ then children
          else match (p, children) with (TentativeMid _, [_] ++ _) then
            handleLeaf queue (_addRightChildren st p children);
            work queue
          else match p with TentativeMid _ then
            error "Somehow reached a TentativeMid without right children, that was still added to the queue"
          else never
        else []
    in

    let frontier = st.frontier in
    let queue = _newQueueFromFrontier frontier in
    iter (handleLeaf queue) frontier;
    match work queue with res & [_] ++ _ then Some res else None ()

type Ambiguity self tokish = {first: self, last: self, partialResolutions: [[tokish]]}

type BreakableError self tokish
con Ambiguities : [Ambiguity self tokish] -> BreakableError self tokish

let breakableConstructResult
  : (self -> tokish)
  -> tokish
  -> tokish
  -> BreakableInput res self LCLosed RClosed
  -> [PermanentNode res self] -- NonEmpty
  -> Either (BreakableError self tokish) res
  = lam selfToTok. lam lpar. lam rpar. lam parInput. lam nodes.
    let parId = _opIdI parInput in
    -- NOTE(vipa, 2021-02-15): All alternatives for children at the
    -- same point in the tree have the exact same range in the input,
    -- i.e., they will have exactly the same input as first and last
    -- input, that's why we only look at one of the children, we don't
    -- need to look at the others
    recursive let range
      : PermanentNode res self
      -> {first: self, last: self}
      = lam node.
        match node with AtomP {self = self} then {first = self, last = self}
        else match node with InfixP {leftChildAlts = [l] ++ _, rightChildAlts = [r] ++ _} then
          { first = (range l).first
          , last = (range r).last
          }
        else match node with PrefixP {self = self, rightChildAlts = [r] ++ _} then
          { first = self
          , last = (range r).last
          }
        else match node with PostfixP {self = self, leftChildAlts = [l] ++ _} then
          { first = (range l).first
          , last = self
          }
        else never
    in

    recursive
      let flattenOne : PermanentNode res self -> [tokish] = lam node.
        switch node
        case AtomP {self = self} then [selfToTok self]
        case InfixP p then
          join [flattenMany p.leftChildAlts, [selfToTok p.self], flattenMany p.rightChildAlts]
        case PrefixP p then
          cons (selfToTok p.self) (flattenMany p.rightChildAlts)
        case PostfixP p then
          snoc (flattenMany p.leftChildAlts) (selfToTok p.self)
        end
      let flattenMany : [PermanentNode res self] -> [tokish] = lam nodes. -- NonEmpty
        match nodes with [n] ++ _ then
          flattenOne n
        else never
    in

    let resolveWith : [Int] -> AllowSet OpId -> [PermanentNode res self] -> ([Int] -> PermanentNode res self -> [[tokish]]) -> [[tokish]] =
      lam tops. lam allowSet. lam children. lam resolveDir.
        let needToWrap = not (null tops) in
        if needToWrap then
          if breakableInAllowSet parId allowSet then
            [cons lpar (snoc (flattenMany children) rpar)]
          else
            join (map (resolveDir tops) children)
        else
          [flattenMany children]
    in

    recursive let resolveDir : Bool -> Bool -> [Int] -> PermamentNode res self -> [[tokish]] =
      lam forceLeft. lam forceRight. lam tops. lam node.
        switch node
        case AtomP {self = self} then [[selfToTok self]]
        case InfixP (node & {input = InfixI i}) then
          let left =
            if forceLeft then
              [cons lpar (snoc (flattenMany node.leftChildAlts) rpar)]
            else
              let tops = filter (gti node.idx) tops in
              resolveWith tops i.leftAllow node.leftChildAlts (resolveDir false true)
          in
          let right =
            if forceRight then
              [cons lpar (snoc (flattenMany node.rightChildAlts) rpar)]
            else
              let tops = filter (lti node.idx) tops in
              resolveWith tops i.rightAllow node.rightChildAlts (resolveDir true false)
          in
          let here = [selfToTok node.self] in
          seqLiftA2 (lam l. lam r. join [l, here, r]) left right
        case PrefixP (node & {input = PrefixI i}) then
          let left = [[]] in
          let right =
            if forceRight then
              [cons lpar (snoc (flattenMany node.rightChildAlts) rpar)]
            else
              let tops = filter (lti node.idx) tops in
              resolveWith tops i.rightAllow node.rightChildAlts (resolveDir true false)
          in
          let here = [selfToTok node.self] in
          -- OPT(vipa, 2021-10-11): This follows the structure above, but
          -- could be done with just a concatMap
          seqLiftA2 (lam l. lam r. join [l, here, r]) left right
        case PostfixP (node & {input = PostfixI i}) then
          let left =
            if forceLeft then
              [cons lpar (snoc (flattenMany node.leftChildAlts) rpar)]
            else
              let tops = filter (gti node.idx) tops in
              resolveWith tops i.leftAllow node.leftChildAlts (resolveDir false true)
          in
          let right = [[]] in
          let here = [selfToTok node.self] in
          -- OPT(vipa, 2021-10-11): This follows the structure above, but
          -- could be done with just a concatMap
          seqLiftA2 (lam l. lam r. join [l, here, r]) left right
        end
    in
    let ambiguities : Ref [Ambiguity self] = ref [] in

    recursive
      let workMany
        : [PermanentNode res self] -- NonEmpty
        -> Option res
        = lam tops.
          match tops with [n] then
            workOne n
          else match tops with [n] ++ _ then
            -- OPT(vipa, 2021-10-11): This should probably be a set that supports
            -- member querying as well as `removeGreaterThan` and `removeLesserThan`
            let topIdxs = map _opIdxP tops in
            let range = range n in
            let resolutions = join (map (resolveDir false false topIdxs) tops) in
            -- TODO(vipa, 2021-10-11): Compute valid elisons
            let err = {first = range.first, last = range.last, partialResolutions = resolutions} in
            modref ambiguities (cons err (deref ambiguities));
            None ()
          else dprintLn tops; never
      let workOne
        : PermanentNode res self
        -> Option res
        = lam node.
          match node with AtomP {self = self, input = AtomI {construct = c}} then
            Some (c self)
          else match node with PrefixP {self = self, rightChildAlts = rs, input = PrefixI {construct = c}} then
            optionMap (c self) (workMany rs)
          else match node with InfixP {self = self, leftChildAlts = ls, rightChildAlts = rs, input = InfixI {construct = c}} then
            let l = workMany ls in
            let r = workMany rs in
            optionZipWith (c self) l r
          else match node with PostfixP {self = self, leftChildAlts = ls, input = PostfixI {construct = c}} then
            optionMap (c self) (workMany ls)
          else never
    in

    match workMany nodes
    with Some res then Right res
    else Left (Ambiguities (deref ambiguities))

mexpr

type Ast in
con IntA : {pos: Int, val: Int} -> Ast in
con PlusA : {pos: Int, l: Ast, r: Ast} -> Ast in
con TimesA : {pos: Int, l: Ast, r: Ast} -> Ast in
con DivideA : {pos: Int, l: Ast, r: Ast} -> Ast in
con NegateA : {pos: Int, r: Ast} -> Ast in
con IfA : {pos: Int, r: Ast} -> Ast in
con ElseA : {pos: Int, l: Ast, r: Ast} -> Ast in
con NonZeroA : {pos: Int, l: Ast} -> Ast in
con ParA : {pos: Int} -> Ast in

type Self = {pos: Int, val: Int, str: String} in

let allowAllBut = lam xs. DisallowSet (mapFromSeq cmpString (map (lam x. (x, ())) xs)) in
let allowAll = allowAllBut [] in
let allowOnly = lam xs. AllowSet (mapFromSeq cmpString (map (lam x. (x, ())) xs)) in

let highLowPrec
  : [prodLabel]
  -> [prodLabel]
  -> [((prodLabel, prodLabel), OpGrouping)]
  =
    let mkGrouping = lam high. lam low.
      [ ((high, low), {mayGroupLeft = true, mayGroupRight = false})
      , ((low, high), {mayGroupLeft = false, mayGroupRight = true})
      ] in
    lam high. lam low. join (seqLiftA2 mkGrouping high low)
in

recursive let precTableNoEq
  : [[prodLabel]]
  -> [((prodLabel, prodLabel), OpGrouping)]
  = lam table.
    match table with [high] ++ lows then
      concat (highLowPrec high (join lows)) (precTableNoEq lows)
    else []
in

let grammar =
  { productions =
    [ BreakableAtom {label = "int", construct = lam x: Self. IntA {pos = x.pos, val = x.val}}
    , BreakableAtom {label = "par", construct = lam x: Self. ParA {pos = x.pos}}
    , BreakableInfix
      { label = "plus"
      , construct = lam x: Self. lam l. lam r. PlusA {pos = x.pos, l = l, r = r}
      , leftAllow = allowAll
      , rightAllow = allowAll
      }
    , BreakableInfix
      { label = "times"
      , construct = lam x: Self. lam l. lam r. TimesA {pos = x.pos, l = l, r = r}
      , leftAllow = allowAll
      , rightAllow = allowAll
      }
    , BreakableInfix
      { label = "divide"
      , construct = lam x: Self. lam l. lam r. DivideA {pos = x.pos, l = l, r = r}
      , leftAllow = allowAll
      , rightAllow = allowAll
      }
    , BreakablePrefix
      { label = "negate"
      , construct = lam x: Self. lam r. NegateA {pos = x.pos, r = r}
      , rightAllow = allowAll
      }
    , BreakablePrefix
      { label = "if"
      , construct = lam x: Self. lam r. IfA {pos = x.pos, r = r}
      , rightAllow = allowAll
      }
    , BreakableInfix
      { label = "else"
      , construct = lam x: Self. lam l. lam r. ElseA {pos = x.pos, l = l, r = r}
      , leftAllow = allowOnly ["if"]
      , rightAllow = allowAll
      }
    , BreakablePostfix
      { label = "nonZero"
      , construct = lam x: Self. lam l. NonZeroA {pos = x.pos, l = l}
      , leftAllow = allowAll
      }
    ]
  , precedences = join
    [ precTableNoEq
      [ ["negate"]
      , ["times", "divide"]
      , ["plus"]
      , ["if"]
      ]
    ]
  }
in
let genned = breakableGenGrammar cmpString grammar in
let atom = lam label. mapFindExn label genned.atoms in
let prefix = lam label. mapFindExn label genned.prefixes in
let infix = lam label. mapFindExn label genned.infixes in
let postfix = lam label. mapFindExn label genned.postfixes in

type Self = {val : Int, pos : Int, str : String} in

type TestToken in
con TestAtom : { x : Self, input : BreakableInput Ast Self RClosed RClosed } -> TestToken in
con TestPrefix : { x : Self, input : BreakableInput Ast Self RClosed ROpen } -> TestToken in
con TestInfix : { x : Self, input : BreakableInput Ast Self ROpen ROpen } -> TestToken in
con TestPostfix : { x : Self, input : BreakableInput Ast Self ROpen RClosed } -> TestToken in

let _int =
  let input = atom "int" in
  lam val. lam pos. TestAtom {x = {val = val, pos = pos, str = int2string val}, input = input} in
let _plus =
  let input = infix "plus" in
  lam pos. TestInfix {x = {val = 0, pos = pos, str = "+"}, input = input} in
let _times =
  let input = infix "times" in
  lam pos. TestInfix {x = {val = 0, pos = pos, str = "*"}, input = input} in
let _divide =
  let input = infix "divide" in
  lam pos. TestInfix {x = {val = 0, pos = pos, str = "/"}, input = input} in
let _negate =
  let input = prefix "negate" in
  lam pos. TestPrefix {x = {val = 0, pos = pos, str = "-"}, input = input} in
let _if =
  let input = prefix "if" in
  lam pos. TestPrefix {x = {val = 0, pos = pos, str = "if"}, input = input} in
let _else =
  let input = infix "else" in
  lam pos. TestInfix {x = {val = 0, pos = pos, str = "else"}, input = input} in
let _nonZero =
  let input = postfix "nonZero" in
  lam pos. TestPostfix {x = {val = 0, pos = pos, str = "?"}, input = input} in

let selfToTok : Self -> String = lam x. x.str in

let testParse
  : [Int -> TestToken]
  -> Option (Either (BreakableError Self String) Ast)
  = recursive
      let workROpen = lam pos. lam st. lam tokens.
        match tokens with [t] ++ tokens then
          let t = t pos in
          let pos = addi 1 pos in
          match t with TestAtom {x = self, input = input} then
            workRClosed pos (breakableAddAtom input self st) tokens
          else match t with TestPrefix {x = self, input = input} then
            workROpen pos (breakableAddPrefix input self st) tokens
          else None ()
        else None ()
      let workRClosed = lam pos. lam st. lam tokens.
        match tokens with [t] ++ tokens then
          let t = t pos in
          let pos = addi 1 pos in
          match t with TestInfix {x = self, input = input} then
            match breakableAddInfix input self st with Some st
            then workROpen pos st tokens
            else None ()
          else match t with TestPostfix {x = self, input = input} then
            match breakableAddPostfix input self st with Some st
            then workRClosed pos st tokens
            else None ()
          else None ()
        else optionMap (breakableConstructResult selfToTok "(" ")" (atom "par")) (breakableFinalizeParse st)
    in workROpen 0 (breakableInitState ())
in

utest testParse []
with None ()
in

utest testParse [_int 4]
with Some (Right (IntA {val = 4,pos = 0}))
in

utest testParse [_int 4, _plus]
with None ()
in

utest testParse [_int 4, _plus, _int 7]
with Some (Right
  (PlusA
    { pos = 1
    , l = (IntA {val = 4,pos = 0})
    , r = (IntA {val = 7,pos = 2})
    }))
in

utest testParse [_negate, _int 8]
with Some (Right
  (NegateA
    { pos = 0
    , r = (IntA {val = 8,pos = 1})
    }))
in

utest testParse [_negate, _negate, _int 8]
with Some (Right
  (NegateA
    { pos = 0
    , r = (NegateA
      { pos = 1
      , r = (IntA {val = 8,pos = 2})
      })
    }))
in

utest testParse [_int 9, _nonZero, _nonZero]
with Some (Right
  (NonZeroA
    { pos = 2
    , l = (NonZeroA
      { pos = 1
      , l = (IntA {val = 9,pos = 0})})
    }))
in

utest testParse [_negate, _nonZero]
with None ()
in

utest testParse [_int 1, _plus, _int 2, _times, _int 3]
with Some (Right
  (PlusA
    { pos = 1
    , l = (IntA {val = 1,pos = 0})
    , r = (TimesA
      { pos = 3
      , l = (IntA {val = 2,pos = 2})
      , r = (IntA {val = 3,pos = 4})
      })
    }))
in

utest testParse [_int 1, _times, _int 2, _plus, _int 3]
with Some (Right
  (PlusA
    { pos = 3
    , l = (TimesA
      { pos = 1
      , l = (IntA {val = 1,pos = 0})
      , r = (IntA {val = 2,pos = 2})
      })
    , r = (IntA {val = 3,pos = 4})
    }))
in

utest testParse [_int 1, _times, _int 2, _divide, _int 3]
with Some (Left (Ambiguities (
  [ { first = {val = 1,pos = 0,str = "1"}
    , last = {val = 3,pos = 4,str = "3"}
    , partialResolutions =
      [ ["1", "*", "(", "2", "/", "3", ")"]
      , ["(", "1", "*", "2", ")", "/", "3"]
      ]
    }
  ])))
in

utest testParse [_int 1, _times, _int 2, _divide, _int 3, _plus, _int 4]
with Some (Left (Ambiguities (
  [ { first = {val = 1,pos = 0,str = "1"}
    , last = {val = 3,pos = 4,str = "3"}
    , partialResolutions =
      [ ["1","*","(","2","/","3",")"]
      , ["(","1","*","2", ")","/","3"]
      ]
    }
  ])))
in

utest testParse [_int 0, _plus, _int 1, _times, _int 2, _divide, _int 3]
with Some (Left (Ambiguities (
  [ { first = {val = 1,pos = 2,str = "1"}
    , last = {val = 3,pos = 6,str = "3"}
    , partialResolutions =
      [ ["1","*","(","2","/","3",")"]
      , ["(","1","*","2",")","/","3"]
      ]
    }
  ])))
in

-- TODO(vipa, 2021-02-15): When we compute elisons we can report two ambiguities here, the nested one is independent
utest testParse [_int 0, _plus, _int 1, _times, _int 2, _divide, _int 3, _plus, _int 4]
with Some (Left (Ambiguities (
  [ { first = {val = 0,pos = 0,str = "0"}
    , last = {val = 4,pos = 8,str = "4"}
    , partialResolutions =
    [ ["0","+","(","1","*","2","/","3","+","4",")"]
    , ["(","0","+","1","*","2","/","3",")","+","4"]
    ]
    }
  ])))
in

-- TODO(vipa, 2021-02-15): Do we want to specify the order of the returned ambiguities in some way?
utest testParse [_int 1, _times, _int 2, _divide, _int 3, _plus, _int 4, _divide, _int 5, _times, _int 6]
with Some (Left (Ambiguities (
  [ { first = {val = 4, pos = 6,str = "4"}
    , last = {val = 6, pos = 10,str = "6"}
    , partialResolutions =
      [ ["4","/","(","5","*","6",")"]
      , ["(","4","/","5",")","*","6"]
      ]
    }
  , { first = {val = 1,pos = 0,str = "1"}
    , last = {val = 3,pos = 4,str = "3"}
    , partialResolutions =
      [ ["1","*","(","2","/","3",")"]
      , ["(","1","*","2",")","/","3"]
      ]
    }
  ])))
in

utest testParse [_if, _int 1]
with Some (Right
  (IfA
    { pos = 0
    , r = (IntA {val = 1,pos = 1})
    }))
in

utest testParse [_if, _int 1, _else, _int 2]
with Some (Right
  (ElseA
    { pos = 2
    , l = (IfA
      { pos = 0
      , r = (IntA {val = 1,pos = 1})
      })
    , r = (IntA {val = 2,pos = 3})
    }))

in

utest testParse [_if, _int 1, _else, _int 2, _else, _int 3]
with None ()
in

utest testParse [_if, _if, _int 1, _else, _int 2]
with Some (Left (Ambiguities (
  [ { first = {val = 0,pos = 0,str = "if"}
    , last = {val = 2,pos = 4,str = "2"}
    , partialResolutions =
      [ ["if","(","if","1", "else","2",")"]
      , ["if","(","if","1", ")","else","2"]
      ]
    }
  ])))
in

utest testParse [_negate, _if, _int 1, _else, _int 2]
with Some (Right
  (NegateA
    { pos = 0
    , r = (ElseA
      { pos = 3
      , l = (IfA
        { pos = 1
        , r = (IntA {val = 1,pos = 2})
        })
      , r = (IntA {val = 2,pos = 4})
      })
    }))
in

utest testParse [_if, _negate, _if, _int 1, _else, _int 2]
with Some (Left (Ambiguities (
  [ { first = {val = 0,pos = 0,str = "if"}
    , last = {val = 2,pos = 5,str = "2"}
    , partialResolutions =
      [ ["if","(","-","if", "1","else","2",")"]
      , ["if","(","-","if", "1",")","else","2"]
      ]
    }
  ])))
in

utest testParse [_int 1, _plus, _if, _negate, _if, _int 1, _else, _int 2]
with Some (Left (Ambiguities (
  [ { first = {val = 0,pos = 2,str = "if"}
    , last = {val = 2,pos = 7,str = "2"}
    , partialResolutions =
      [ ["if","(","-","if", "1","else","2",")"]
      , ["if","(","-","if", "1",")","else","2"]
      ]
    }
  ])))
in

utest testParse [_int 1, _times, _if, _int 7, _else, _int 12]
with Some (Right
  (TimesA
    { pos = 1
    , l = (IntA {val = 1,pos = 0})
    , r = (ElseA
      { pos = 4
      , l = (IfA
        { pos = 2
        , r = (IntA {val = 7,pos = 3})
        })
      , r = (IntA {val = 12,pos = 5})
      })
    }))
in

utest testParse [_int 1, _plus, _plus, _int 2]
with None ()
in

utest testParse [_int 1, _plus, _nonZero]
with None ()
in

utest testParse [_int 1, _nonZero, _plus, _int 2]
with Some (Right
  (PlusA
    { pos = 2
    , l = (NonZeroA
      { pos = 1
      , l = (IntA {val = 1,pos = 0})
      })
    , r = (IntA {val = 2,pos = 3})
    }))
in

()
