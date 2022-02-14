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

# Grammar restrictions for resolvable ambiguity

To ensure that all ambiguities that may arise while parsing are
resolvable there are two restrictions:

- Grouping parentheses should be allowed almost always; the only place
  they are not allowed are inside broken productions. For example,
  using the `if then else` example above, parentheses are not allowed
  on the left of `else` since that would split it from the `if`.
  - This should be expressed by using an `AllowSet` that does not
    contain the grouping operator. Most other locations should use
    `DisallowSet`s with very few members.
- It should be unambiguous how we "unbreak" a broken production. If
  there were such an ambiguity we could not resolve it since we can't
  put parentheses inside a broken production, following the previous
  point.

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
6. Call `breakableReportAmbiguities` to find any ambiguities and their
resolutions. If this function returns an empty list then the SPPF
represents a single valid AST, which can be constructed either through
breakableConstructSimple or manual traversal of the SPPF.

-/

include "map.mc"
include "set.mc"
include "either.mc"
include "common.mc"
include "string.mc"  -- NOTE(vipa, 2021-02-15): This is only required for the tests, but we can't put an include only there

type AllowSet id
con AllowSet : Map id () -> AllowSet id
con DisallowSet : Map id () -> AllowSet id

let _isWhitelist
  : AllowSet id -> Bool
  = lam a. match a with AllowSet _ then true else false

type BreakableProduction prodLabel
con BreakableAtom :
  { label : prodLabel
  } -> BreakableProduction prodLabel
con BreakableInfix :
  { label : prodLabel
  , leftAllow : AllowSet prodLabel
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel
con BreakablePrefix :
  { label : prodLabel
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel
con BreakablePostfix :
  { label : prodLabel
  , leftAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel

type OpGrouping = {mayGroupLeft : Bool, mayGroupRight : Bool}

type BreakableGrammar prodLabel =
  { productions : [BreakableProduction prodLabel]
  , precedences : [((prodLabel, prodLabel), OpGrouping)]
  , topAllowed : AllowSet prodLabel
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
type BreakableInput lstyle rstyle
con AtomI :
  { id : OpId
  , allowedTop : Bool
  } -> BreakableInput LClosed RClosed
con InfixI :
  { id : OpId
  , allowedTop : Bool
  , leftAllow : AllowSet OpId
  , rightAllow : AllowSet OpId
  , precWhenThisIsRight : Map OpId OpGrouping
  } -> BreakableInput LOpen ROpen
con PrefixI :
  { id : OpId
  , allowedTop : Bool
  , rightAllow : AllowSet OpId
  } -> BreakableInput LClosed ROpen
con PostfixI :
  { id : OpId
  , allowedTop : Bool
  , leftAllow : AllowSet OpId
  , precWhenThisIsRight : Map OpId OpGrouping
  } -> BreakableInput LOpen RClosed

-- This describes a generated breakable grammar that is ready for parsing with
type BreakableGenGrammar prodLabel =
  { atoms : Map prodLabel (BreakableInput LClosed RClosed)
  , prefixes : Map prodLabel (BreakableInput LClosed ROpen)
  , infixes : Map prodLabel (BreakableInput LOpen ROpen)
  , postfixes : Map prodLabel (BreakableInput LOpen RClosed)
  }

-- NOTE(vipa, 2021-02-12): Many sequences in this file have an extra
-- comment after them: NonEmpty. In the original implementation this
-- was the type of a non-empty list, but we don't have one of those
-- here, so for now I'm just recording that knowledge in comments,
-- then we'll see what we do about it later.

-- This is the type of a node in an SPPF. The `self`, `leftChildAlts`,
-- and `rightChildAlts` fields are considered public, all others are
-- implementation details and should be considered private. In
-- particular this means that it's fine to examine an SPPF (i.e.,
-- pattern match on it, typically to construct an AST), but not to
-- construct a new SPPF.
type PermanentNode self
con AtomP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput LClosed RClosed
  , self : self LClosed RClosed
  } -> PermanentNode self
con InfixP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput LOpen ROpen
  , self : self LOpen ROpen
  , leftChildAlts : [PermanentNode self] -- NonEmpty
  , rightChildAlts : [PermanentNode self] -- NonEmpty
  } -> PermanentNode self
con PrefixP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput LClosed ROpen
  , self : self LClosed ROpen
  , rightChildAlts : [PermanentNode self] -- NonEmpty
  } -> PermanentNode self
con PostfixP :
  { id : PermanentId
  , idx : Int
  , input : BreakableInput LOpen RClosed
  , self : self LOpen ROpen
  , leftChildAlts : [PermanentNode self] -- NonEmpty
  } -> PermanentNode self

-- This is the data carried by tentative nodes, nodes that don't yet
-- have all their children known
type TentativeData self
con InfixT :
  { input : BreakableInput LOpen ROpen
  , idx : Int
  , self : self LOpen ROpen
  , leftChildAlts : [PermanentNode self] -- NonEmpty
  } -> TentativeData self
con PrefixT :
  { input : BreakableInput LClose ROpen
  , idx : Int
  , self : self LClosed ROpen
  } -> TentativeData self

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
type TentativeNode self rstyle
con TentativeLeaf :
  { parents : [TentativeNode self ROpen] -- NonEmpty
  , node : PermanentNode self
  } -> TentativeNode self RClosed
con TentativeMid :
  { addedNodesLeftChildren : Ref (TimeStep, Ref [PermanentNode])
  , addedNodesRightChildren : Ref (TimeStep, [PermanentNode])
  , parents : [TentativeNode self ROpen] -- NonEmpty
  , tentativeData : TentativeData self
  , maxDistanceFromRoot : Int
  } -> TentativeNode self ROpen
con TentativeRoot :
  { addedNodesLeftChildren : Ref (TimeStep, Ref [PermanentNode])
  , addedNodesRightChildren : Ref (TimeStep, [PermanentNode])
  } -> TentativeNode self ROpen

-- The data we carry along while parsing
type State self rstyle =
  { timestep : Ref TimeStep
  , nextIdx : Ref Int
  , frontier : [TentativeNode self rstyle]
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
  : TentativeNode self rstyle
  -> Option [TentativeNode self ROpen] -- NonEmpty
  = lam n.
    switch n
    case TentativeLeaf{parents = ps} | TentativeMid{parents = ps} then Some ps
    case TentativeRoot _ then None ()
    end
let _opIdI
  : BreakableInput lstyle rstyle
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
  : PermanentNode self
  -> OpId
  = lam node.
    match node with AtomP {input = input} then _opIdI input else
    match node with InfixP {input = input} then _opIdI input else
    match node with PrefixP {input = input} then _opIdI input else
    match node with PostfixP {input = input} then _opIdI input else
    never
let _opIdxP
  : PermanentNode self
  -> Int
  = lam node.
    match node with AtomP {idx = idx} then idx else
    match node with InfixP {idx = idx} then idx else
    match node with PrefixP {idx = idx} then idx else
    match node with PostfixP {idx = idx} then idx else
    never
let _opIdTD
  : TentativeData self
  -> OpId
  = lam data.
    match data with InfixT {input = input} | PrefixT {input = input} then _opIdI input else
    never
let _opIdT
  : TentativeNode self rstyle
  -> OpId
  = lam node.
    match node with TentativeLeaf{node = node} then _opIdP node else
    match node with TentativeMid{tentativeData = data} then _opIdTD data else
    match node with TentativeRoot _ then _rootID else
    never
let _addedNodesLeftChildren
  : TentativeNode self ROpen
  -> [TentativeNode self ROpen] -- NonEmpty
  = lam node.
    match node with TentativeRoot{addedNodesLeftChildren = x} | TentativeMid{addedNodesLeftChildren = x}
    then x
    else never
let _addedNodesRightChildren
  : TentativeNode self ROpen
  -> [TentativeNode self ROpen] -- NonEmpty
  = lam node.
    match node with TentativeRoot{addedNodesRightChildren = x} | TentativeMid{addedNodesRightChildren = x}
    then x
    else never
let _isTopAllowedP = lam p.
  switch p
  case AtomP { input = AtomI { allowedTop = allowedTop } } then allowedTop
  case InfixP { input = InfixI { allowedTop = allowedTop } } then allowedTop
  case PrefixP { input = PrefixI { allowedTop = allowedTop } } then allowedTop
  case PostfixP { input = PostfixI { allowedTop = allowedTop } } then allowedTop
  end
-- TODO(vipa, 2022-02-14): This doesn't have a good return type, fix
let _callWithSelfP
  : (all lstyle. all rstyle. self lstyle rstyle -> x)
  -> PermanentNode self
  -> x
  = lam f. lam p.
  switch p
  case AtomP p then f p.self
  case InfixP p then f p.self
  case PrefixP p then f p.self
  case PostfixP p then f p.self
  end

let _isBrokenEdge
  : Bool
  -> PermanentNode self
  -> Bool
  = lam parenForbidden. lam node.
    or parenForbidden (not (_isTopAllowedP node))
let _leftStuffP = lam p.
  switch p
  case InfixP ({ input = InfixI { leftAllow = allows } } & r) then
    Some (r.leftChildAlts, allows)
  case PostfixP ({ input = PostfixI { leftAllow = allows } } & r) then
    Some (r.leftChildAlts, allows)
  case _ then None ()
  end
let _rightStuffP = lam p.
  switch p
  case InfixP ({ input = InfixI { rightAllow = allows } } & r) then
    Some (r.rightChildAlts, allows)
  case PrefixP ({ input = PrefixI { rightAllow = allows } } & r) then
    Some (r.rightChildAlts, allows)
  case _ then None ()
  end

let _brokenIdxesP
  : PermanentNode self
  -> [Int]
  = recursive let work = lam isWhitelist. lam p.
      if _isBrokenEdge isWhitelist p then
        let l = match _leftStuffP p with Some (children, allows)
          then join (map (work (_isWhitelist allows)) children)
          else [] in
        let r = match _rightStuffP p with Some (children, allows)
          then join (map (work (_isWhitelist allows)) children)
          else [] in
        join [l, [_opIdxP p], r]
      else []
    in work true
let _brokenChildrenP
  : PermanentNode self
  -> [PermanentNode self]
  = recursive let work = lam isWhitelist. lam p.
      if _isBrokenEdge isWhitelist p then
        let l = match _leftStuffP p with Some (children, allows)
          then join (map (work (_isWhitelist allows)) children)
          else [] in
        let r = match _rightStuffP p with Some (children, allows)
          then join (map (work (_isWhitelist allows)) children)
          else [] in
        concat l r
      else [p]
    in work true

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
  -> BreakableGrammar prodLabel
  -> BreakableGenGrammar prodLabel
  = lam cmp. lam grammar.
    let nOpId : Ref OpId = ref _firstOpId in
    let newOpId : () -> OpId = lam.
      let res = deref nOpId in
      modref nOpId (_nextOpId res);
      res in

    let label
      : BreakableProduction prodLabel
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

    let atoms : Ref [(prodLabel, BreakableInput LClosed RClosed)] = ref [] in
    let prefixes : Ref [(prodLabel, BreakableInput LClosed ROpen)] = ref [] in
    let infixes : Ref [(prodLabel, BreakableInput LOpen ROpen)] = ref [] in
    let postfixes : Ref [(prodLabel, BreakableInput LOpen RClosed)] = ref [] in
    let updateRef : Ref a -> (a -> a) -> ()
      = lam ref. lam f. modref ref (f (deref ref)) in

    let isTopAllowed =
      let topAllowed = breakableMapAllowSet toOpId _cmpOpId grammar.topAllowed in
      lam id. breakableInAllowSet id topAllowed in

    for_ grammar.productions
      (lam prod.
        let label = label prod in
        let id = toOpId label in
        match prod with BreakableAtom _ then
          updateRef atoms (cons (label, AtomI {id = id, allowedTop = isTopAllowed id}))
        else match prod with BreakablePrefix {rightAllow = r} then
          let r = breakableMapAllowSet toOpId _cmpOpId r in
          updateRef prefixes (cons (label, PrefixI {id = id, allowedTop = isTopAllowed id, rightAllow = r}))
        else match prod with BreakableInfix {leftAllow = l, rightAllow = r} then
          let l = breakableMapAllowSet toOpId _cmpOpId l in
          let r = breakableMapAllowSet toOpId _cmpOpId r in
          let p = getGroupingByRight id in
          updateRef infixes (cons (label, InfixI {id = id, allowedTop = isTopAllowed id, leftAllow = l, rightAllow = r, precWhenThisIsRight = p}))
        else match prod with BreakablePostfix {leftAllow = l} then
          let l = breakableMapAllowSet toOpId _cmpOpId l in
          let p = getGroupingByRight id in
          updateRef postfixes (cons (label, PostfixI {id = id, allowedTop = isTopAllowed id, leftAllow = l, precWhenThisIsRight = p}))
        else never);

    { atoms = mapFromSeq cmp (deref atoms)
    , prefixes = mapFromSeq cmp (deref prefixes)
    , infixes = mapFromSeq cmp (deref infixes)
    , postfixes = mapFromSeq cmp (deref postfixes)
    }

let breakableInitState : () -> State self ROpen
  = lam.
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
  : TentativeNode self rstyle
  -> Int
  = lam n.
    switch n
    case TentativeMid {maxDistanceFromRoot = r} then r
    case TentativeRoot _ then 0
    case TentativeLeaf {parents = ps} then
      maxOrElse (lam. 0) subi (map _maxDistanceFromRoot ps)
    end
end

let _shallowAllowedLeft
  : BreakableInput LOpen rstyle
  -> TentativeNode self RClosed
  -> Option (PermanentNode self)
  = lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      match parent with InfixI {leftAllow = s} | PostfixI {leftAllow = s} then
        if breakableInAllowSet (_opIdP node) s then Some node else None ()
      else never
    else never

let _shallowAllowedRight
  : TentativeNode self ROpen
  -> TentativeNode self RClosed
  -> Option (PermanentNode self)
  = lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      switch parent
      case TentativeMid {tentativeData = (InfixT {input = InfixI {rightAllow = s}} | PrefixT {input = PrefixI {rightAllow = s}})} then
        if breakableInAllowSet (_opIdP node) s then Some node else None ()
      case TentativeRoot _ then
        if _isTopAllowedP node then Some node else None ()
      end
    else never

let _addRightChildren
  : State self rstyle
  -> TentativeNode self ROpen
  -> [PermanentNode self] -- NonEmpty
  -> TentativeNode self RClosed
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
  : State self rstyle2
  -> BreakableInput LOpen rstyle
  -> self LOpen rstyle
  -> [PermanentNode self] -- NonEmpty
  -> [TentativeNode self ROpen] -- NonEmpty
  -> TentativeNode self rstyle
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
  -> PermanentNode self
  -> TentativeNode self ROpen
  -> Option (TentativeNode self ROpen)
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
  -> PermanentNode self
  -> [TentativeNode self ROpen] -- NonEmpty
  -> Option (NonEmpty (TentativeNode self ROpen))
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
  : BreakableInput LOpen rstyle
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
  : TentativeNode self ROpen
  -> BreakableInput LOpen rstyle
  -> Bool
  = lam l. lam r.
    (_getOpGroup r (_opIdT l)).mayGroupRight

let _mayGroupLeft
  : TentativeNode self ROpen
  -> BreakableInput LOpen rstyle
  -> Bool
  = lam l. lam r.
    (_getOpGroup r (_opIdT l)).mayGroupLeft

-- NOTE(vipa, 2021-02-15): This should be a private type, and/or replaced with some standard library type at a later point in time
type BreakableQueue self = [Ref [TentativeNode self ROpen]]
let _newQueueFromFrontier
  : [TentativeNode self rstyle]
  -> BreakableQueue self
  = lam frontier.
    (create
      (addi 1 (maxOrElse (lam. 0) subi (map _maxDistanceFromRoot frontier)))
      (lam. ref []))
let _addToQueue
  : TentativeNode self ROpen
  -> BreakableQueue self
  -> ()
  = lam node. lam queue.
    let dist = _maxDistanceFromRoot node in
    let target = get queue dist in
    modref target (snoc (deref target) node)
recursive let _popFromQueue
  : BreakableQueue
  -> Option (TentativeNode self ROpen)
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
  : BreakableInput LOpen rstyle
  -> self LOpen rstyle
  -> State self RClosed
  -> Option (State self rstyle)
  = lam input. lam self. lam st.
    let time = addi 1 (deref st.timestep) in
    modref st.timestep time;

    let makeNewParents
      : [TentativeNode self ROpen] -- NonEmpty
      -> TentativeNode self rstyle
      = lam parents.
        match parents with [p] ++ _ then
          let snd: (a, b) -> b = lam x. x.1 in
          let cs = deref (snd (deref (_addedNodesLeftChildren p))) in
          match cs with [_] ++ _ then
            _addLeftChildren st input self cs parents
          else error "Somehow thought that a node would be a new parent, but it had no added children"
        else never -- TODO(vipa, 2021-02-12): this isn't technically never by for the typesystem, since we're matching against a possibly empty list. However, the list will never be empty, by the comment about NonEmpty above
    in

    -- NOTE(vipa, 2021-11-04): We only ever add to the queue here, no popping.
    let handleLeaf
      : BreakableQueue self
      -> TentativeNode self RClosed
      -> Option [TentativeNode self ROpen] -- NonEmpty
      = lam queue. lam child.
        match _getParents child with Some parents then
          -- NOTE(vipa, 2021-11-30): `_shallowAllowedLeft` and
          -- `_shallowAllowedRight` do two things: they check if the
          -- child is allowed as a left or right child, respectively,
          -- and they extract the already created PermanentNode inside
          -- the TentativeNode. `shallowRight` is thus `Some` iff
          -- shallow restrictions allow grouping to the right, and
          -- correspondingly for `shallowLeft`.
          -- NOTE(vipa, 2021-11-30): This means that if both
          -- `shallowLeft` and `shallowRight` are `Some`, then
          -- `shallowLeft = shallowRight`.
          let shallowRight = _shallowAllowedLeft input child in
          let f = lam parent.
            let shallowLeft = _shallowAllowedRight parent child in
            let precLeft = _mayGroupLeft parent input in
            let precRight = _mayGroupRight parent input in
            let config = (shallowLeft, shallowRight, precLeft, precRight) in
            -- NOTE(vipa, 2021-11-30): Grouping to the left is done by
            -- telling the parent that it should have `child` as a
            -- right child and adding it (the parent) to the queue if
            -- it isn't there already. It will later be made into a
            -- new permanent node, once all its children have been
            -- processed.
            (match (parent, config) with (!TentativeRoot _, _) & ((_, (Some child, None _, _, _)) | (_, (Some child, _, true, _))) then
               match _addRightChildToParent time child parent with Some parent then
                 _addToQueue parent queue
               else ()
             else ());
            -- NOTE(vipa, 2021-11-30): Grouping to the right is done
            -- by returning `true` to `filter`
            match config with (None _, Some child, _, _) | (_, Some child, _, true) then
              true
            else false in
          let parentsThatAllowRight = filter f parents in
          -- NOTE(vipa, 2021-11-30): If `parents` is non-empty then
          -- `shallowRight` must be `Some` (since `f` would return
          -- `false` otherwise).
          match (shallowRight, parentsThatAllowRight) with (Some child, parents & [_] ++ _) then
            -- NOTE(vipa, 2021-11-30): We cannot create the new
            -- tentative node yet because there may be more sharing
            -- available: multiple parents may share multiple
            -- children, in which case we still want to only create
            -- *one* new tentative node that has all of the shared
            -- children as left children. Thus we tell the parents
            -- that this `child` should be a left-child of this new
            -- node, once it is created.
            _addLeftChildToParent time child parents
          else None ()
        else never
    in

    recursive let work
      : BreakableQueue self
      -> [[TentativeNode self ROpen]] -- The inner sequence is NonEmpty
      -> [[TentativeNode self ROpen]] -- The inner sequence is NonEmpty
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
    -- NOTE(vipa, 2021-11-04): This is a priority queue sorted on
    --   maxDistanceFromRoot (pop longest distance first). It's empty
    --   from the start (the frontier is only used to find the highest
    --   possible distance).
    let queue = _newQueueFromFrontier frontier in
    let newParents = mapOption (handleLeaf queue) frontier in
    let newParents = work queue newParents in
    match map makeNewParents newParents with frontier & ([_] ++ _) then
      Some {st with frontier = frontier}
    else
      None ()

let breakableAddPrefix
  : BreakableInput LClosed ROpen
  -> self LClosed ROpen
  -> State self ROpen
  -> State self ROpen
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
  : BreakableInput LOpen ROpen
  -> self LOpen ROpen
  -> State self RClosed
  -> Option (State self ROpen)
  = lam input. lam self. lam st.
    let res = _addLOpen input self st in
    modref st.nextIdx (addi 1 (deref st.nextIdx));
    res

let breakableAddPostfix
  : BreakableInput LOpen RClosed
  -> self LOpen RClosed
  -> State self RClosed
  -> Option (State self RClosed)
  = lam input. lam self. lam st.
    let res = _addLOpen input self st in
    modref st.nextIdx (addi 1 (deref st.nextIdx));
    res

let breakableAddAtom
  : BreakableInput LClosed RClosed
  -> self LClosed RClosed
  -> State self ROpen
  -> State self RClosed
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
  : State self RClosed
  -> Option [PermanentNode self] -- NonEmpty
  = lam st.
    let time = addi 1 (deref st.timestep) in
    modref st.timestep time;

    let handleLeaf
      : BreakableQueue self
      -> TentativeNode self RClosed
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
      : BreakableQueue self
      -> [PermanentNode self]
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

type Ambiguity pos tokish = {range: {first: pos, last: pos}, partialResolutions: [[tokish]]}

type Important
con Important : () -> Important
con Unimportant : () -> Important

-- Examine an SPPF, reporting all ambiguities present, if any. If the
-- resulting list is empty then no ambiguities were found, which
-- implies that `leftChildAlts` and `rightChildAlts` are singleton
-- lists throughout the entire SPPF.
let breakableReportAmbiguities
  : { toTok : all lstyle. all rstyle. Important -> self lstyle rstyle -> [tokish]
    , parens : BreakableInput LCLosed RClosed
    , leftPos : all rstyle. self LClosed rstyle -> pos
    , rightPos : all lstyle. self lstyle RClosed -> pos
    , lpar : tokish
    , rpar : tokish }
  -> [PermanentNode self] -- NonEmpty
  -> [Ambiguity pos tokish]
  = lam info. lam nodes.
    let parId = _opIdI info.parens in
    let isParenForbidden : AllowSet OpId -> Bool = lam allows. not (breakableInAllowSet parId allows) in
    -- NOTE(vipa, 2021-02-15): All alternatives for children at the
    -- same point in the tree have the exact same range in the input,
    -- i.e., they will have exactly the same input as first and last
    -- input, that's why we only look at one of the children, we don't
    -- need to look at the others
    -- OPT(vipa, 2022-02-14): We don't need to examine children in the
    -- middle, could have two recursive functions, one going right,
    -- and one going left.
    recursive let range
      : PermanentNode self
      -> {first: pos, last: pos}
      = lam node.
        match node with AtomP {self = self} then {first = info.leftPos self, last = info.rightPos self}
        else match node with InfixP {leftChildAlts = [l] ++ _, rightChildAlts = [r] ++ _} then
          { first = (range l).first
          , last = (range r).last
          }
        else match node with PrefixP {self = self, rightChildAlts = [r] ++ _} then
          { first = info.leftPos self
          , last = (range r).last
          }
        else match node with PostfixP {self = self, leftChildAlts = [l] ++ _} then
          { first = (range l).first
          , last = info.rightPos self
          }
        else never
    in

    type IdxSet = [Int] in
    let leftOf : Int -> IdxSet -> IdxSet = lam idx. lam set. filter (gti idx) set in
    let rightOf : Int -> IdxSet -> IdxSet = lam idx. lam set. filter (lti idx) set in
    let inIdxSet : Int -> IdxSet -> Bool = lam idx. lam set. any (eqi idx) set in
    let idxSetEmpty : IdxSet -> Bool = lam set. null set in

    let isImportant : PermanentNode self -> IdxSet -> Important = lam p. lam set.
      if inIdxSet (_opIdxP p) set then Important () else Unimportant () in
    let idxAndImportant : PermanentNode self -> IdxSet -> (IdxSet, Important, IdxSet) = lam p. lam set.
      let idx = _opIdxP p in
      (leftOf idx set, if inIdxSet idx set then Important () else Unimportant (), rightOf idx set) in

    recursive
      let flattenOne : IdxSet -> PermanentNode self -> [tokish] = lam important. lam node.
        let isImportant = isImportant node important in
        switch node
        case AtomP {self = self} then info.toTok isImportant self
        case InfixP p then
          join [flattenMany important p.leftChildAlts, info.toTok isImportant p.self, flattenMany important p.rightChildAlts]
        case PrefixP p then
          concat (info.toTok isImportant p.self) (flattenMany important p.rightChildAlts)
        case PostfixP p then
          concat (flattenMany important p.leftChildAlts) (info.toTok isImportant p.self)
        end
      let flattenMany : IdxSet -> [PermanentNode self] -> [tokish] = lam important. lam nodes. -- NonEmpty
        match nodes with [n] ++ _ then
          flattenOne important n
        else never
    in

    recursive
      let resolveTopOne : IdxSet -> PermanentNode self -> [[tokish]] =
        lam topIdxs. lam p.
          match idxAndImportant p topIdxs with (lIdxs, selfImportant, rIdxs) in
          let l = match _leftStuffP p with Some (children, allows)
            then resolveTopMany lIdxs (isParenForbidden allows) children
            else [[]] in
          let r = match _rightStuffP p with Some (children, allows)
            then resolveTopMany rIdxs (isParenForbidden allows) children
            else [[]] in
          let here = _callWithSelfP (info.toTok selfImportant) p in
          seqLiftA2 (lam l. lam r. join [l, here, r]) l r
      let resolveTopMany : [Int] -> Bool -> [PermanentNode self] -> [[tokish]] =
        lam topIdxs. lam parenForbidden. lam ps.
          match partition (_isBrokenEdge parenForbidden) ps with (broken, whole) in
          let broken = join (map (resolveTopOne topIdxs) broken) in
          let whole = if null whole then [] else
            let flattened = flattenMany topIdxs whole in
            if idxSetEmpty topIdxs then [flattened] else [snoc (cons info.lpar flattened) info.rpar]
          in
          concat broken whole
    in
    let ambiguities : Ref [Ambiguity pos tokish] = ref [] in

    recursive
      let workMany
        : Option (PermanentNode self)
        -> Bool
        -> [PermanentNode self] -- NonEmpty
        -> ()
        = lam brokenParent. lam parenForbidden. lam tops.
          match tops with [n] then
            workOne (if _isBrokenEdge parenForbidden n then Some brokenParent else None ()) n
          else match tops with [n] ++ _ then
            let x = match (any (_isBrokenEdge parenForbidden) tops, brokenParent)
              with (true, Some parent) then ([parent], range parent)
              else (tops, range n) in
            let tops = x.0 in
            let range = x.1 in

            -- TODO(vipa, 2021-11-12): Make sure to not report the
            -- same brokenParent multiple times, since that's possible
            -- with the current setup

            -- NOTE(vipa, 2021-11-12): Find all nodes that can be at
            -- the root, including nodes that are part of the same
            -- broken production
            let topIdxs = setOfSeq subi (join (map _brokenIdxesP tops)) in
            -- NOTE(vipa, 2021-11-12): Some nodes will be in the top
            -- broken production in some alternatives but not in
            -- others. If we cover these in those alternatives then we
            -- cut off some ambiguity, but not all. Ex: we have `I I x
            -- E x` with prefix `I` and infix `E`, and unbreaking must
            -- put `E` as a child of an `I`. One alternative is
            -- resolved as `I (I x) E x`. However, neither the inner
            -- `I` nor the `x` can be in the root, unbroken or not,
            -- yet we still need to cover it with parens. This is
            -- because another node (`E`) that *can* be in the root
            -- can also be unbroken into a production that contains
            -- both it and the inner `I`, namely in the other
            -- alternative: `I (I x E x)`. We must thus also find
            -- nodes that can be unbroken together with nodes that can
            -- be in the root.
            -- OPT(vipa, 2021-11-15): It should be sufficient to check
            -- children along the edges only, not all descendants.
            recursive let addChildMaybe = lam acc. lam c.
              let idxs = _brokenIdxesP c in
              let acc = if any (lam x. setMem x topIdxs) idxs
                then foldl (lam acc. lam x. setInsert x acc) acc idxs
                else acc in
              foldl addChildMaybe acc (_brokenChildrenP c)
            in
            let addChildrenMaybe = lam acc. lam top.
              foldl addChildMaybe acc (_brokenChildrenP top) in
            let mergeRootIdxs = foldl addChildrenMaybe (setEmpty subi) tops in

            -- OPT(vipa, 2021-10-11): This should probably be a set that supports
            -- member querying as well as `removeGreaterThan` and `removeLesserThan`
            let idxesToCover = setToSeq (setUnion mergeRootIdxs topIdxs) in

            let resolutions : [[tokish]] = resolveTopMany idxesToCover true tops in

            -- TODO(vipa, 2021-10-11): Compute valid elisons
            let err = {range = range, partialResolutions = resolutions} in
            modref ambiguities (cons err (deref ambiguities));
            ()
          else dprintLn tops; never
      let workOne
        : Option (PermanentNode self)
        -> PermanentNode self
        -> ()
        = lam brokenParent. lam node.
          (match _leftStuffP node with Some (children, allows)
            then workMany (optionOr brokenParent (Some node)) (isParenForbidden allows) children
            else ());
          (match _rightStuffP node with Some (children, allows)
            then workMany (optionOr brokenParent (Some node)) (isParenForbidden allows) children
            else ());
          ()
    in

    workMany (None ()) false nodes;
    deref ambiguities

let breakableConstructSimple
  : { constructAtom : self LClosed RClosed -> res
    , constructInfix : self LOpen ROpen -> res -> res -> res
    , constructPrefix : self LClosed ROpen -> res -> res
    , constructPostfix : self LOpen RClosed -> res -> res
    }
  -> [PermanentNode self] -- NonEmpty
  -> res
  = lam f. lam ns.
    recursive let work
      : PermanentNode self -> res
      = lam n.
        switch n
        case AtomP p then f.constructAtom p.self
        case InfixP (p & {leftChildAlts = [l] ++ _, rightChildAlts = [r] ++ _}) then
          f.constructInfix p.self (work l) (work r)
        case PrefixP (p & {rightChildAlts = [r] ++ _}) then
          f.constructPrefix p.self (work r)
        case PostfixP (p & {leftChildAlts = [l] ++ _}) then
          f.constructPostfix p.self (work l)
        end
    in match ns with [n] ++ _ then work n else error "NonEmpty"

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

type Self a b = {val : Int, pos : Int, str : String} in

type TestToken in
con TestAtom : { x : Self RClosed RClosed, input : BreakableInput RClosed RClosed } -> TestToken in
con TestPrefix : { x : Self RClosed ROpen, input : BreakableInput RClosed ROpen } -> TestToken in
con TestInfix : { x : Self ROpen ROpen, input : BreakableInput ROpen ROpen } -> TestToken in
con TestPostfix : { x : Self ROpen RClosed, input : BreakableInput ROpen RClosed } -> TestToken in

let selfToTok : Important -> Self a b -> [(Bool, String)] = lam important. lam x. [(match important with Important _ then true else false, x.str)] in

type ParseResult in
con PSuccess : Ast -> ParseResult in
con PFail : () -> ParseResult in
con PAmbiguities : [Ambiguity Self (Bool, String)] -> ParseResult in

let constructAtom
  : Self LClosed RClosed -> Ast
  = lam self. IntA {pos = self.pos, val = self.val} in
let constructInfix
  : Self LOpen ROpen -> Ast -> Ast -> Ast
  = lam self. lam l. lam r.
    switch self.str
    case "+" then PlusA {pos = self.pos, l = l, r = r}
    case "*" then TimesA {pos = self.pos, l = l, r = r}
    case "/" then DivideA {pos = self.pos, l = l, r = r}
    case "else" then ElseA {pos = self.pos, l = l, r = r}
    end in
let constructPrefix
  : Self LClosed ROpen -> Ast -> Ast
  = lam self. lam r.
    switch self.str
    case "-" then NegateA {pos = self.pos, r = r}
    case "if" then IfA {pos = self.pos, r = r}
    end in
let constructPostfix
  : Self LOpen RClosed -> Ast -> Ast
  = lam self. lam l.
    switch self.str
    case "?" then NonZeroA {pos = self.pos, l = l}
    end in

let testParse
  : (String -> BreakableInput LCLosed RClosed)
  -> [Int -> TestToken]
  -> ParseResult
  = lam atom. recursive
      let workROpen = lam pos. lam st. lam tokens.
        match tokens with [t] ++ tokens then
          let t = t pos in
          let pos = addi 1 pos in
          match t with TestAtom {x = self, input = input} then
            workRClosed pos (breakableAddAtom input self st) tokens
          else match t with TestPrefix {x = self, input = input} then
            workROpen pos (breakableAddPrefix input self st) tokens
          else PFail ()
        else PFail ()
      let workRClosed = lam pos. lam st. lam tokens.
        match tokens with [t] ++ tokens then
          let t = t pos in
          let pos = addi 1 pos in
          match t with TestInfix {x = self, input = input} then
            match breakableAddInfix input self st with Some st
            then workROpen pos st tokens
            else PFail ()
          else match t with TestPostfix {x = self, input = input} then
            match breakableAddPostfix input self st with Some st
            then workRClosed pos st tokens
            else PFail ()
          else PFail ()
        else match breakableFinalizeParse st with Some tops then
          let reportConfig =
            { toTok = selfToTok
            , parens = atom "par"
            , leftPos = lam s: Self LClosed rstyle. s.pos
            , rightPos = lam s: Self lstyle RClosed. s.pos
            , lpar = (true, "(")
            , rpar = (true, ")")
            } in
          let constructConfig =
            { constructAtom = constructAtom
            , constructInfix = constructInfix
            , constructPrefix = constructPrefix
            , constructPostfix = constructPostfix
            } in
          match breakableReportAmbiguities reportConfig tops with ambs & [_] ++ _ then
            PAmbiguities ambs
          else PSuccess (breakableConstructSimple constructConfig tops)
        else PFail ()
    in workROpen 0 (breakableInitState ())
in

-- TODO(vipa, 2022-02-14): Code generation doesn't see the need to
-- generate a function that compares (Bool, String), even though
-- they're used and known later in this file, thus this utest is here
-- to make the requirement explicit until the bug is fixed.
-- See: https://github.com/miking-lang/miking/issues/542
utest (true, "foo") with (true, "foo") in

let i : String -> (Bool, String) = lam x. (true, x) in
let u : String -> (Bool, String) = lam x. (false, x) in

let grammar =
  { productions =
    [ BreakableAtom {label = "int"}
    , BreakableAtom {label = "par"}
    , BreakableInfix
      { label = "plus"
      , leftAllow = allowAll
      , rightAllow = allowAll
      }
    , BreakableInfix
      { label = "times"
      , leftAllow = allowAll
      , rightAllow = allowAll
      }
    , BreakableInfix
      { label = "divide"
      , leftAllow = allowAll
      , rightAllow = allowAll
      }
    , BreakablePrefix
      { label = "negate"
      , rightAllow = allowAll
      }
    , BreakablePrefix
      { label = "if"
      , rightAllow = allowAll
      }
    , BreakableInfix
      { label = "else"
      , leftAllow = allowOnly ["if"]
      , rightAllow = allowAll
      }
    , BreakablePostfix
      { label = "nonZero"
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
  , topAllowed = allowAll
  }
in
let genned: BreakableGenGrammar a b c = breakableGenGrammar cmpString grammar in
let atom = lam label. mapFindExn label genned.atoms in
let prefix = lam label. mapFindExn label genned.prefixes in
let infix = lam label. mapFindExn label genned.infixes in
let postfix = lam label. mapFindExn label genned.postfixes in

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

let test = testParse atom in

utest test []
with PFail ()
in

utest test [_int 4]
with PSuccess (IntA {val = 4,pos = 0})
in

utest test [_int 4, _plus]
with PFail ()
in

utest test [_int 4, _plus, _int 7]
with PSuccess
  (PlusA
    { pos = 1
    , l = (IntA {val = 4,pos = 0})
    , r = (IntA {val = 7,pos = 2})
    })
in

utest test [_negate, _int 8]
with PSuccess
  (NegateA
    { pos = 0
    , r = (IntA {val = 8,pos = 1})
    })
in

utest test [_negate, _negate, _int 8]
with PSuccess
  (NegateA
    { pos = 0
    , r = (NegateA
      { pos = 1
      , r = (IntA {val = 8,pos = 2})
      })
    })
in

utest test [_int 9, _nonZero, _nonZero]
with PSuccess
  (NonZeroA
    { pos = 2
    , l = (NonZeroA
      { pos = 1
      , l = (IntA {val = 9,pos = 0})})
    })
in

utest test [_negate, _nonZero]
with PFail ()
in

utest test [_int 1, _plus, _int 2, _times, _int 3]
with PSuccess
  (PlusA
    { pos = 1
    , l = (IntA {val = 1,pos = 0})
    , r = (TimesA
      { pos = 3
      , l = (IntA {val = 2,pos = 2})
      , r = (IntA {val = 3,pos = 4})
      })
    })
in

utest test [_int 1, _times, _int 2, _plus, _int 3]
with PSuccess
  (PlusA
    { pos = 3
    , l = (TimesA
      { pos = 1
      , l = (IntA {val = 1,pos = 0})
      , r = (IntA {val = 2,pos = 2})
      })
    , r = (IntA {val = 3,pos = 4})
    })
in

utest test [_int 1, _times, _int 2, _divide, _int 3]
with PAmbiguities (
  [ { range =
      { first = 0
      , last = 4
      }
    , partialResolutions =
      [ [u"1", i"*", i"(", u"2", i"/", u"3", i")"]
      , [i"(", u"1", i"*", u"2", i")", i"/", u"3"]
      ]
    }
  ])
in

utest test [_int 1, _times, _int 2, _divide, _int 3, _plus, _int 4]
with PAmbiguities (
  [ { range =
      { first = 0
      , last = 4
      }
    , partialResolutions =
      [ [u"1",i"*",i"(",u"2",i"/",u"3",i")"]
      , [i"(",u"1",i"*",u"2",i")",i"/",u"3"]
      ]
    }
  ])
in

utest test [_int 0, _plus, _int 1, _times, _int 2, _divide, _int 3]
with PAmbiguities (
  [ { range =
      { first = 2
      , last = 6 }
    , partialResolutions =
      [ [u"1",i"*",i"(",u"2",i"/",u"3",i")"]
      , [i"(",u"1",i"*",u"2",i")",i"/",u"3"]
      ]
    }
  ])
in

-- TODO(vipa, 2021-02-15): When we compute elisons we can report two ambiguities here, the nested one is independent
utest test [_int 0, _plus, _int 1, _times, _int 2, _divide, _int 3, _plus, _int 4]
with PAmbiguities (
  [ { range =
      { first = 0
      , last = 8
      }
    , partialResolutions =
      [ [u"0",i"+",i"(",u"1",u"*",u"2",u"/",u"3",i"+",u"4",i")"]
      , [i"(",u"0",i"+",u"1",u"*",u"2",u"/",u"3",i")",i"+",u"4"]
      ]
    }
  ])
in

-- TODO(vipa, 2021-02-15): Do we want to specify the order of the returned ambiguities in some way?
utest test [_int 1, _times, _int 2, _divide, _int 3, _plus, _int 4, _divide, _int 5, _times, _int 6]
with PAmbiguities (
  [ { range =
      { first = 6
      , last = 10
      }
    , partialResolutions =
      [ [u"4",i"/",i"(",u"5",i"*",u"6",i")"]
      , [i"(",u"4",i"/",u"5",i")",i"*",u"6"]
      ]
    }
  , { range =
      { first = 0
      , last = 4
      }
    , partialResolutions =
      [ [u"1",i"*",i"(",u"2",i"/",u"3",i")"]
      , [i"(",u"1",i"*",u"2",i")",i"/",u"3"]
      ]
    }
  ])
in

utest test [_if, _int 1]
with PSuccess
  (IfA
    { pos = 0
    , r = (IntA {val = 1,pos = 1})
    })
in

utest test [_if, _int 1, _else, _int 2]
with PSuccess
  (ElseA
    { pos = 2
    , l = (IfA
      { pos = 0
      , r = (IntA {val = 1,pos = 1})
      })
    , r = (IntA {val = 2,pos = 3})
    })

in

utest test [_if, _int 1, _else, _int 2, _else, _int 3]
with PFail ()
in

utest test [_if, _if, _int 1, _else, _int 2]
with PAmbiguities (
  [ { range =
      { first = 0
      , last = 4
      }
    , partialResolutions =
      [ [i"if",i"(",i"if",u"1",i"else",u"2",i")"]
      , [i"if",i"(",i"if",u"1",i")",i"else",u"2"]
      ]
    }
  ])
in

utest test [_negate, _if, _int 1, _else, _int 2]
with PSuccess
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
    })
in

utest test [_if, _negate, _if, _int 1, _else, _int 2]
with PAmbiguities (
  [ { range =
      { first = 0
      , last = 5
      }
    , partialResolutions =
      [ [i"if",i"(",u"-",i"if",u"1",i"else",u"2",i")"]
      , [i"if",i"(",u"-",i"if",u"1",i")",i"else",u"2"]
      ]
    }
  ])
in

utest test [_int 1, _plus, _if, _negate, _if, _int 1, _else, _int 2]
with PAmbiguities (
  [ { range =
      { first = 2
      , last = 7
      }
    , partialResolutions =
      [ [i"if",i"(",u"-",i"if",u"1",i"else",u"2",i")"]
      , [i"if",i"(",u"-",i"if",u"1",i")",i"else",u"2"]
      ]
    }
  ])
in

utest test [_int 1, _times, _if, _int 7, _else, _int 12]
with PSuccess
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
    })
in

utest test [_int 7, _else, _int 12]
with PFail ()
in

utest test [_int 1, _plus, _plus, _int 2]
with PFail ()
in

utest test [_int 1, _plus, _nonZero]
with PFail ()
in

utest test [_int 1, _nonZero, _plus, _int 2]
with PSuccess
  (PlusA
    { pos = 2
    , l = (NonZeroA
      { pos = 1
      , l = (IntA {val = 1,pos = 0})
      })
    , r = (IntA {val = 2,pos = 3})
    })
in

let grammar =
  { productions =
    [ BreakableAtom {label = "int"}
    , BreakableAtom {label = "par"}
    , BreakableInfix
      { label = "plus"
      , leftAllow = allowAllBut ["else"]
      , rightAllow = allowAllBut ["else"]
      }
    , BreakableInfix
      { label = "times"
      , leftAllow = allowAllBut ["else"]
      , rightAllow = allowAllBut ["else"]
      }
    , BreakableInfix
      { label = "divide"
      , leftAllow = allowAllBut ["else"]
      , rightAllow = allowAllBut ["else"]
      }
    , BreakablePrefix
      { label = "negate"
      , rightAllow = allowAllBut ["else"]
      }
    , BreakablePrefix
      { label = "if"
      , rightAllow = allowAll
      }
    , BreakableInfix
      { label = "else"
      , leftAllow = allowAllBut ["else"]
      , rightAllow = allowAllBut ["else"]
      }
    , BreakablePostfix
      { label = "nonZero"
      , leftAllow = allowAllBut ["else"]
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
  , topAllowed = allowAllBut ["else"]
  }
in

let genned: BreakableGenGrammar a b c = breakableGenGrammar cmpString grammar in
let atom = lam label. mapFindExn label genned.atoms in
let prefix = lam label. mapFindExn label genned.prefixes in
let infix = lam label. mapFindExn label genned.infixes in
let postfix = lam label. mapFindExn label genned.postfixes in

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

let test = testParse atom in

utest test [_if, _int 1]
with PSuccess
  (IfA
    { pos = 0
    , r = (IntA {val = 1,pos = 1})
    })
in

utest test [_if, _int 1, _else, _int 2]
with PSuccess
  (IfA
    { pos = 0
    , r = (ElseA
      { pos = 2
      , l = (IntA {val = 1,pos = 1})
      , r = (IntA {val = 2,pos = 3})
      })
    })

in

utest test [_if, _int 1, _else, _int 2, _else, _int 3]
with PFail ()
in

utest test [_if, _if, _int 1, _else, _int 2]
with PAmbiguities (
  [ { range =
      { first = 0
      , last = 4
      }
    , partialResolutions =
      [ [i"if",i"(",i"if",u"1",i")",i"else",u"2"]
      , [i"if",i"(",i"if",u"1",i"else",u"2",i")"]
      ]
    }
  ])
in

utest test [_negate, _if, _int 1, _else, _int 2]
with PSuccess
  (NegateA
    { pos = 0
    , r = (IfA
      { pos = 1
      , r = (ElseA
        { pos = 3
        , l = (IntA {val = 1,pos = 2})
        , r = (IntA {val = 2,pos = 4})
        })
      })
    })
in

utest test [_if, _negate, _if, _int 1, _else, _int 2]
with PAmbiguities (
  [ { range =
      { first = 0
      , last = 5
      }
    , partialResolutions =
      [ [i"if",i"(",u"-",i"if",u"1",i")",i"else",u"2"]
      , [i"if",i"(",u"-",i"if",u"1",i"else",u"2",i")"]
      ]
    }
  ])
in

utest test [_int 1, _plus, _if, _negate, _if, _int 1, _else, _int 2]
with PAmbiguities (
  [ { range =
      { first = 2
      , last = 7
      }
    , partialResolutions =
      [ [i"if",i"(",u"-",i"if",u"1",i")",i"else",u"2"]
      , [i"if",i"(",u"-",i"if",u"1",i"else",u"2",i")"]
      ]
    }
  ])
in

utest test [_int 1, _times, _if, _int 7, _else, _int 12]
with PSuccess
  (TimesA
    { pos = 1
    , l = (IntA {val = 1,pos = 0})
    , r = (IfA
      { pos = 2
      , r = (ElseA
        { pos = 4
        , l = (IntA {val = 7,pos = 3})
        , r = (IntA {val = 12,pos = 5})
        })
      })
    })
in

utest test [_int 7, _else, _int 12]
with PFail ()
in

()
