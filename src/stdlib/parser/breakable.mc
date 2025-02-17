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

/-
NOTE(vipa, 2022-05-05): This file uses GADTs, even though the current
typechecker doesn't support them. The external API is largely
unaffected, the relevant types can be expressed properly, but the
internals need some uses of `unsafeCoerce`. The issue we're working
around is as follows:

type Foo a in
con FooInt : Int -> Foo Int in
con FooChar : Char -> Foo Char in
let f : all a. Foo a -> Foo a = lam foo.
  -- This branch ends up unifying `a` with `Int`
  match foo with FooInt i then FooInt i else
  -- This branch ends up unifying `a` with `Char`
  match foo with FooChar c then FooChar c else
  -- Both of the unifications "leak" out of the branches, but with
  -- GADTs they should "return" to being just `a` when we return
  -- from them.
  never in
f (FooInt 2)


The workaround we use changes the above to this:
type Foo a in
con FooInt : Int -> Foo Int in
con FooChar : Char -> Foo Char in
let f : all a. Foo a -> Foo a = lam foo.
  -- Create a function that forgets that we have a `Foo a`
  let unlink : all b. Foo a -> Foo b = unsafeCoerce in
  match unlink foo with FooInt i then
    -- Create a function that forgets that we know that we have a
    -- `Foo Int` and instead remembers that it's a `Foo a`.
    let return : Foo Int -> Foo a = unsafeCoerce in
    return (FooInt i)
  else match unlink foo with FooChar c then
    -- Create a function that forgets that we know that we have a
    -- `Foo Char` and instead remembers that it's a `Foo a`.
    let return : Foo Char -> Foo a = unsafeCoerce in
    return (FooChar c)
  else never in
f (FooInt 2)

The `unlink` and `return` functions are safe to use as long as they
follow precisely this pattern, otherwise they are decidedly unsafe.
-/

include "map.mc"
include "set.mc"
include "either.mc"
include "common.mc"
include "error.mc"

type AllowedDirection
con GNeither : () -> AllowedDirection
con GLeft : () -> AllowedDirection
con GRight : () -> AllowedDirection
con GEither : () -> AllowedDirection

let _includesLeft
  : AllowedDirection -> Bool
  = lam dir. match dir with GEither _ | GLeft _ then true else false
let _includesRight
  : AllowedDirection -> Bool
  = lam dir. match dir with GEither _ | GRight _ then true else false

-- Each node in the parsed SPPF has a unique ID via `gensym`.
type PermanentId = Symbol

-- This is the type that is used to describe an item to be added to the parse
type LOpen
type LClosed
type ROpen
type RClosed

type WrappedSelf
con WAtom : all self. self LClosed RClosed -> WrappedSelf
con WInfix : all self. self LOpen ROpen -> WrappedSelf
con WPrefix : all self. self LClosed ROpen -> WrappedSelf
con WPostfix : all self. self LOpen RClosed -> WrappedSelf

type LOpenSelf self rstyle
con LInfix : all self. self LOpen ROpen -> LOpenSelf self ROpen
con LPostfix : all self. self LOpen RClosed -> LOpenSelf self RClosed

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
con AtomP : all self.
  { id : PermanentId
  , idx : Int
  , self : self LClosed RClosed
  } -> PermanentNode self
con InfixP : all self.
  { id : PermanentId
  , idx : Int
  , self : self LOpen ROpen
  , leftChildAlts : [PermanentNode self] -- NonEmpty
  , rightChildAlts : [PermanentNode self] -- NonEmpty
  } -> PermanentNode self
con PrefixP : all self.
  { id : PermanentId
  , idx : Int
  , self : self LClosed ROpen
  , rightChildAlts : [PermanentNode self] -- NonEmpty
  } -> PermanentNode self
con PostfixP : all self.
  { id : PermanentId
  , idx : Int
  , self : self LOpen RClosed
  , leftChildAlts : [PermanentNode self] -- NonEmpty
  } -> PermanentNode self

-- This is the data carried by tentative nodes, nodes that don't yet
-- have all their children known
type TentativeData self
con InfixT : all self.
  { idx : Int
  , self : self LOpen ROpen
  , leftChildAlts : [PermanentNode self] -- NonEmpty
  } -> TentativeData self
con PrefixT : all self.
  { idx : Int
  , self : self LClosed ROpen
  } -> TentativeData self

type GroupingsAllowedFunc self = all lstyle. all rstyle.
  (self lstyle ROpen, self LOpen rstyle) -> AllowedDirection
type TopAllowedFunc self = all lstyle. all rstyle.
  self lstyle rstyle -> Bool
type LeftAllowedFunc self = all lstyle. all rstyle1. all rstyle2.
  {parent : self LOpen rstyle1, child : self lstyle rstyle2} -> Bool
type RightAllowedFunc self = all lstyle1. all lstyle2. all rstyle.
  {parent : self lstyle1 ROpen, child : self lstyle2 rstyle} -> Bool
type ParenAllowedFunc self = all lstyle. all rstyle.
  self lstyle rstyle -> AllowedDirection

type Config self =
  { topAllowed : TopAllowedFunc self
  , leftAllowed : LeftAllowedFunc self
  , rightAllowed : RightAllowedFunc self
  , parenAllowed : ParenAllowedFunc self
  , groupingsAllowed : GroupingsAllowedFunc self
  }

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
con TentativeLeaf : all self.
  { parents : [TentativeNode self ROpen] -- NonEmpty
  , node : PermanentNode self
  } -> TentativeNode self RClosed
con TentativeMid : all self.
  { addedNodesLeftChildren : Ref (TimeStep, Ref [PermanentNode self])
  , addedNodesRightChildren : Ref (TimeStep, [PermanentNode self])
  , parents : [TentativeNode self ROpen] -- NonEmpty
  , tentativeData : TentativeData self
  , maxDistanceFromRoot : Int
  } -> TentativeNode self ROpen
con TentativeRoot : all self.
  { addedNodesLeftChildren : Ref (TimeStep, Ref [PermanentNode self])
  , addedNodesRightChildren : Ref (TimeStep, [PermanentNode self])
  } -> TentativeNode self ROpen

-- The data we carry along while parsing
type State self rstyle =
  { timestep : Ref TimeStep
  , nextIdx : Ref Int
  , frontier : [TentativeNode self rstyle]
  }

let _firstTimeStep : TimeStep = 0
let _isBefore : TimeStep -> TimeStep -> Bool = lti
let _uniqueID : () -> PermanentId = gensym
let _getParents
  : all self. all rstyle. TentativeNode self rstyle
  -> Option [TentativeNode self ROpen] -- NonEmpty
  = lam n.
    let unlink : all r. TentativeNode self rstyle -> TentativeNode self r
      = unsafeCoerce in
    match unlink n with TentativeLeaf {parents = ps} then Some ps else
    match unlink n with TentativeMid {parents = ps} then Some ps else
    match unlink n with TentativeRoot _ then None () else
    never
let _opIdxP
  : all self. PermanentNode self
  -> Int
  = lam node.
    match node with AtomP {idx = idx} then idx else
    match node with InfixP {idx = idx} then idx else
    match node with PrefixP {idx = idx} then idx else
    match node with PostfixP {idx = idx} then idx else
    never
let _addedNodesLeftChildren
  : all self. TentativeNode self ROpen
  -> Ref (TimeStep, Ref [PermanentNode self]) -- NonEmpty
  = lam node.
    match node with TentativeRoot{addedNodesLeftChildren = x} | TentativeMid{addedNodesLeftChildren = x}
    then x
    else never
let _addedNodesRightChildren
  : all self. TentativeNode self ROpen
  -> Ref (TimeStep, [PermanentNode self]) -- NonEmpty
  = lam node.
    match node with TentativeRoot{addedNodesRightChildren = x} | TentativeMid{addedNodesRightChildren = x}
    then x
    else never
let _callWithSelfP
  : all self. all x. (all lstyle. all rstyle. self lstyle rstyle -> x)
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
  : all self. TopAllowedFunc self
  -> Bool
  -> PermanentNode self
  -> Bool
  = lam isTopAllowed. lam parenAllowed. lam node.
    or (not parenAllowed) (not (_callWithSelfP #frozen"isTopAllowed" node))
let _leftChildrenP
  : all self. PermanentNode self -> Option [PermanentNode self] = lam p.
  switch p
  case InfixP r then
    Some r.leftChildAlts
  case PostfixP r then
    Some r.leftChildAlts
  case _ then None ()
  end
let _rightChildrenP
  : all self. PermanentNode self -> Option [PermanentNode self] = lam p.
  switch p
  case InfixP r then
    Some r.rightChildAlts
  case PrefixP r then
    Some r.rightChildAlts
  case _ then None ()
  end

let _brokenIdxesP
  : all self. TopAllowedFunc self
  -> ParenAllowedFunc self
  -> PermanentNode self
  -> [Int]
  = lam isTopAllowed. lam parenAllowedDirs.
    recursive let work = lam parenAllowed. lam p.
      if _isBrokenEdge #frozen"isTopAllowed" #frozen"parenAllowed" p then
        let parAllowed = _callWithSelfP #frozen"parenAllowedDirs" p in
        let l = match _leftChildrenP p with Some children
          then join (map (work (_includesLeft parAllowed)) children)
          else [] in
        let r = match _rightChildrenP p with Some children
          then join (map (work (_includesRight parAllowed)) children)
          else [] in
        join [l, [_opIdxP p], r]
      else []
    in work false
let _brokenChildrenP
  : all self. TopAllowedFunc self
  -> ParenAllowedFunc self
  -> PermanentNode self
  -> [PermanentNode self]
  = lam isTopAllowed. lam parenAllowedDirs.
    recursive let work = lam parenAllowed. lam p.
      if _isBrokenEdge #frozen"isTopAllowed" parenAllowed p then
        let parAllowed = _callWithSelfP #frozen"parenAllowedDirs" p in
        let l = match _leftChildrenP p with Some children
          then join (map (work (_includesLeft parAllowed)) children)
          else [] in
        let r = match _rightChildrenP p with Some children
          then join (map (work (_includesRight parAllowed)) children)
          else [] in
        concat l r
      else [p]
    in work false

let breakableInitState : all self. () -> State self ROpen
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
  : all self. all rstyle.
  TentativeNode self rstyle
  -> Int
  = lam n.
    let unlink : all r. TentativeNode self rstyle -> TentativeNode self r
      = unsafeCoerce in
    match unlink n with TentativeMid {maxDistanceFromRoot = r} then r else
    match unlink n with TentativeRoot _ then 0 else
    match unlink n with  TentativeLeaf {parents = ps} then
      maxOrElse (lam. 0) subi (map _maxDistanceFromRoot ps)
    else never
end

let _shallowAllowedLeft
  : all self. all rstyle.
  LeftAllowedFunc self
  -> LOpenSelf self rstyle
  -> TentativeNode self RClosed
  -> Option (PermanentNode self)
  = lam allowedLeft. lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      let helper = lam self.
        let unlink : all r. LOpenSelf self rstyle -> LOpenSelf self r = unsafeCoerce in
        match unlink parent with LInfix parent then allowedLeft {parent = parent, child = self} else
        match unlink parent with LPostfix parent then allowedLeft {parent = parent, child = self} else
        never in
      if _callWithSelfP #frozen"helper" node
      then Some node
      else None ()
    else never

let _shallowAllowedRight
  : all self. TopAllowedFunc self
  -> RightAllowedFunc self
  -> TentativeNode self ROpen
  -> TentativeNode self RClosed
  -> Option (PermanentNode self)
  = lam topAllowed. lam rightAllowed. lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      switch parent
      case TentativeMid {tentativeData = InfixT {self = parent}} then
        let f = lam child. rightAllowed {parent = parent, child = child} in
        if _callWithSelfP #frozen"f" node
        then Some node
        else None ()
      case TentativeMid {tentativeData = PrefixT {self = parent}} then
        let f = lam child. rightAllowed {parent = parent, child = child} in
        if _callWithSelfP #frozen"f" node
        then Some node
        else None ()
      case TentativeRoot _ then
        if _callWithSelfP #frozen"topAllowed" node then Some node else None ()
      end
    else never

let _addRightChildren
  : all self. all rstyle. State self rstyle
  -> TentativeNode self ROpen
  -> [PermanentNode self] -- NonEmpty
  -> TentativeNode self RClosed
  = lam st. lam parent. lam children.
    match parent with TentativeMid {parents = parents, tentativeData = data} then
      let id = _uniqueID () in
      let node =
        match data with InfixT {idx = idx, self = self, leftChildAlts = l} then
          InfixP {id = id, idx = idx, self = self, leftChildAlts = l, rightChildAlts = children}
        else match data with PrefixT {idx = idx, self = self} then
          PrefixP {id = id, idx = idx, self = self, rightChildAlts = children}
        else never in
      TentativeLeaf {parents = parents, node = node}
    else match parent with TentativeRoot _ then
      error "Unexpectedly tried to add right children to the root"
    else never

let _addLeftChildren
  : all self. all rstyle. all rstyle2.
  State self rstyle2
  -> LOpenSelf self rstyle
  -> [PermanentNode self] -- NonEmpty
  -> [TentativeNode self ROpen] -- NonEmpty
  -> TentativeNode self rstyle
  = lam st. lam lself. lam leftChildren. lam parents.
    let idx = deref st.nextIdx in
    let unlink : all r. LOpenSelf self rstyle -> LOpenSelf self r = unsafeCoerce in
    match unlink lself with LInfix self then
      let return : TentativeNode self ROpen -> TentativeNode self rstyle = unsafeCoerce in
      let time = deref st.timestep in
      let addedLeft = ref (_firstTimeStep, ref []) in
      let addedRight = ref (_firstTimeStep, []) in
      let res = TentativeMid
        { parents = parents
        , addedNodesLeftChildren = addedLeft
        , addedNodesRightChildren = addedRight
        , maxDistanceFromRoot = addi 1 (maxOrElse (lam. 0) subi (map _maxDistanceFromRoot parents))
        , tentativeData = InfixT {idx = idx, self = self, leftChildAlts = leftChildren}
        } in
      return res
    else match unlink lself with LPostfix self then
      let return : TentativeNode self RClosed -> TentativeNode self rstyle = unsafeCoerce in
      let id = _uniqueID () in
      let res = TentativeLeaf
        { parents = parents
        , node = PostfixP {id = id, idx = idx, self = self, leftChildAlts = leftChildren}
        } in
      return res
    else never

let _addRightChildToParent
  : all self. TimeStep
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
  : all self. TimeStep
  -> PermanentNode self
  -> [TentativeNode self ROpen] -- NonEmpty
  -> Option [TentativeNode self ROpen] -- NonEmpty
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

let _getAllowedGroupings
  : all self. all rstyle.
  GroupingsAllowedFunc self
  -> TentativeNode self ROpen
  -> LOpenSelf self rstyle
  -> (Bool, Bool)
  = lam groupings. lam l. lam r.
    switch l
    case TentativeRoot _ then (false, true)
    case TentativeMid l then
      let dirs =
        let unlink : all r. LOpenSelf self rstyle -> LOpenSelf self r = unsafeCoerce in
        match (l.tentativeData, unlink r) with (InfixT l, LInfix r) then groupings (l.self, r) else
        match (l.tentativeData, unlink r) with (PrefixT l, LInfix r) then groupings (l.self, r) else
        match (l.tentativeData, unlink r) with (InfixT l, LPostfix r) then groupings (l.self, r) else
        match (l.tentativeData, unlink r) with (PrefixT l, LPostfix r) then groupings (l.self, r) else
        never
      in (_includesLeft dirs, _includesRight dirs)
    end

-- NOTE(vipa, 2021-02-15): This should be a private type, and/or replaced with some standard library type at a later point in time
type BreakableQueue self = Ref (Map Int [TentativeNode self ROpen])
let _newQueue
  : all self. () -> BreakableQueue self
  = lam. ref (mapEmpty (lam x. lam y. subi y x))
let _addToQueue
  : all self. TentativeNode self ROpen
  -> BreakableQueue self
  -> ()
  = lam node. lam queue.
    modref queue (mapInsertWith concat (_maxDistanceFromRoot node) [node] (deref queue))
let _popFromQueue
  : all self. BreakableQueue self
  -> Option (TentativeNode self ROpen)
  = lam queue.
    match mapGetMin (deref queue) with Some (k, [v] ++ vs) then
      let newQueue = match vs with []
                     then mapRemove k (deref queue)
                     else mapInsert k vs (deref queue)
      in
      modref queue newQueue; Some v
    else None ()

let _addLOpen
  : all self. all rstyle. Config self
  -> LOpenSelf self rstyle
  -> State self RClosed
  -> Option (State self rstyle)
  = lam config. lam lself. lam st.
    let nodesToProcess = _newQueue () in
    let time = addi 1 (deref st.timestep) in
    modref st.timestep time;

    let makeNewParents
      : [TentativeNode self ROpen] -- NonEmpty
      -> TentativeNode self rstyle
      = lam parents.
        match parents with [p] ++ _ then
          let snd: all a. all b. (a, b) -> b = lam x. x.1 in
          let cs = deref (snd (deref (_addedNodesLeftChildren p))) in
          match cs with [_] ++ _ then
            _addLeftChildren st lself cs parents
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
          let lallowed : LeftAllowedFunc self = config.leftAllowed in
          let rallowed : RightAllowedFunc self = config.rightAllowed in
          let tallowed : TopAllowedFunc self = config.topAllowed in
          let gallowed : GroupingsAllowedFunc self = config.groupingsAllowed in
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
          let shallowRight = _shallowAllowedLeft #frozen"lallowed" lself child in
          let f = lam parent.
            let shallowLeft = _shallowAllowedRight #frozen"tallowed" #frozen"rallowed" parent child in
            match _getAllowedGroupings #frozen"gallowed" parent lself with (precLeft, precRight) in
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
    let newParents = mapOption (handleLeaf nodesToProcess) frontier in
    let newParents = work nodesToProcess newParents in
    match map makeNewParents newParents with frontier & ([_] ++ _) then
      -- NOTE(vipa, 2022-05-05): The typechecker currently requires
      -- that {x with foo = ...} does not change the type of `foo`,
      -- which this code needs to do (the type of `frontier` changes),
      -- thus we reconstruct the entire record for the moment.
      Some {timestep = st.timestep, nextIdx = st.nextIdx, frontier = frontier}
    else
      None ()

let breakableAddPrefix
  : all self. Config self
  -> self LClosed ROpen
  -> State self ROpen
  -> State self ROpen
  = lam config. lam self. lam st.
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
        , tentativeData = PrefixT {idx = idx, self = self}
        }
      ]
    }

let breakableAddInfix
  : all self. Config self
  -> self LOpen ROpen
  -> State self RClosed
  -> Option (State self ROpen)
  = lam config. lam self. lam st.
    let res = _addLOpen config (LInfix self) st in
    modref st.nextIdx (addi 1 (deref st.nextIdx));
    res

let breakableAddPostfix
  : all self. Config self
  -> self LOpen RClosed
  -> State self RClosed
  -> Option (State self RClosed)
  = lam config. lam self. lam st.
    let res = _addLOpen config (LPostfix self) st in
    modref st.nextIdx (addi 1 (deref st.nextIdx));
    res

let breakableAddAtom
  : all self. Config self
  -> self LClosed RClosed
  -> State self ROpen
  -> State self RClosed
  = lam config. lam self. lam st.
    let idx = deref st.nextIdx in
    modref st.nextIdx (addi 1 idx);
    let id = _uniqueID () in
    -- NOTE(vipa, 2022-05-05): The typechecker currently requires that
    -- {x with foo = ...} does not change the type of `foo`, which
    -- this code needs to do (the type of `frontier` changes), thus we
    -- reconstruct the entire record for the moment.
    { timestep = st.timestep
    , nextIdx = st.nextIdx
    , frontier =
      [ TentativeLeaf
        { parents = st.frontier
        , node = AtomP {id = id, idx = idx, self = self}
        }
      ]
    }

-- TODO(vipa, 2021-02-15): There should be more information in case of
-- a parse failure, but it's not obvious precisely how the information
-- should be presented, it's not obvious to me that there will always
-- be a single cause of the failure that is easy to find
-- algorithmically
let breakableFinalizeParse
  : all self. Config self
  -> State self RClosed
  -> Option [PermanentNode self] -- NonEmpty
  = lam config. lam st.
    let nodesToProcess = _newQueue () in
    let time = addi 1 (deref st.timestep) in
    modref st.timestep time;
    let rallowed : RightAllowedFunc self = config.rightAllowed in
    let tallowed : TopAllowedFunc self = config.topAllowed in

    let handleLeaf
      : BreakableQueue self
      -> TentativeNode self RClosed
      -> ()
      = lam queue. lam child.
        match _getParents child with Some parents then
          for_ parents
            (lam parent.
              match _shallowAllowedRight #frozen"tallowed" #frozen"rallowed" parent child with Some child then
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
          let snd: all a. all b. (a, b) -> b = lam x. x.1 in
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
    iter (handleLeaf nodesToProcess) frontier;
    match work nodesToProcess with res & [_] ++ _ then Some res else None ()

type Ambiguity pos tokish = {range: {first: pos, last: pos}, partialResolutions: [[tokish]]}

type Important
con Important : () -> Important
con Unimportant : () -> Important

-- Examine an SPPF, reporting all ambiguities present, if any. If the
-- resulting list is empty then no ambiguities were found, which
-- implies that `leftChildAlts` and `rightChildAlts` are singleton
-- lists throughout the entire SPPF.
let breakableReportAmbiguities
  : all self. all pos. all tokish.
    { parenAllowed : ParenAllowedFunc self
    , topAllowed : TopAllowedFunc self
    , toTok : all lstyle. all rstyle. Important -> self lstyle rstyle -> [tokish]
    , leftPos : all rstyle. self LClosed rstyle -> pos
    , rightPos : all lstyle. self lstyle RClosed -> pos
    , lpar : tokish
    , rpar : tokish }
  -> [PermanentNode self] -- NonEmpty
  -> [Ambiguity pos tokish]
  = lam info. lam nodes.
    let pallowed : ParenAllowedFunc self = info.parenAllowed in
    let tallowed : TopAllowedFunc self = info.topAllowed in
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
        switch node
        case AtomP {self = self} then {first = info.leftPos self, last = info.rightPos self}
        case InfixP {leftChildAlts = [l] ++ _, rightChildAlts = [r] ++ _} then
          { first = (range l).first
          , last = (range r).last
          }
        case PrefixP {self = self, rightChildAlts = [r] ++ _} then
          { first = info.leftPos self
          , last = (range r).last
          }
        case PostfixP {self = self, leftChildAlts = [l] ++ _} then
          { first = (range l).first
          , last = info.rightPos self
          }
        end
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
          let parAllowed = _callWithSelfP #frozen"pallowed" p in
          let l = match _leftChildrenP p with Some children
            then resolveTopMany lIdxs (_includesLeft parAllowed) children
            else [[]] in
          let r = match _rightChildrenP p with Some children
            then resolveTopMany rIdxs (_includesRight parAllowed) children
            else [[]] in
          let f = lam x. info.toTok selfImportant x in
          let here = _callWithSelfP #frozen"f" p in
          seqLiftA2 (lam l. lam r. join [l, here, r]) l r
      let resolveTopMany : [Int] -> Bool -> [PermanentNode self] -> [[tokish]] =
        lam topIdxs. lam parenAllowed. lam ps.
          match partition (_isBrokenEdge #frozen"tallowed" parenAllowed) ps with (broken, whole) in
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
        = lam brokenParent. lam parenAllowed. lam tops.
          match tops with [n] then
            workOne (if _isBrokenEdge #frozen"tallowed" parenAllowed n then brokenParent else None ()) n
          else match tops with [n] ++ _ then
            let x = match (any (_isBrokenEdge #frozen"tallowed" parenAllowed) tops, brokenParent)
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
            let topIdxs = setOfSeq subi (join (map (_brokenIdxesP #frozen"tallowed" #frozen"pallowed") tops)) in
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
              let idxs = _brokenIdxesP #frozen"tallowed" #frozen"pallowed" c in
              let acc = if any (lam x. setMem x topIdxs) idxs
                then foldl (lam acc. lam x. setInsert x acc) acc idxs
                else acc in
              foldl addChildMaybe acc (_brokenChildrenP #frozen"tallowed" #frozen"pallowed" c)
            in
            let addChildrenMaybe = lam acc. lam top.
              foldl addChildMaybe acc (_brokenChildrenP #frozen"tallowed" #frozen"pallowed" top) in
            let mergeRootIdxs = foldl addChildrenMaybe (setEmpty subi) tops in

            -- OPT(vipa, 2021-10-11): This should probably be a set that supports
            -- member querying as well as `removeGreaterThan` and `removeLesserThan`
            let idxesToCover = setToSeq (setUnion mergeRootIdxs topIdxs) in

            let resolutions : [[tokish]] = resolveTopMany idxesToCover false tops in

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
          let parAllowed = _callWithSelfP #frozen"pallowed" node in
          (match _leftChildrenP node with Some children
            then workMany (optionOr brokenParent (Some node)) (_includesLeft parAllowed) children
            else ());
          (match _rightChildrenP node with Some children
            then workMany (optionOr brokenParent (Some node)) (_includesRight parAllowed) children
            else ());
          ()
    in

    workMany (None ()) false nodes;
    deref ambiguities

let breakableConstructSimple
  : all self. all res.
    { constructAtom : self LClosed RClosed -> res
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

type BreakableErrorHighlightConfig self =
  { parenAllowed : ParenAllowedFunc self
  , topAllowed : TopAllowedFunc self
  , terminalInfos : all lstyle. all rstyle. self lstyle rstyle -> [Info]
  , getInfo : all lstyle. all rstyle. self lstyle rstyle -> Info
  , lpar : String
  , rpar : String
  }

let breakableToErrorHighlightSpec
  : all self. BreakableErrorHighlightConfig self
  -> [PermanentNode self] -- NonEmpty
  -> [{info: Info, partialResolutions: [[Highlight]]}]
  = lam config. lam tops.
    let pallowed : ParenAllowedFunc self = config.parenAllowed in
    let tallowed : TopAllowedFunc self = config.topAllowed in
    let linfo : all rstyle. self LClosed rstyle -> Info = config.getInfo in
    let rinfo : all lstyle. self lstyle RClosed -> Info = config.getInfo in
    let totok : all lstyle. all rstyle. Important -> self lstyle rstyle -> [Highlight] = lam imp. lam self.
      match imp with Important _ then
        map (lam info. Relevant info) (config.terminalInfos self)
      else [Irrelevant (config.getInfo self)] in
    let reportConfig =
      { parenAllowed = #frozen"pallowed"
      , topAllowed = #frozen"tallowed"
      , toTok = #frozen"totok"
      , leftPos = #frozen"linfo"
      , rightPos = #frozen"rinfo"
      , lpar = Added {content = config.lpar, ensureSurroundedBySpaces = true}
      , rpar = Added {content = config.rpar, ensureSurroundedBySpaces = true}
      } in
    let res = breakableReportAmbiguities reportConfig tops in
    let fixup = lam amb: Ambiguity Info Highlight.
      let amb: Ambiguity Info Highlight = amb in
      {info = mergeInfo amb.range.first amb.range.last, partialResolutions = amb.partialResolutions}
    in map fixup res

let breakableDefaultHighlight
  : all self. BreakableErrorHighlightConfig self
  -> String
  -> [PermanentNode self]
  -> [(Info, String)]
  = lam config. lam content. lam tops.
    let highlightOne = lam amb: {info: Info, partialResolutions: [[Highlight]]}.
      let alternatives = map (formatHighlights terminalHighlightAddedConfig content) amb.partialResolutions in
      let body =
        if match amb.info with Info x then eqi x.row1 x.row2 else false then
          strJoin "\n" (map (concat "  ") alternatives)
        else
          strJoin "\n\n" (mapi (lam i. lam str. join ["Alternative ", int2string (addi i 1), ":\n", str]) alternatives)
      in (amb.info, join ["Ambiguity error\n", body, "\n"])
    in map highlightOne (breakableToErrorHighlightSpec config tops)
