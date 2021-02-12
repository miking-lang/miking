-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "map.mc"

type AllowSet id
con AllowSet : Map id () -> AllowSet id
con DisallowSet : Map id () -> AllowSet id

type BreakableProduction prodLabel self res
con BreakableAtom :
  { label : prodLabel
  , construct : self -> res
  } -> BreakableProduction prodLabel self res
con BreakableInfix :
  { label : prodLabel
  , construct : self -> res -> res -> res
  , leftAllow : AllowSet prodLabel
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel self res
con BreakablePrefix :
  { label : prodLabel
  , construct : self -> res -> res
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel self res
con BreakablePostfix :
  { label : prodLabel
  , construct : self -> res -> res
  , leftAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel self res

type OpGrouping = {mayGroupLeft : Bool, mayGroupRight : Bool}

type BreakableGrammar prodLabel self res =
  { productions : [BreakableProduction prodLabel self res]
  , precedences : [((prodLabel, prodLabel), OpGrouping)]
  }

-- Each operator is uniquely identifiable by its ID, which is used to
-- look up precedence and the like
type OpId = Int

-- Each node in the parsed SPPF has a unique ID (it will likely not be
-- unique when comparing between two different SPPFs though).
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
  , input : BreakableInput res self LClosed RClosed
  , self : self
  } -> PermanentNode res self
con InfixP :
  { id : PermanentId
  , input : BreakableInput res self LOpen ROpen
  , self : self
  , leftChildAlts : [PermanentNode res self] -- NonEmpty
  , rightChildAlts : [PermanentNode res self] -- NonEmpty
  } -> PermanentNode res self
con PrefixP :
  { id : PermanentId
  , input : BreakableInput res self LClosed ROpen
  , self : self
  , rightChildAlts : [PermanentNode res self] -- NonEmpty
  } -> PermanentNode res self
con PostfixP :
  { id : PermanentId
  , input : BreakableInput res self LOpen RClosed
  , self : self
  , leftChildAlts : [PermanentNode res self] -- NonEmpty
  } -> PermanentNode res self

-- This is the data carried by tentative nodes, nodes that don't yet
-- have all their children known
type TentativeData res self
con InfixT :
  { input : BreakableInput res self LOpen ROpen
  , self : self
  , leftChildAlts : [PermanentNode res self] -- NonEmpty
  } -> TentativeData res self
con PrefixT :
  { input : BreakableInput res self LClose ROpen
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
  { nextId : Ref Int
  , timestep : Ref Int
  , frontier : [TentativeNode res self rstyle]
  }

let _firstTimeStep : TimeStep = 0
let _isBefore : TimeStep -> TimeStep -> Bool = lti
let _eqOpId : OpId -> OpId -> Bool = eqi
let _rootID : OpId = negi 1
let _firstOpId : OpId = 0
let _uniqueID : () -> PermanentId = gensym
let _getParents
  : TentativeNode res self rstyle
  -> Option [TentativeNode res self ROpen] -- NonEmpty
  = lam n.
    match n with TentativeLeaf{parents = ps} | TentativeMid{parents = ps} then Some ps else
    match n with TentativeRoot _ then None () else
    never
let _opIdP
  : PermanentNode res self
  -> OpId
  = lam node.
    match node with AtomP {id = id} then id else
    match node with InfixP {id = id} then id else
    match node with PrefixP {id = id} then id else
    match node with PostfixP {id = id} then id else
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
    match node with TentativeMid{tentativeData = data} then _opIdTD else
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
-- NOTE(vipa, 2021-02-08): This should possibly be in the stdlib, but it might depend on opinions on side effects down the line
recursive let _iter = lam f. lam xs.
  match xs with [x] ++ xs then
    let _ = f x in _iter f xs
  else match xs with [] then
    ()
  else never
end
let _for = lam xs. lam f. _iter f xs


let breakableGenGrammar
  : (prodLabel -> prodLabel -> Int)
  -> BreakableGrammar prodLabel self res
  -> BreakableGenGrammar prodLabel self res
  = lam cmp. lam grammar. never

let breakableInitState : () -> State res self ROpen
  = lam cmp. lam grammar.
    let nextId = ref _firstOpId in
    let timestep = ref _firstTimeStep in
    let addedLeft = ref (_firstTimeStep, ref []) in
    let addedRight = ref (_firstTimeStep, []) in
    { nextId = nextId
    , timestep = timestep
    , frontier =
      [ TentativeRoot { addedNodesLeftChildren = addedLeft, addedNodesRightChildren = addedRight } ]
    }

let inAllowSet
  : id
  -> AllowSet id
  -> Bool
  = lam id. lam set.
    match set with AllowSet s then mapMem id s else
    match set with DisallowSet s then not (mapMem id s) else
    never

recursive let _maxDistanceFromRoot
  : TentativeNode res self rstyle
  -> Int
  = lam n.
    match n with TentativeMid {maxDistanceFromRoot = r} then r else
    match n with TentativeRoot _ then 0 else
    match n with TentativeLeaf {parents = parents} then maxOrElse (lam _. 0) subi (map _maxDistanceFromRoot parents) else
    never
end

let _shallowAllowedLeft
  : BreakableInput res self LOpen rstyle
  -> TentativeNode res self RClosed
  -> Option (PermanentNode res self)
  = lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      match parent with InfixI {leftAllow = s} | PostfixI {leftAllow = s} then
        if inAllowSet (_opIdP node) s then Some node else None ()
      else never
    else never

let _shallowAllowedRight
  : TentativeNode s res self ROpen
  -> TentativeNode res self RClosed
  -> Option (PermanentNode res self)
  = lam parent. lam child.
    match child with TentativeLeaf {node = node} then
      match parent with TentativeRoot _ then Some node else
      match parent with TentativeMid {tentativeData = (InfixT {rightAllowed = s} | PrefixT {rightAllowed = s})} then
        if inAllowSet (_opIdP node) s then Some node else None ()
      else never
    else never

let _addRightChildren
  : State res self rstyle
  -> TentativeNode res self ROpen
  -> [PermanentNode res self] -- NonEmpty
  -> TentativeNode s res self RClosed
  = lam st. lam parent. lam children.
    match parent with TentativeMid {parents = parents, tentativeData = data} then
      let id = _uniqueID st in
      let node =
        match data with InfixT {input = input, self = self, leftChildAlts = l} then
          InfixP {id = id, input = input, self = self, leftChildAlts = l, rightChildAlts = children}
        else match data with PrefixT {input = input, self = self} then
          PrefixP {id = id, input = input, self = self, rightChildAlts = children}
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
    match input with InfixI _ then
      let time = deref st.timestep in
      let addedLeft = ref (_firstTimeStep, ref []) in
      let addedRight = ref (_firstTimeStep, []) in
      TentativeMid
        { parents = parents
        , addedNodesLeftChildren = addedLeft
        , addedNodesRightChildren = addedRight
        , maxDistanceFromRoot = addi 1 (maxOrElse (lam _. 0) subi (map _maxDistanceFromRoot parents))
        , tentativeData = InfixT {input = input, self = self, leftChildAlts = leftChildren}
        }
    else match input with PostfixI _ then
      let id = _uniqueID st in
      TentativeLeaf
        { parents = parents
        , node = PostfixP {id = id, input = input, self = self, leftChildAlts = leftChildren}
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
        let _ = modref target (time, [child]) in
        Some parent
      else
        let _ = modref target (time, cons child prev) in
        None ()
    else never

let _addLeftChildToParent
  : TimeStep
  -> PermanentNode res self
  -> [TentativeNode s res self ROpen] -- NonEmpty
  -> Option (NonEmpty (TentativeNode res self ROpen))
  = lam time. lam child. lam parents.
    match parents with [p] ++ _ then
      let target = _addedNodesLeftChildren p in
      match deref target with (lastUpdate, prev) then
        if _isBefore lastUpdate time then
          let leftChildrenHere = ref [child] in
          let _ = _iter (lam p. modref (_addedNodesLeftChildren p) (time, leftChildrenHere)) parents in
          Some parents
        else
          let _ = modref target (time, cons child prev) in
          None ()
      else never
    else never -- TODO(vipa, 2021-02-12): this isn't technically never by for the typesystem, since we're matching against a possibly empty list. However, the list will never be empty, by the comment about NonEmpty above

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
    let _ = modref st.timestep time in

    type BreakableQueue = [Ref [TentativeNode res self ROpen]] in
    let addToQueue
      : TentativeNode res self ROpen
      -> BreakableQueue
      -> ()
      = lam node. lam queue.
        let dist = _maxDistanceFromRoot node in
        let target = get dist queue in
        modref target (snoc (deref target) node)
    in
    recursive let popFromQueue
      : BreakableQueue
      -> Option (TentativeNode res self ROpen)
      = lam queue.
        match queue with queue ++ [target] then
          let nodes = deref target in
          match nodes with [node] ++ nodes then
            let _ = modref target nodes in
            Some node
          else popFromQueue queue
        else None ()
    in

    let makeNewParents
      : [TentativeNode res self ROpen] -- NonEmpty
      -> TentativeNode res self rstyle
      = lam parents.
        match parents with [p] ++ _ then
          let cs = deref (deref (_addedNodesLeftChildren p)).1 in
          match cs with [_] ++ _ then
            _addLeftChildren st input self cs parents
          else error "Somehow thought that a node would be a new parent, but it had no added children"
        else never -- TODO(vipa, 2021-02-12): this isn't technically never by for the typesystem, since we're matching against a possibly empty list. However, the list will never be empty, by the comment about NonEmpty above
    in

    let handleLeaf
      : TentativeNode res self RClosed
      -> BreakableQueue
      -> (MaxPQueue Int (TentativeNode res self ROpen), Option [TentativeNode res self ROpen]) -- NonEmpty
      = lam child. lam queue.
        let parents = _getParents child in
        let _ = _for parents
          (lam parent.
            if not (_mayGroupLeft parent input) then () else
            match _shallowAllowedRight parent child with Some child then
              match _addRightChildToParent time child parent with Some parent then
                addToQueue parent queue
              else ()
            else ()) in
        match (_shallowAllowedLeft input child, filter (lam l. _mayGroupRight l input) parents)
        with (Some child, parents & [_] ++ _) then
          _addLeftChildToParent time child parents
        else None ()
    in

    recursive let work
      : BreakableQueue
      -> [[TentativeNode res self ROpen]] -- The inner sequence is NonEmpty
      -> [[TentativeNode res self ROpen]] -- The inner sequence is NonEmpty
      = lam queue. lam acc.
        match popFromQueue queue with Some (parent & TentativeMid{addedNodesRightChildren = addedRight}) then
          match deref addedRight with (_, children & [_] ++ _) then
            let acc = match handleLeaf (_addRightChildren st parent children) queue
              with Some n then cons n acc
              else acc in
            work queue acc
          else error "Somehow reached a parent without right children that was still added to the queue"
        else acc
    in

    -- TODO(vipa, 2021-02-12): This could use a `make : (Int -> a) -> Int -> [a]` that we discussed a while back
    let frontier = st.frontier in
    let queue = map (lam _. ref []) (makeSeq (maxOrElse (lam _. 0) subi (map _maxDistanceFromRoot frontier)) ()) in
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
    let addedLeft = ref (_firstTimeStep, ref []) in
    let addedRight = ref (_firstTimeStep, []) in
    { st with frontier =
      [ TentativeMid
        { parents = frontier
        , addedNodesLeftChildren = addedLeft
        , addedNodesRightChildren = addedRight
        , maxDistanceFromRoot = addi 1 (maxOrElse (lam _. 0) subi (map _maxDistanceFromRoot frontier))
        , tentativeData = PrefixT {input = input, self = self}
        }
      ]
    }

let breakableAddInfix
  : BreakableInput res self LOpen ROpen
  -> self
  -> State res self RClosed
  -> Option (State res self ROpen)
  = _addLOpen

let breakableAddPostfix
  : BreakableInput res self LOpen RClosed
  -> self
  -> State res self RClosed
  -> Option (State res self RClosed)
  = _addLOpen

let breakableAddAtom
  : BreakableInput res self LClosed RClosed
  -> self
  -> State res self ROpen
  -> State res self RClosed
  = lam input. lam self. lam st.
    let id = _uniqueID st in
    { st with frontier = [TentativeLeaf {id = id, input = input, self = self}] }
