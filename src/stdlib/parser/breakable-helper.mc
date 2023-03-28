include "breakable.mc"

type AllowSet id
con AllowSet : all id. Map id () -> AllowSet id
con DisallowSet : all id. Map id () -> AllowSet id

let _isWhitelist
  : AllowSet id -> Bool
  = lam a. match a with AllowSet _ then true else false

type BreakableProduction prodLabel
con BreakableAtom : all prodLabel.
  { label : prodLabel
  } -> BreakableProduction prodLabel
con BreakableInfix : all prodLabel.
  { label : prodLabel
  , leftAllow : AllowSet prodLabel
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel
con BreakablePrefix : all prodLabel.
  { label : prodLabel
  , rightAllow : AllowSet prodLabel
  } -> BreakableProduction prodLabel
con BreakablePostfix : all prodLabel.
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

let _eqOpId : OpId -> OpId -> Bool = eqi
let _cmpOpId : OpId -> OpId -> Int = subi
let _rootID : OpId = negi 1
let _firstOpId : OpId = 0
let _nextOpId : OpId -> OpId = addi 1

let _opIdI
  : all lstyle. all rstyle. BrekableInput lstyle rstyle
  -> OpId
  = lam input.
    switch input
    case AtomI x then x.id
    case InfixI x then x.id
    case PrefixI x then x.id
    case PostfixI x then x.id
    end
let _allowedTopI
  : BreakableInput lstyle rstyle
  -> Bool
  = lam input.
    switch input
    case AtomI x then x.allowedTop
    case InfixI x then x.allowedTop
    case PrefixI x then x.allowedTop
    case PostfixI x then x.allowedTop
    end
let _allowedLeftI
  : BreakableInput lstyle rstyle
  -> AllowSet OpId
  = lam input.
    switch input
    case InfixI x then x.leftAllow
    case PostfixI x then x.leftAllow
    case _ then AllowSet (mapEmpty _cmpOpId)
    end
let _allowedRightI
  : BreakableInput lstyle rstyle
  -> AllowSet OpId
  = lam input.
    switch input
    case InfixI x then x.rightAllow
    case PrefixI x then x.rightAllow
    case _ then AllowSet (mapEmpty _cmpOpId)
    end

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

type PairedSelf self lstyle rstyle =
  { self : self lstyle rstyle
  , input : BreakableInput lstyle rstyle
  }

let breakableHelperInterface
  : BreakableGenGrammar prodLabel
  -> BreakableInput LClosed RClosed
  -> { addAtom
       : BreakableInput LClosed RClosed
       -> self LClosed RClosed
       -> State self ROpen
       -> State self RClosed
     , addPrefix
       : BreakableInput LClosed ROpen
       -> self LClosed ROpen
       -> State self ROpen
       -> State self ROpen
     , addInfix
       : BreakableInput LOpen ROpen
       -> self LOpen ROpen
       -> State self RClosed
       -> Option (State self ROpen)
     , addPostfix
       : BreakableInput LOpen RClosed
       -> self LOpen RClosed
       -> State self RClosed
       -> Option (State self RClosed)
     , finalizeParse
       : State self RClosed
       -> Option [PermanentNode self]
     , reportAmbiguities
       : { toTok : all lstyle. all rstyle. Important -> self lstyle rstyle -> [tokish]
         , leftPos : all rstyle. self LClosed rstyle -> pos
         , rightPos : all lstyle. self lstyle RClosed -> pos
         , lpar : tokish
         , rpar : tokish }
       -> [PermanentNode self] -- NonEmpty
       -> [Ambiguity pos tokish]
     , constructSimple
       : { constructAtom : self LClosed RClosed -> res
         , constructInfix : self LOpen ROpen -> res -> res -> res
         , constructPrefix : self LClosed ROpen -> res -> res
         , constructPostfix : self LOpen RClosed -> res -> res
         }
       -> [PermanentNode self] -- NonEmpty
       -> res
     }
  = lam gen. lam parInput.
    let parId = _opIdI parInput in
    let config: Config (PairedSelf self) =
      { topAllowed = lam ps: PairedSelf self lstyle rstyle. _allowedTopI ps.input
      , leftAllowed = lam x: {parent: PairedSelf self LOpen rstyle, child: PairedSelf self lstyle rstyle2}. breakableInAllowSet (_opIdI x.child.input) (_allowedLeftI x.parent.input)
      , rightAllowed = lam x: {parent: PairedSelf self lstyle ROpen, child: PairedSelf self lstyle2 rstyle}. breakableInAllowSet (_opIdI x.child.input) (_allowedRightI x.parent.input)
      , parenAllowed = lam x: PairedSelf self lstyle rstyle.
        let l = breakableInAllowSet parId (_allowedLeftI x.input) in
        let r = breakableInAllowSet parId (_allowedRightI x.input) in
        switch (l, r)
        case (true, true) then GEither ()
        case (true, false) then GLeft ()
        case (false, true) then GRight ()
        case (false, false) then GNeither ()
        end
      , groupingsAllowed = lam pair: (PairedSelf self lstyle ROpen, PairedSelf self LOpen rstyle).
        let map = switch pair .1 .input
          case InfixI x then x.precWhenThisIsRight
          case PostfixI x then x.precWhenThisIsRight
          end in
        match mapLookup (_opIdI pair .0 .input) map with Some g then
          let g: OpGrouping = g in
          switch g
          case {mayGroupLeft = true, mayGroupRight = true} then GEither ()
          case {mayGroupLeft = true, mayGroupRight = false} then GLeft ()
          case {mayGroupLeft = false, mayGroupRight = true} then GRight ()
          case {mayGroupLeft = false, mayGroupRight = false} then GNeither ()
          end
        else GEither ()
      } in
    { addAtom = lam input. lam self. lam state. breakableAddAtom config {self = self, input = input} state
    , addInfix = lam input. lam self. lam state. breakableAddInfix config {self = self, input = input} state
    , addPrefix = lam input. lam self. lam state. breakableAddPrefix config {self = self, input = input} state
    , addPostfix = lam input. lam self. lam state. breakableAddPostfix config {self = self, input = input} state
    , finalizeParse = lam state. breakableFinalizeParse config state
    , reportAmbiguities =
      lam reportConfig
        : { toTok : all lstyle. all rstyle. Important -> self lstyle rstyle -> [tokish]
          , leftPos : all rstyle. self LClosed rstyle -> pos
          , rightPos : all lstyle. self lstyle RClosed -> pos
          , lpar : tokish
          , rpar : tokish }.
      let reportConfig =
        { topAllowed = config.topAllowed
        , parenAllowed = config.parenAllowed
        , toTok = lam important. lam self: PairedSelf self lstyle rstyle. reportConfig.toTok important self.self
        , leftPos = lam self: PairedSelf self LClosed rstyle. reportConfig.leftPos self.self
        , rightPos = lam self: PairedSelf self lstyle RClosed. reportConfig.rightPos self.self
        , lpar = reportConfig.lpar
        , rpar = reportConfig.rpar
        }
      in breakableReportAmbiguities reportConfig
    , constructSimple =
      lam config
        : { constructAtom : self LClosed RClosed -> res
        , constructInfix : self LOpen ROpen -> res -> res -> res
        , constructPrefix : self LClosed ROpen -> res -> res
        , constructPostfix : self LOpen RClosed -> res -> res }.
      let config =
        { constructAtom = lam self: PairedSelf self LClosed RClosed. config.constructAtom self.self
        , constructInfix = lam self: PairedSelf self LOpen ROpen. config.constructInfix self.self
        , constructPrefix = lam self: PairedSelf self LClosed ROpen. config.constructPrefix self.self
        , constructPostfix = lam self: PairedSelf self LOpen RClosed. config.constructPostfix self.self
        }
      in breakableConstructSimple config
    }

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

type Self lopen ropen = {pos: Int, val: Int, str: String} in

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
  : BreakableGenGrammar String
  -> [Int -> TestToken]
  -> ParseResult
  = lam gen.
    let parInput = mapFindExn "par" gen.atoms in
    match breakableHelperInterface gen parInput
    with {addAtom = addAtom, addPrefix = addPrefix, addInfix = addInfix, addPostfix = addPostfix, finalizeParse = finalizeParse, reportAmbiguities = reportAmbiguities, constructSimple = constructSimple} in
    recursive
      let workROpen = lam pos. lam st. lam tokens.
        match tokens with [t] ++ tokens then
          let t = t pos in
          let pos = addi 1 pos in
          match t with TestAtom {x = self, input = input} then
            workRClosed pos (addAtom input self st) tokens
          else match t with TestPrefix {x = self, input = input} then
            workROpen pos (addPrefix input self st) tokens
          else PFail ()
        else PFail ()
      let workRClosed = lam pos. lam st. lam tokens.
        match tokens with [t] ++ tokens then
          let t = t pos in
          let pos = addi 1 pos in
          match t with TestInfix {x = self, input = input} then
            match addInfix input self st with Some st
            then workROpen pos st tokens
            else PFail ()
          else match t with TestPostfix {x = self, input = input} then
            match addPostfix input self st with Some st
            then workRClosed pos st tokens
            else PFail ()
          else PFail ()
        else match finalizeParse st with Some tops then
          let reportConfig =
            { toTok = selfToTok
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
          match reportAmbiguities reportConfig tops with ambs & [_] ++ _ then
            PAmbiguities ambs
          else PSuccess (constructSimple constructConfig tops)
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

let test = testParse genned in

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

let test = testParse genned in

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
