-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "lexer.mc"
include "map.mc"
include "string.mc"
include "either.mc"
include "common.mc"
include "error-highlight.mc"
include "name.mc"

-- NOTE(vipa, 2021-02-05): I want to create types that refer to
-- `Token`, which lives in a language fragment. There is no top-level
-- `use` (for fairly good reasons), and there is no type-level `use`
-- (just because it hasn't been done yet), so for the moment I create
-- a new language fragment to declare the types
lang ParserBase = TokenParser + EOFTokenParser
  syn SpecSymbol =
  | TokSpec TokenRepr
  | LitSpec {lit: String}

  -- NOTE(vipa, 2022-03-02): `SpecSymbol` should only have the
  -- `TokSpec` and `LitSpec` constructors, but `TokenRepr` should be
  -- complete according to what's in scope.
  type SymSet = {eps: Bool, syms: Map SpecSymbol ()}

  sem eqSpecSymbol (l : SpecSymbol) =
  | r -> eqi 0 (_compareSpecSymbol (l, r))
  sem compareSpecSymbol (l : SpecSymbol) =
  | r -> _compareSpecSymbol (l, r)
  sem _compareSpecSymbol =
  | (TokSpec l, TokSpec r) -> tokReprCompare (l, r)
  | (LitSpec l, LitSpec r) -> cmpString l.lit r.lit
  | (l, r) -> subi (constructorTag l) (constructorTag r)

  sem symSpecToStr =
  | TokSpec t -> tokReprToStr t
  | LitSpec t -> snoc (cons '\'' t.lit) '\''
end

type Production prodLabel state = {nt: Name, label: prodLabel, rhs: [Symbol], action: Action state}
type Grammar prodLabel state =
  { start: Name
  , productions: [Production prodLabel state]
  }

lang ParserSpec = ParserBase
  syn SpecSymbol =
  | NtSpec Name

  sem symSpecToStr =
  | NtSpec n -> n

  sem _compareSpecSymbol =
  | (NtSpec l, NtSpec r) -> nameCmp l r

  sem ntSym =
  | nt -> NtSpec nt
  sem litSym =
  | str ->
    let res: NextTokenResult = nextToken {str = str, pos = posVal "" 1 1} in
    match (res.stream.str, res.lit) with ("", !"") then LitSpec {lit = str}
    else error (join ["A literal token does not lex as a single token: \"", res.stream.str, "\""])
  sem tokSym =
  | repr -> TokSpec repr
end

lang ParserGenerated = ParserBase
  syn SpecSymbol =
  -- NOTE(vipa, 2021-02-08): The `Ref` here is slightly undesirable, but I see no other way to construct a cyclic data structure
  -- NOTE(vipa, 2021-02-08): The first `SpecSymbol` here should be `ParserBase.SpecSymbol`
  | NtSym {nt: Name, table: (Ref (Map SpecSymbol {syms: [SpecSymbol], action: Action state, label: prodLabel}))}

  -- NOTE(vipa, 2021-02-08): These should be opaque, and the key
  -- `SpecSymbol` in the `Map` should be `ParserBase.Symbol`
  type TableProd = {syms: [SpecSymbol], label: prodLabel, action: Action state}
  type Table = {start: {nt: Name, table: (Ref (Map SpecSymbol (TableProd prodLabel)))}, firstOfRhs: [SpecSymbol] -> SymSet, lits: Map String ()}

  sem symSpecToStr =
  | NtSym t -> t.nt

  sem _compareSpecSymbol =
  | (NtSym l, NtSym r) -> nameCmp l.nt r.nt
end

-- NOTE(vipa, 2022-03-02): This is essentially just a language
-- fragment to enable adding new `Token`s, everything else is intended
-- to be closed
lang ParserConcrete = ParserBase + ParserGenerated
  syn ParsedSymbol =
  | UserSym Dyn
  | TokParsed Token
  | LitParsed {lit: String, info: Info}

  type Action = state -> [ParsedSymbol] -> Dyn

  type FullStackItem = {seen: [ParsedSymbol], rest: [SpecSymbol], label: prodLabel, action: Action state}
  type StackItem = {seen: [ParsedSymbol], rest: [SpecSymbol], label: prodLabel}

  sem symParsedToStr =
  | UserSym _ -> "<UserSym>"
  | TokParsed t -> tokToStr t
  | LitParsed t -> t.lit

  sem symParsedInfo =
  | UserSym _ -> NoInfo ()
  | TokParsed t -> tokInfo t
  | LitParsed t -> t.info

  sem parsedSymToSpecSym =
  | TokParsed t -> TokSpec (tokToRepr t)
  | LitParsed x -> LitSpec {lit = x.lit}

  sem parsedMatchesSpec (spec : SpecSymbol) =
  | TokParsed t -> match spec with TokSpec repr then tokKindEq repr t else false
  | LitParsed x -> match spec with LitSpec s then eqString x.lit s.lit else false

  syn ParseError =
  | UnexpectedFirst {nt : Name, stack : [StackItem prodLabel], found : ParsedSymbol, expected : [SpecSymbol]}
  | UnexpectedToken {stack : [StackItem prodLabel], found : ParsedSymbol, expected : SpecSymbol}
end

let _iterateUntilFixpoint : (a -> a -> Bool) -> (a -> a) -> a -> a =
  lam eq. lam f.
    recursive let work = lam a.
      let next = f a in
      if eq a next then a else work next
    in work

let _sanitizeStack = use ParserConcrete in use ParserSpec in lam stack.
  let genSymToSym = lam sym.
    match sym with NtSym {nt = nt} then NtSpec nt else sym in
  let work = lam item: FullStackItem prodLabel.
    {seen = item.seen, rest = map genSymToSym item.rest, label = item.label} in
  map work stack

let _expectedFromStack = use ParserConcrete in lam firstOfRhs: [SpecSymbol] -> SymSet.
  recursive let work = lam stack: [FullStackItem prodLabel].
    match stack with stack ++ [{rest = rest}] then
      let res = firstOfRhs rest in
      let here = mapKeys res.syms in
      if res.eps
      then concat here (work stack)
      else here
    else []
  in work


type GenError prodLabel = Map Name (Map SpecSymbol [prodLabel])

lang ParserGeneration = ParserSpec + ParserGenerated
  -- NOTE(vipa, 2022-03-02): The type signature is a bit weird here,
  -- because `ParserGenerated` will add the `NtSym` constructor to
  -- `SpecSymbol`, even though that's not a valid input for this
  -- function.
  sem genParsingTable =
  | grammar ->
    let grammar: Grammar prodLabel state = grammar in
    match grammar with {productions = productions, start = startNt} in

    let emptySymSet = {eps = false, syms = mapEmpty compareSpecSymbol} in
    let eqSymSet = lam s1: SymSet. lam s2: SymSet.
      match (s1, s2) with ({eps = e1, syms = s1}, {eps = e2, syms = s2}) then
        and
          (eqBool e1 e2)
          (eqSeq (lam a: (Symbol, ()). lam b: (Symbol, ()). eqSpecSymbol a.0 b.0)
            (mapBindings s1)
            (mapBindings s2))
      else dprintLn (s1, s2);  never in

    let eqFirstSet = lam s1. lam s2.
      eqSeq
        (lam a: (Name, SpecSymbol). lam b: (Name, SpecSymbol). if nameEq a.0 b.0 then eqSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let eqFollowSymSet = lam s1. lam s2.
      eqSeq (lam a: (SpecSymbol, ()). lam b: (SpecSymbol, ()). eqSpecSymbol a.0 b.0)
        (mapBindings s1)
        (mapBindings s2) in

    let eqFollowSet = lam s1. lam s2.
      eqSeq
        (lam a: (Name, Unknown). lam b: (Name, Unknown). if nameEq a.0 b.0 then eqFollowSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let addProdToFirst : Map Name SymSet -> Production prodLabel state -> SymSet -> SymSet =
      lam prev. lam prod. lam symset.
        recursive let work = lam symset: SymSet. lam rhs.
          match rhs with [] then {symset with eps = true}
          else match rhs with [(TokSpec _ | LitSpec _) & t] ++ _ then
            {symset with syms = mapInsert t () symset.syms}
          else match rhs with [NtSpec nt] ++ rhs then
            let otherSymset = match mapLookup nt prev
              with Some s then s
              else emptySymSet in
            let symset = {symset with syms = mapUnion symset.syms otherSymset.syms} in
            if otherSymset.eps then work symset rhs else symset
          else never
        in work symset prod.rhs in

    let groupedProds : Map Name [Production prodLabel state] =
      foldl
        (lam acc. lam prod: Production prodLabel state. mapInsert prod.nt (snoc (optionGetOr [] (mapLookup prod.nt acc)) prod) acc)
        (mapEmpty nameCmp)
        productions in

    let addNtToFirstSet = lam prev. lam nt. lam symset.
      let prods = mapFindExn nt groupedProds in
      foldl (lam symset. lam prod. addProdToFirst prev prod symset) symset prods in

    -- let dprintFirstSet = lam firstSet.
    --   let _ = printLn "" in
    --   let _ = dprint (mapBindings (mapMap (lam symset. {symset with syms = mapBindings symset.syms}) firstSet)) in
    --   let _ = printLn "" in
    --   firstSet in

    -- let dprintFollowSet = lam followSet.
    --   let _ = printLn "" in
    --   let _ = dprint (mapBindings (mapMap mapBindings followSet)) in
    --   let _ = printLn "" in
    --   followSet in

    let firstSet : Map Name SymSet =
      _iterateUntilFixpoint eqFirstSet
        (lam prev. mapMapWithKey (addNtToFirstSet prev) prev)
        (mapMap (lam. emptySymSet) groupedProds) in

    -- let _ = print "\n\nFirsts:" in
    -- let _ = dprintFirstSet firstSet in

    let firstOfRhs : [SpecSymbol] -> SymSet =
      recursive let work = lam symset: SymSet. lam rhs.
        -- NOTE(vipa, 2021-06-18): This will be called post generation
        -- as well, so it needs to handle NtSym, even thought it'll
        -- not be relevant when generating the table
        match rhs with [] then {symset with eps = true}
        else match rhs with [(TokSpec _ | LitSpec _) & t] ++ _ then
          {symset with syms = mapInsert t () symset.syms}
        else match rhs with [NtSpec nt | NtSym {nt = nt}] ++ rhs then
          let otherSymset = match mapLookup nt firstSet
            with Some s then s
            else emptySymSet in
          let symset = {symset with syms = mapUnion symset.syms otherSymset.syms} in
          if otherSymset.eps then work symset rhs else symset
        else never
      in work emptySymSet in

    let addProdToFollow : Production prodLabel state -> Map Name (Map SpecSymbol ()) -> Map Name (Map SpecSymbol ()) = lam prod. lam follow.
      match prod with {nt = prodNt, rhs = rhs} then
        recursive let work = lam follow. lam rhs.
          match rhs with [] then follow
          else match rhs with [NtSpec nt] ++ rhs then
            let ntFollow = match mapLookup nt follow
              with Some s then s
              else mapEmpty compareSpecSymbol in
            let otherSymset = firstOfRhs rhs in
            let ntFollow = mapUnion ntFollow otherSymset.syms in
            let ntFollow = if otherSymset.eps
              then mapUnion ntFollow (mapFindExn prodNt follow)
              else ntFollow in
            work (mapInsert nt ntFollow follow) rhs
          else match rhs with [_] ++ rhs then
            work follow rhs
          else never
        in work follow rhs
      else never in

    let followSet : Map Name (Map SpecSymbol ()) =
      _iterateUntilFixpoint eqFollowSet
        (lam prev. foldl (lam prev. lam prod. addProdToFollow prod prev) prev productions)
        (mapInsert startNt (mapInsert (TokSpec (EOFRepr ())) () (mapEmpty compareSpecSymbol))
          (mapMap (lam. mapEmpty compareSpecSymbol) groupedProds)) in

    -- let _ = print "\n\nFollows:" in
    -- let _ = dprintFollowSet followSet in

    -- The first `Symbol` should be `ParserBase.Symbol`, the second should be `ParserGenerated.Symbol`
    let emptyTableTarget = ref (mapEmpty compareSpecSymbol) in
    let table : Map Name (Ref (Map SpecSymbol {syms : [SpecSymbol], action: Action state})) =
      mapMap (lam. ref (mapEmpty compareSpecSymbol)) groupedProds in

    let specSymToGenSym = lam sym.
      match sym with NtSpec nt
      then NtSym {nt = nt, table = optionGetOr emptyTableTarget (mapLookup nt table)}
      else sym
    in

    let hasLl1Error = ref false in
    let ll1Errors = mapMap (lam. ref (mapEmpty compareSpecSymbol)) groupedProds in

    let addProdToTable = lam prod: Production prodLabel state.
      let tableRef = mapFindExn prod.nt table in
      let prev = deref tableRef in
      let firstSymset = firstOfRhs prod.rhs in
      let symset = if firstSymset.eps
        then mapUnion firstSymset.syms (mapFindExn prod.nt followSet)
        else firstSymset.syms in
      let newProd = {action = prod.action, label = prod.label, syms = map specSymToGenSym prod.rhs} in
      let tableAdditions = mapMap (lam. newProd) symset in
      for_ (mapBindings tableAdditions)
        (lam binding: (Symbol, TableProd prodLabel).
          match binding with (sym, {label = label}) then
            match mapLookup sym prev with Some prevProd then
              let prevProd: TableProd prodLabel = prevProd in
              modref hasLl1Error true;
              let errRef = mapFindExn prod.nt ll1Errors in
              let errTab = deref errRef in
              let errList = match mapLookup sym errTab
                with Some prods then snoc prods label
                else [prevProd.label, label] in
              modref errRef (mapInsert sym errList errTab)
            else ()
          else never);
      modref tableRef (mapUnion prev tableAdditions)
    in

    iter addProdToTable productions;

    let addLitToLits = lam lits. lam sym.
      match sym with LitSpec {lit = lit}
        then mapInsert lit () lits
        else lits in
    let lits = foldl
      (lam acc. lam prod: Production prodLabel state. foldl addLitToLits acc prod.rhs)
      (mapEmpty cmpString)
      productions in

    -- let dprintTablePair = lam nt. lam actions.
    --   dprintLn (nt, mapBindings (deref actions))
    -- in
    -- printLn "\n\nParse table:";
    -- mapMapWithKey dprintTablePair table;

    if deref hasLl1Error
      then Left (mapFromSeq nameCmp (filter (lam binding: (Unknown, Unknown). not (null (mapBindings binding.1))) (mapBindings (mapMap deref ll1Errors))))
      else Right {start = {nt = startNt, table = optionGetOr emptyTableTarget (mapLookup startNt table)}, firstOfRhs = firstOfRhs, lits = lits}
end

lang LL1Parser = ParserGeneration + ParserConcrete
  -- [SpecSymbol] -> [SpecSymbol]
  sem _dedupSymbolList =
  | x ->
    recursive
      let work = lam seen. lam retained. lam rest.
        match rest with [] then retained else
        match rest with [sym] ++ rest then
          match mapLookup sym seen with Some _
          then work seen retained rest
          else work (mapInsert sym () seen) (snoc retained sym) rest
        else never
    in work (mapEmpty compareSpecSymbol) [] x

  /-
    : ([SpecSymbol] -> SymSet)
    -> Option (Name, ParsedSymbol, [FullStackItem prodLabel])
    -> Option (SpecSymbol, ParsedSymbol, [FullStackItem prodLabel])
    -> ParseError prodLabel
  -/
  sem _mkLL1Error (firstOfRhs : [SpecSymbol] -> SymSet) (openInfo : Option (Name, ParsedSymbol, [FullStackItem prodLabel])) =
  | workInfo ->
    match openInfo with Some (nt, token, stack) then
      UnexpectedFirst
        { nt = nt
        , stack = _sanitizeStack stack
        , found = token
        , expected =
          let here: SymSet = firstOfRhs [use ParserSpec in NtSpec nt] in
          let res = mapKeys here.syms in
          let res = if here.eps
            then concat res (_expectedFromStack firstOfRhs stack)
            else res
          in _dedupSymbolList res
        }
     else match workInfo with Some (expected, token, stack) then
       UnexpectedToken
         { stack = _sanitizeStack stack
         , found = token
         , expected = expected
         }
     else error "Tried to make an LL1 error without having any information to construct one with"

  sem parseWithTable (table : Table parseLabel) (filename : String) (state : state) =
  | contents ->
    match table with {start = start, lits = lits, firstOfRhs = firstOfRhs} in
    let lastOpen = ref (None ()) in
    let getNextToken = lam stream.
      let res: NextTokenResult = nextToken stream in
        -- OPT(vipa, 2021-02-08): Could use the hash of the lit to maybe optimize this, either by using a hashmap, or by first checking against the hash in a bloom filter or something like that
      if if (eqString "" res.lit) then true else not (mapMem res.lit lits)
        then {token = TokParsed res.token, stream = res.stream}
        else {token = LitParsed {lit = res.lit, info = res.info}, stream = res.stream} in
    recursive
      let openNt = lam nt: {nt: Name, table: Unknown}. lam token. lam stack. lam stream.
        modref lastOpen (Some (nt.nt, token, stack));
        let table = deref nt.table in
        match mapLookup (parsedSymToSpecSym token) table with Some r then
          let r: {syms: [SpecSymbol], action: Action state, label: prodLabel} = r in
          work (snoc stack {seen = [], rest = r.syms, action = r.action, label = r.label}) token stream
        else Left (_mkLL1Error firstOfRhs (deref lastOpen) (None ()))
      let work = lam stack : [FullStackItem prodLabel]. lam token. lam stream.
        match stack with stack ++ [curr & {rest = [NtSym nt] ++ rest}] then
          openNt nt token (snoc stack {curr with rest = rest}) stream
        else match stack with stack ++ [above & {seen = seenAbove}, {seen = seen, rest = [], action = action}] then
          work (snoc stack {above with seen = snoc seenAbove (UserSym (action state seen))}) token stream
        else match stack with oldStack & (stack ++ [curr & {rest = [t] ++ rest, seen = seen}]) then
          if parsedMatchesSpec t token then
            modref lastOpen (None ());
            let next = getNextToken stream in
            work (snoc stack {{curr with rest = rest} with seen = snoc seen token}) next.token next.stream
          else Left (_mkLL1Error firstOfRhs (deref lastOpen) (Some (t, token, oldStack)))
        else match stack with [{seen = seen, rest = [], action = action}] then
          match token with TokParsed (EOFTok _)
            then Right (action state seen)
            else Left (_mkLL1Error firstOfRhs (deref lastOpen) (Some (TokSpec (EOFRepr ()), token, stack)))
        else print "ERROR: ";
             dprintLn (stack, token, stream);
             error "Unexpected parse error, this shouldn't happen"
    in
      let stream = {pos = initPos filename, str = contents} in
      match getNextToken stream with {token = token, stream = stream} in
      openNt start token [] stream

  sem highlightsForFound =
  | TokParsed (EOFTok {info = Info x}) ->
    let info = Info {{x with row1 = subi x.row1 1} with col1 = 0} in
    [Irrelevant info, Added {content = tokReprToStr (EOFRepr ()), ensureSurroundedBySpaces = false}]
  | x -> [Relevant (symParsedInfo x)]
  sem ll1ToErrorHighlightSpec =
  | UnexpectedFirst x ->
    let info = symParsedInfo x.found in
    { highlight = highlightsForFound x.found, found = parsedSymToSpecSym x.found, expected = x.expected, info = info }
  | UnexpectedToken x ->
    let info = symParsedInfo x.found in
    { highlight = highlightsForFound x.found, found = parsedSymToSpecSym x.found, expected = [x.expected], info = info }

  sem ll1DefaultHighlight (content : String) =
  | x ->
    let x: { highlight : [Highlight], found : SpecSymbol, expected : [SpecSymbol], info : Info } = x in
    let expectedStr = switch map symSpecToStr x.expected
      case [x] then x
      case [a, b] then join [a, " or ", b]
      case rest ++ [b] then join [strJoin ", " rest, ", or ", b]
      end
    in
    let highlight = formatHighlights terminalHighlightErrorConfig content x.highlight in
    let message = join
      [ "Unexpected token, found ", symSpecToStr x.found, ", expected ", expectedStr, "\n"
      , highlight
      ] in
    (x.info, message)
end

lang TestParserLang = LL1Parser + Lexer
end

mexpr

use TestParserLang in

let genParser = genParsingTable in

let nonTerminal = nameSym in
let nt = ntSym in
let lit = litSym in
let lident = tokSym (LIdentRepr ()) in
let uident = tokSym (UIdentRepr ()) in
let int = tokSym (IntRepr ()) in

let errorMapToBindingsExc = lam m.
  match m with Left m then
    map (lam x. match x with (nt, x) in (nameGetStr nt, x)) (mapBindings (mapMap mapBindings m))
  else error "Expected a left result" in
let unwrapTableExc = lam m.
  match m with Right m then m
  else error "Expected a right result" in

let top = nonTerminal "File" in
let topAtom = nonTerminal "FileAtom" in
let topInfix = nonTerminal "FileInfix" in
let topFollow = nonTerminal "FileFollow" in
let decl = nonTerminal "Declaration" in
let expr = nonTerminal "Expression" in
let exprAtom = nonTerminal "ExpressionAtom" in
let exprFollow = nonTerminal "ExpressionFollow" in
let exprInfix = nonTerminal "ExpressionInfix" in
let exprPrefix = nonTerminal "ExpressionPrefix" in
let exprPrefixes = nonTerminal "ExpressionPrefixes" in

type Wrapped in
con Wrapped : {label: String, val: [SpecSymbol]} -> Wrapped in
let wrap = lam label. lam state: (). lam x. Wrapped {label = label, val = x} in

let gFailOnce : Grammar String () =
  { start = top
  , productions =
    [ {nt = top, label = "toptop", rhs = [nt topAtom, nt topFollow], action = wrap "toptop"}
    , {nt = topAtom, label = "topdecl", rhs = [nt decl], action = wrap "topdecl"}
    , {nt = topFollow, label = "topfollowsome", rhs = [nt topInfix, nt topAtom, nt topFollow], action = wrap "topfollowsome"}
    , {nt = topFollow, label = "topfollownone", rhs = [], action = wrap "topfollownone"}
    , {nt = topInfix, label = "topinfixjuxt", rhs = [], action = wrap "topinfixjuxt"}
    , {nt = decl, label = "decllet", rhs = [lit "let", lident, lit "=", nt expr], action = wrap "decllet"}
    , {nt = decl, label = "declletrec", rhs = [lit "let", lit "rec", lident, lit "=", nt expr], action = wrap "declletrec"}
    , {nt = expr, label = "exprint", rhs = [int], action = wrap "exprint"}
    ]
  } in

utest errorMapToBindingsExc (genParser gFailOnce)
with [ ( "Declaration"
  , [ ( LitSpec { lit = "let" }
      , [ "decllet" , "declletrec" ]
      )
    ]
  )
]
in

let gFailTwice : Grammar String () =
  { start = top
  , productions =
    [ {nt = top, label = "toptop", rhs = [nt topAtom, nt topFollow], action = wrap "toptop"}
    , {nt = topAtom, label = "topdecl", rhs = [nt decl], action = wrap "topdecl"}
    , {nt = topFollow, label = "topfollowsome", rhs = [nt topInfix, nt topAtom, nt topFollow], action = wrap "topfollowsome"}
    , {nt = topFollow, label = "topfollownone", rhs = [], action = wrap "topfollownone"}
    , {nt = topInfix, label = "topinfixjuxt", rhs = [], action = wrap "topinfixjuxt"}
    , {nt = decl, label = "decllet", rhs = [lit "let", lident, lit "=", nt expr], action = wrap "decllet"}
    , {nt = decl, label = "declletrec", rhs = [lit "let", lit "rec", lident, lit "=", nt expr], action = wrap "declletrec"}
    , {nt = decl, label = "declletmut", rhs = [lit "let", lit "mut", lident, lit "=", nt expr], action = wrap "declletmut"}
    , {nt = expr, label = "exprint", rhs = [int], action = wrap "exprint"}
    ]
  } in

utest errorMapToBindingsExc (genParser gFailTwice)
with [ ( "Declaration"
  , [ ( LitSpec { lit = "let" }
      , [ "decllet" , "declletrec" , "declletmut" ]
      )
    ]
  )
]
in

let gFailLet : Grammar String () =
  { start = top
  , productions =
    [ {nt = top, label = "toptop", rhs = [nt topAtom, nt topFollow], action = wrap "toptop"}
    , {nt = topAtom, label = "topdecl", rhs = [nt decl], action = wrap "topdecl"}
    , {nt = topFollow, label = "topfollowsome", rhs = [nt topInfix, nt topAtom, nt topFollow], action = wrap "topfollowsome"}
    , {nt = topFollow, label = "topfollownone", rhs = [], action = wrap "topfollownone"}
    , {nt = topInfix, label = "topinfixjuxt", rhs = [], action = wrap "topinfixjuxt"}
    , {nt = decl, label = "decllet", rhs = [lit "let", lident, lit "=", nt expr], action = wrap "decllet"}
    , {nt = expr, label = "exprtop", rhs = [nt exprPrefixes, nt exprAtom, nt exprFollow], action = wrap "exprtop"}
    , {nt = exprPrefixes, label = "exprpresome", rhs = [nt exprPrefix, nt exprPrefixes], action = wrap "exprpresome"}
    , {nt = exprPrefixes, label = "exprprenone", rhs = [], action = wrap "exprprenone"}
    , {nt = exprFollow, label = "exprfollowsome", rhs = [nt exprInfix, nt exprPrefixes, nt exprAtom, nt exprFollow], action = wrap "exprfollowsome"}
    , {nt = exprFollow, label = "exprfollownone", rhs = [], action = wrap "exprfollownone"}
    , {nt = exprPrefix, label = "exprlet", rhs = [lit "let", lident, lit "=", nt expr, lit "in"], action = wrap "exprlet"}
    , {nt = exprInfix, label = "exprinfixjuxt", rhs = [], action = wrap "exprinfixjuxt"}
    , {nt = exprAtom, label = "exprint", rhs = [int], action = wrap "exprint"}
    ]
  } in

utest errorMapToBindingsExc (genParser gFailLet)
with [ ( "ExpressionFollow"
  , [ ( LitSpec { lit = "let" }
      , [ "exprfollowsome" , "exprfollownone" ]
      )
    ]
  )
]
in

let g : Grammar String () =
  { start = top
  , productions =
    [ {nt = top, label = "toptop", rhs = [nt topAtom, nt topFollow], action = wrap "toptop"}
    , {nt = topAtom, label = "topdecl", rhs = [nt decl], action = wrap "topdecl"}
    , {nt = topFollow, label = "topfollowsome", rhs = [nt topInfix, nt topAtom, nt topFollow], action = wrap "topfollowsome"}
    , {nt = topFollow, label = "topfollownone", rhs = [], action = wrap "topfollownone"}
    , {nt = topInfix, label = "topinfixjuxt", rhs = [], action = wrap "topinfixjuxt"}
    , {nt = decl, label = "decllet", rhs = [lit "let", lident, lit "=", nt expr], action = wrap "decllet"}
    , {nt = expr, label = "exprint", rhs = [int], action = wrap "exprint"}
    ]
  } in

let table = unwrapTableExc (genParser g) in
let parse = parseWithTable table "file" () in

utest parse "let a = 1"
with Right
  ( Wrapped
    { label = "toptop"
    , val =
      [ UserSym
        ( Wrapped
          { label = "topdecl"
          , val =
            [ UserSym
              (Wrapped
                { label = "decllet"
                , val =
                  [ LitParsed
                    { lit = "let"
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
                    }
                  , TokParsed
                    ( LIdentTok
                      { val = "a"
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                      }
                    )
                  , LitParsed
                    { lit = "="
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
                    }
                  , UserSym
                    ( Wrapped
                      { label = "exprint"
                      , val =
                        [ TokParsed
                          ( IntTok
                            { val = 1
                            , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 9 , col1 = 8 }
                            }
                          )
                        ]
                      }
                    )
                  ]
                }
              )
            ]
          }
        )
      , UserSym (Wrapped { label = "topfollownone" , val = [] })
      ]
    }
  )
in

utest parse "let a = 1\nlet b = 4"
with Right
  ( Wrapped
    { label = "toptop"
    , val =
      [ UserSym
        ( Wrapped
          { label = "topdecl"
          , val =
            [ UserSym
              ( Wrapped
                { label = "decllet"
                , val =
                  [ LitParsed
                    { lit = "let"
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
                    }
                  , TokParsed
                    ( LIdentTok
                      { val = "a"
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                      }
                    )
                  , LitParsed
                    { lit = "="
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
                    }
                  , UserSym
                    ( Wrapped
                      { label = "exprint"
                      , val =
                        [ TokParsed
                          ( IntTok
                            { val = 1
                            , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 9 , col1 = 8 }
                            }
                          )
                        ]
                      }
                    )
                  ]
                }
              )
            ]
          }
        )
      , UserSym
        ( Wrapped
          { label = "topfollowsome"
          , val =
            [ UserSym (Wrapped { label = "topinfixjuxt" , val = [] })
            , UserSym
              ( Wrapped
                { label = "topdecl"
                , val =
                  [ UserSym
                    ( Wrapped
                      { label = "decllet"
                      , val =
                        [ LitParsed
                          { lit = "let"
                          , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 3 , col1 = 0 }
                          }
                        , TokParsed
                          ( LIdentTok
                            { val = "b"
                            , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 5 , col1 = 4 }
                            }
                          )
                        , LitParsed
                          { lit = "="
                          , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 7 , col1 = 6 }
                          }
                        , UserSym
                          ( Wrapped
                            { label = "exprint"
                            , val =
                              [ TokParsed
                                ( IntTok
                                  { val = 4
                                  , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 9 , col1 = 8 }
                                  }
                                )
                              ]
                            }
                          )
                        ]
                      }
                    )
                  ]
                }
              )
            , UserSym (Wrapped { label = "topfollownone" , val = [] })
            ]
          }
        )
      ]
    }
  )
in

utest parse "let" with () using lam l. lam. match l
with Left (UnexpectedToken
  { expected = (TokSpec (LIdentRepr ()))
  , stack = (
    [ {label = ("toptop"),seen = ([]),rest = ([(NtSpec _)])}
    , {label = ("topdecl"),seen = ([]),rest = ([])}
    , { label = ("decllet")
      , seen = ([(LitParsed {lit = ("let"),info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 0})})])
      , rest = ([(TokSpec (LIdentRepr ())),(LitSpec {lit = ("=")}),(NtSpec _)])
      }
    ])
  , found = (TokParsed (EOFTok {info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 3})}))
  })
then true else false
in

utest parse "let x =" with () using lam l. lam. match l
with Left (UnexpectedFirst
  { expected =
    [ TokSpec (IntRepr ())
    ]
  , stack =
    [ { label = "toptop" , seen = [] , rest = [NtSpec _]}
    , { label = "topdecl" , seen = [] , rest = []}
    , { label = "decllet"
      , seen =
        [ LitParsed {info = Info {filename = "file", row2 = 1,row1 = 1, col2 = 3,col1 = 0} , lit = "let"}
        , TokParsed (LIdentTok {info = Info {filename = "file", row2 = 1,row1 = 1, col2 = 5,col1 = 4} , val = "x"})
        , LitParsed {info = Info {filename = "file", row2 = 1,row1 = 1, col2 = 7,col1 = 6} , lit = "="}
        ]
      , rest = ([])
      }
    ]
  , found = TokParsed (EOFTok {info = (Info {filename = "file",row2 = 1,row1 = 1, col2 = 7,col1 = 7})}
    )
  , nt = _
  })
then true else false
in

utest parse "let let = 4" with ()
using lam l. lam. match l with Left (UnexpectedToken
  { expected = (TokSpec (LIdentRepr ()))
  , stack = (
    [ {label = ("toptop"),seen = ([]),rest = ([(NtSpec _)])}
    , {label = ("topdecl"),seen = ([]),rest = ([])}
    , { label = ("decllet")
      , seen = ([(LitParsed {lit = ("let"),info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 0})})])
      , rest = ([(TokSpec (LIdentRepr ())),(LitSpec {lit = ("=")}),(NtSpec _)])
      }
    ])
  , found = (LitParsed {lit = ("let"),info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 7,col1 = 4})})
  })
then true else false
in

()
