-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "lexer.mc"
include "map.mc"
include "string.mc"
include "either.mc"
include "common.mc"
include "error.mc"
include "name.mc"

type Dyn

let asDyn : all a. a -> Dyn = unsafeCoerce
let fromDyn : all a. Dyn -> a = unsafeCoerce

type SpecSymbol tok repr state prodLabel
type ParsedSymbol tok
type Action tok state = state -> [ParsedSymbol tok] -> Dyn

con TokSpec : all tok. all repr. all state. all prodLabel. repr -> SpecSymbol tok repr state prodLabel
con LitSpec : all tok. all repr. all state. all prodLabel. {lit: String} -> SpecSymbol tok repr state prodLabel
con NtSpec : all tok. all repr. all state. all prodLabel. Name -> SpecSymbol tok repr state prodLabel
  -- NOTE(vipa, 2021-02-08): The `Ref` here is slightly undesirable, but I see no other way to construct a cyclic data structure
  -- NOTE(vipa, 2021-02-08): The first `SpecSymbol` here should be `ParserBase.SpecSymbol`
con NtSym : all repr. all tok. all state. all prodLabel.
  { nt: Name
  , table: (Ref (Map (SpecSymbol tok repr state prodLabel) {syms: [SpecSymbol tok repr state prodLabel], action: Action tok state, label: prodLabel}))
  } -> SpecSymbol tok repr state prodLabel

con UserSym : all tok. Dyn -> ParsedSymbol tok
con TokParsed : all tok. tok -> ParsedSymbol tok
con LitParsed : all tok. {lit: String, info: Info} -> ParsedSymbol tok

type StackItem tok repr state prodLabel =
  { seen: [ParsedSymbol tok]
  , rest: [SpecSymbol tok repr state prodLabel]
  , label: prodLabel
  }

type ParseError tok repr state prodLabel
con UnexpectedFirst : all tok. all repr. all state. all prodLabel.
  { nt : Name
  , stack : [StackItem tok repr state prodLabel]
  , found : ParsedSymbol tok
  , expected : [SpecSymbol tok repr state prodLabel]
  } -> ParseError tok repr state prodLabel
con UnexpectedToken : all tok. all repr. all state. all prodLabel.
  { stack : [StackItem tok repr state prodLabel]
  , found : ParsedSymbol tok
  , expected : SpecSymbol tok repr state prodLabel
  } -> ParseError tok repr state prodLabel

-- NOTE(vipa, 2021-02-05): I want to create types that refer to
-- `Token`, which lives in a language fragment. There is no top-level
-- `use` (for fairly good reasons), and there is no type-level `use`
-- (just because it hasn't been done yet), so for the moment I create
-- a new language fragment to declare the types
lang ParserBase = TokenParser + EOFTokenParser
  -- NOTE(vipa, 2022-03-02): `SpecSymbol` should only have the
  -- `TokSpec` and `LitSpec` constructors, but `TokenRepr` should be
  -- complete according to what's in scope.
  type SymSet state prodLabel = {eps: Bool, syms: Map (SpecSymbol Token TokenRepr state prodLabel) ()}

  sem eqSpecSymbol : all state. all prodLabel. SpecSymbol Token TokenRepr state prodLabel -> SpecSymbol Token TokenRepr state prodLabel -> Bool
  sem eqSpecSymbol l =
  | r -> eqi 0 (_compareSpecSymbol (l, r))
  sem compareSpecSymbol : all state. all prodLabel. SpecSymbol Token TokenRepr state prodLabel -> SpecSymbol Token TokenRepr state prodLabel -> Int
  sem compareSpecSymbol l =
  | r -> _compareSpecSymbol (l, r)
  sem _compareSpecSymbol : all state. all prodLabel. (SpecSymbol Token TokenRepr state prodLabel, SpecSymbol Token TokenRepr state prodLabel) -> Int
  sem _compareSpecSymbol =
  | (TokSpec l, TokSpec r) -> tokReprCmp l r
  | (LitSpec l, LitSpec r) -> cmpString l.lit r.lit
  | (NtSpec l, NtSpec r) -> nameCmp l r
  | (l, r) -> subi (constructorTag l) (constructorTag r)

  sem symSpecToStr =
  | TokSpec t -> tokReprToStr t
  | LitSpec t -> snoc (cons '\'' t.lit) '\''
  | NtSpec n -> nameGetStr n
end

lang ParserSpec = ParserBase
  sem ntSym =
  | nt -> NtSpec nt
  sem litSym =
  | str ->
    let res: NextTokenResult = nextToken {str = str, pos = posVal (concat "lit: " str) 1 1} in
    match (res.stream.str, res.lit) with ("", !"") then LitSpec {lit = str}
    else error (join ["A literal token does not lex as a single token: \"", str,"\" leaves \"", res.stream.str, "\""])
  sem tokSym =
  | repr -> TokSpec repr
end

-- NOTE(vipa, 2022-03-02): This is essentially just a language
-- fragment to enable adding new `Token`s, everything else is intended
-- to be closed
lang ParserConcrete = ParserBase
  -- NOTE(vipa, 2021-02-08): These should be opaque
  type TableProd prodLabel state = {syms: [SpecSymbol Token TokenRepr state prodLabel], label: prodLabel, action: Action Token state}
  type Table prodLabel state = {start: {nt: Name, table: (Ref (Map (SpecSymbol Token TokenRepr state prodLabel) (TableProd prodLabel state)))}, firstOfRhs: [SpecSymbol Token TokenRepr state prodLabel] -> SymSet state prodLabel, lits: Map String ()}

  type Production prodLabel state =
    { nt: Name
    , label: prodLabel
    , rhs: [SpecSymbol Token TokenRepr state prodLabel]
    , action: Action Token state
    }
  type Grammar prodLabel state =
    { start: Name
    , productions: [Production prodLabel state]
    }

  type FullStackItem prodLabel state = {seen: [ParsedSymbol Token], rest: [SpecSymbol Token TokenRepr state prodLabel], label: prodLabel, action: Action Token state}

  sem symParsedToStr =
  | UserSym _ -> "<UserSym>"
  | TokParsed t -> tokToStr t
  | LitParsed t -> t.lit

  sem symParsedInfo =
  | UserSym _ -> NoInfo ()
  | TokParsed t -> tokInfo t
  | LitParsed t -> t.info

  sem parsedSymToSpecSym : all state. all prodLabel. ParsedSymbol Token -> SpecSymbol Token TokenRepr state prodLabel
  sem parsedSymToSpecSym =
  | TokParsed t -> TokSpec (tokToRepr t)
  | LitParsed x -> LitSpec {lit = x.lit}

  sem parsedMatchesSpec spec =
  | TokParsed t -> match spec with TokSpec repr then tokKindEq repr t else false
  | LitParsed x -> match spec with LitSpec s then eqString x.lit s.lit else false

  sem _sanitizeStack
    : all prodLabel. all state. [FullStackItem prodLabel state]
    -> [StackItem Token TokenRepr state prodLabel]
  sem _sanitizeStack =
  | stack ->
    let genSymToSym = lam sym.
      match sym with NtSym {nt = nt} then NtSpec nt else sym in
    let work = lam item.
      {seen = item.seen, rest = map genSymToSym item.rest, label = item.label} in
    map work stack

  sem _expectedFromStack
    : all state. all prodLabel. ([SpecSymbol Token TokenRepr state prodLabel] -> SymSet state prodLabel)
    -> [FullStackItem prodLabel state]
    -> [SpecSymbol Token TokenRepr state prodLabel]
  sem _expectedFromStack =
  | firstOfRhs ->
    recursive let work = lam stack.
      match stack with stack ++ [{rest = rest}] then
        let res = firstOfRhs rest in
        let here = mapKeys res.syms in
        if res.eps
        then concat here (work stack)
        else here
      else []
    in work
end

let _iterateUntilFixpoint : all a. (a -> a -> Bool) -> (a -> a) -> a -> a =
  lam eq. lam f.
    recursive let work = lam a.
      let next = f a in
      if eq a next then a else work next
    in work

type GenError prodLabel state = use Lexer in Map Name (Map (SpecSymbol Token TokenRepr state prodLabel) [prodLabel])

lang ParserGeneration = ParserSpec + ParserConcrete
  -- NOTE(vipa, 2022-03-02): The type signature is a bit weird here,
  -- because `ParserGenerated` will add the `NtSym` constructor to
  -- `SpecSymbol`, even though that's not a valid input for this
  -- function.
  sem genParsingTable : all prodLabel. all state. Grammar prodLabel state -> Either (GenError prodLabel state) (Table prodLabel state)
  sem genParsingTable =
  | grammar ->
    match grammar with {productions = productions, start = startNt} in

    let emptySymSet = {eps = false, syms = mapEmpty compareSpecSymbol} in
    let eqSymSet = lam s1: SymSet state prodLabel. lam s2: SymSet state prodLabel.
      match (s1, s2) with ({eps = e1, syms = s1}, {eps = e2, syms = s2}) then
        and
          (eqBool e1 e2)
          (eqSeq (lam a. lam b. eqSpecSymbol a.0 b.0)
            (mapBindings s1)
            (mapBindings s2))
      else dprintLn (s1, s2);  never in

    let eqFirstSet = lam s1. lam s2.
      eqSeq
        (lam a. lam b. if nameEq a.0 b.0 then eqSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let eqFollowSymSet = lam s1. lam s2.
      eqSeq (lam a. lam b. eqSpecSymbol a.0 b.0)
        (mapBindings s1)
        (mapBindings s2) in

    let eqFollowSet = lam s1. lam s2.
      eqSeq
        (lam a. lam b. if nameEq a.0 b.0 then eqFollowSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let addProdToFirst : Map Name (SymSet state prodLabel) -> Production prodLabel state -> SymSet state prodLabel -> SymSet state prodLabel =
      lam prev. lam prod. lam symset.
        recursive let work = lam symset: SymSet state prodLabel. lam rhs.
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

    let firstSet : Map Name (SymSet state prodLabel) =
      _iterateUntilFixpoint eqFirstSet
        (lam prev. mapMapWithKey (addNtToFirstSet prev) prev)
        (mapMap (lam. emptySymSet) groupedProds) in

    -- let _ = print "\n\nFirsts:" in
    -- let _ = dprintFirstSet firstSet in

    let firstOfRhs : [SpecSymbol Token TokenRepr state prodLabel] -> SymSet state prodLabel =
      recursive let work = lam symset: SymSet state prodLabel. lam rhs.
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

    let addProdToFollow : Production prodLabel state -> Map Name (Map (SpecSymbol Token TokenRepr state prodLabel) ()) -> Map Name (Map (SpecSymbol Token TokenRepr state prodLabel) ()) = lam prod. lam follow.
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

    let followSet : Map Name (Map (SpecSymbol Token TokenRepr state prodLabel) ()) =
      _iterateUntilFixpoint eqFollowSet
        (lam prev. foldl (lam prev. lam prod. addProdToFollow prod prev) prev productions)
        (mapInsert startNt (mapInsert (TokSpec (EOFRepr ())) () (mapEmpty compareSpecSymbol))
          (mapMap (lam. mapEmpty compareSpecSymbol) groupedProds)) in

    -- let _ = print "\n\nFollows:" in
    -- let _ = dprintFollowSet followSet in

    -- The first `Symbol` should be `ParserBase.Symbol`, the second should be `ParserGenerated.Symbol`
    let emptyTableTarget = ref (mapEmpty compareSpecSymbol) in
    let table : Map Name (Ref (Map (SpecSymbol Token TokenRepr state prodLabel) {syms : [SpecSymbol Token TokenRepr state prodLabel], label: prodLabel, action: Action Token state})) =
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
        (lam binding: (SpecSymbol Token TokenRepr state prodLabel, TableProd prodLabel state).
          match binding with (sym, {label = label}) then
            match mapLookup sym prev with Some prevProd then
              let prevProd: TableProd prodLabel state = prevProd in
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
  sem _dedupSymbolList : all state. all prodLabel. [SpecSymbol Token TokenRepr state prodLabel] -> [SpecSymbol Token TokenRepr state prodLabel]
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
  sem _mkLL1Error
    : all prodLabel. all state. ([SpecSymbol Token TokenRepr state prodLabel] -> SymSet state prodLabel)
    -> Option (Name, ParsedSymbol Token, [FullStackItem prodLabel state])
    -> Option (SpecSymbol Token TokenRepr state prodLabel, ParsedSymbol Token, [FullStackItem prodLabel state])
    -> ParseError Token TokenRepr state prodLabel
  sem _mkLL1Error firstOfRhs openInfo =
  | workInfo ->
    match openInfo with Some (nt, token, stack) then
      UnexpectedFirst
        { nt = nt
        , stack = _sanitizeStack stack
        , found = token
        , expected =
          let here: SymSet state prodLabel = firstOfRhs [NtSpec nt] in
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

  sem parseWithTable
    : all state. all prodLabel. Table prodLabel state
    -> String
    -> state
    -> String
    -> Either (ParseError Token TokenRepr state prodLabel) Dyn
  sem parseWithTable table filename state =
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
      let openNt = lam nt. lam token. lam stack. lam stream.
        modref lastOpen (Some (nt.nt, token, stack));
        let table = deref nt.table in
        match mapLookup (parsedSymToSpecSym token) table with Some r then
          work (snoc stack {seen = [], rest = r.syms, action = r.action, label = r.label}) token stream
        else Left (_mkLL1Error firstOfRhs (deref lastOpen) (None ()))
      let work = lam stack. lam token. lam stream.
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
  sem ll1ToErrorHighlightSpec : all state. all prodLabel.
    ParseError Token TokenRepr state prodLabel
    -> { highlight : [Highlight]
       , found : SpecSymbol Token TokenRepr state prodLabel
       , expected : [SpecSymbol Token TokenRepr state prodLabel]
       , info : Info
       }
  sem ll1ToErrorHighlightSpec =
  | UnexpectedFirst x ->
    let info = symParsedInfo x.found in
    { highlight = highlightsForFound x.found, found = parsedSymToSpecSym x.found, expected = x.expected, info = info }
  | UnexpectedToken x ->
    let info = symParsedInfo x.found in
    { highlight = highlightsForFound x.found, found = parsedSymToSpecSym x.found, expected = [x.expected], info = info }

  sem ll1DefaultHighlight : all prodLabel. all state.
    String
    -> { highlight : [Highlight]
       , found : SpecSymbol Token TokenRepr state prodLabel
       , expected : [SpecSymbol Token TokenRepr state prodLabel]
       , info : Info
       }
     -> (Info, String)
  sem ll1DefaultHighlight content =
  | x ->
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
let nt : Name -> SpecSymbol Token TokenRepr () String  = ntSym in
let lit : String -> SpecSymbol Token TokenRepr () String = litSym in
let lident : SpecSymbol Token TokenRepr () String = tokSym (LIdentRepr ()) in
let uident : SpecSymbol Token TokenRepr () String = tokSym (UIdentRepr ()) in
let int : SpecSymbol Token TokenRepr () String = tokSym (IntRepr ()) in

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

type SymThing in
type Wrapped in
con WThing : Wrapped -> SymThing in
con WTok : Token -> SymThing in
con WLit : {lit: String, info: Info} -> SymThing in
con Wrapped : {label: String, val: [SymThing]} -> Wrapped in
let wrapToDyn : Wrapped -> Dyn = unsafeCoerce in
let dynToWrap : Dyn -> Wrapped = unsafeCoerce in
let psymToSymThing : ParsedSymbol Token -> SymThing = lam x.
  switch x
  case UserSym dyn then WThing (dynToWrap dyn)
  case TokParsed tok then WTok tok
  case LitParsed lit then WLit lit
  end in
let wrap = lam label. lam state: (). lam x. wrapToDyn (Wrapped {label = label, val = map psymToSymThing x}) in

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

utest
  match errorMapToBindingsExc (genParser gFailOnce)
  with [ ( "Declaration"
    , [ ( LitSpec { lit = "let" }
        , [ "decllet" , "declletrec" ]
        )
      ]
    )
  ] then true else false
with true in

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

utest
  match errorMapToBindingsExc (genParser gFailTwice)
  with [ ( "Declaration"
    , [ ( LitSpec { lit = "let" }
        , [ "decllet" , "declletrec" , "declletmut" ]
        )
      ]
    )
  ] then true else false
with true in

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

utest
  match errorMapToBindingsExc (genParser gFailLet)
  with [ ( "ExpressionFollow"
    , [ ( LitSpec { lit = "let" }
        , [ "exprfollowsome" , "exprfollownone" ]
        )
      ]
    )
  ]
  then true else false
with true
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
let parse = lam content. eitherMapRight dynToWrap (parseWithTable table "file" () content) in

utest
  match parse "let a = 1"
  with Right
    ( Wrapped
      { label = "toptop"
      , val =
        [ WThing
          ( Wrapped
            { label = "topdecl"
            , val =
              [ WThing
                (Wrapped
                  { label = "decllet"
                  , val =
                    [ WLit
                      { lit = "let"
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
                      }
                    , WTok
                      ( LIdentTok
                        { val = "a"
                        , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                        }
                      )
                    , WLit
                      { lit = "="
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
                      }
                    , WThing
                      ( Wrapped
                        { label = "exprint"
                        , val =
                          [ WTok
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
        , WThing (Wrapped { label = "topfollownone" , val = [] })
        ]
      }
    )
  then true else false
with true
in

utest
  match parse "let a = 1\nlet b = 4"
  with Right
    ( Wrapped
      { label = "toptop"
      , val =
        [ WThing
          ( Wrapped
            { label = "topdecl"
            , val =
              [ WThing
                ( Wrapped
                  { label = "decllet"
                  , val =
                    [ WLit
                      { lit = "let"
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
                      }
                    , WTok
                      ( LIdentTok
                        { val = "a"
                        , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                        }
                      )
                    , WLit
                      { lit = "="
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
                      }
                    , WThing
                      ( Wrapped
                        { label = "exprint"
                        , val =
                          [ WTok
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
        , WThing
          ( Wrapped
            { label = "topfollowsome"
            , val =
              [ WThing (Wrapped { label = "topinfixjuxt" , val = [] })
              , WThing
                ( Wrapped
                  { label = "topdecl"
                  , val =
                    [ WThing
                      ( Wrapped
                        { label = "decllet"
                        , val =
                          [ WLit
                            { lit = "let"
                            , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 3 , col1 = 0 }
                            }
                          , WTok
                            ( LIdentTok
                              { val = "b"
                              , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 5 , col1 = 4 }
                              }
                            )
                          , WLit
                            { lit = "="
                            , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 7 , col1 = 6 }
                            }
                          , WThing
                            ( Wrapped
                              { label = "exprint"
                              , val =
                                [ WTok
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
              , WThing (Wrapped { label = "topfollownone" , val = [] })
              ]
            }
          )
        ]
      }
    )
  then true else false
with true
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
