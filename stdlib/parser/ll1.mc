-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "lexer.mc"
include "map.mc"
include "string.mc"
include "either.mc"
include "common.mc"

type NonTerminal = String

-- NOTE(vipa, 2021-02-05): I want to create types that refer to
-- `Token`, which lives in a language fragment. There is no top-level
-- `use` (for fairly good reasons), and there is no type-level `use`
-- (just because it hasn't been done yet), so for the moment I create
-- a new language fragment to declare the types
lang ParserBase = Lexer
  syn Symbol =
  | Tok Token
  | Lit {lit: String, info: Info}

  -- NOTE(vipa, 2021-02-08): This should be ParserConcrete.Symbol -> Dyn
  -- type Action = [Symbol] -> Dyn

  sem symToStr =
  | Tok t -> tokToStr t
  | Lit t -> t.lit

  sem symInfo =
  | Tok t -> tokInfo t
  | Lit t -> t.info
end

type Production prodLabel = {nt: NonTerminal, label: prodLabel, rhs: [Symbol], action: Action}
type Grammar prodLabel =
  { start: NonTerminal
  , productions: [Production prodLabel]
  }

lang ParserSpec = ParserBase

  syn Symbol =
  | NtSpec NonTerminal

  sem symToStr =
  | NtSpec n -> n

  sem symInfo =
  | NtSpec _ -> NoInfo ()
end

lang ParserGenerated = ParserBase
  syn Symbol =
  -- NOTE(vipa, 2021-02-08): The `Ref` here is slightly undesirable, but I see no other way to construct a cyclic data structure
  -- NOTE(vipa, 2021-02-08): The first `Symbol` here should be `ParserBase.Symbol`
  | NtSym {nt: NonTerminal, table: (Ref (Map Symbol {syms: [Symbol], action: Action, label: prodLabel}))}

  sem symToStr =
  | NtSym t -> t.nt

  sem symInfo =
  | NtSym _ -> NoInfo ()
end

lang ParserConcrete = ParserBase
  syn Symbol =
  | UserSym Dyn

  sem symToStr =
  | UserSym _ -> "<UserSym>"

  sem symInfo =
  | UserSym _ -> NoInfo ()
end

let _compareSymbol = use ParserBase in lam lsym. lam rsym.
  let pair = (lsym, rsym) in
  match pair with (Tok _, Lit _) then negi 1 else
  match pair with (Lit _, Tok _) then 1 else
  match pair with (Tok a, Tok b) then compareTokKind a b else
  match pair with (Lit {lit = a}, Lit {lit = b}) then cmpString a b else
  dprint pair;
  never

let _eqSymbol = lam a. lam b. eqi (_compareSymbol a b) 0

let _iterateUntilFixpoint : (a -> a -> Bool) -> (a -> a) -> a -> a =
  lam eq. lam f.
    recursive let work = lam a.
      let next = f a in
      if eq a next then a else work next
    in work

type SymSet = {eps: Bool, syms: Map Symbol ()}


-- NOTE(vipa, 2021-02-08): This should be opaque, and the first `Symbol` should be `ParserBase.Symbol`, the second should be `ParserGenerated.Symbol`
type TableProd prodLabel = {syms: [Symbol], label: prodLabel, action: Action}
type Table prodLabel = {start: {nt: NonTerminal, table: (Ref (Map Symbol (TableProd prodLabel)))}, firstOfRhs: [Symbol] -> SymSet, lits: Map String ()}

type FullStackItem prodLabel = {seen: [Symbol], rest: [Symbol], label: prodLabel, action: Action}
type StackItem prodLabel = {seen: [Symbol], rest: [Symbol], label: prodLabel}

type ParseError prodLabel
con UnexpectedFirst : {nt : NonTerminal, stack : [StackItem prodLabel], found : Symbol, expected : [Symbol]} -> ParseError prodLabel
con UnexpectedToken : {stack : [StackItem prodLabel], found : Symbol, expected : Symbol} -> ParseError prodLabel

let _sanitizeStack = use ParserGenerated in use ParserSpec in lam stack.
  let genSymToSym = lam sym.
    match sym with NtSym {nt = nt} then NtSpec nt else sym in
  let work = lam item: FullStackItem prodLabel.
    {seen = item.seen, rest = map genSymToSym item.rest, label = item.label} in
  map work stack

let _expectedFromStack = lam firstOfRhs: [Symbol] -> SymSet.
  recursive let work = lam stack: [FullStackItem prodLabel].
    match stack with stack ++ [{rest = rest}] then
      let res = firstOfRhs rest in
      let here = mapKeys res.syms in
      if res.eps
      then concat here (work stack)
      else here
    else []
  in work

let _dedupSymbolList
  : [Symbol]
  -> [Symbol]
  = recursive
      let work = lam seen. lam retained. lam rest.
        match rest with [] then retained else
        match rest with [sym] ++ rest then
          match mapLookup sym seen with Some _
          then work seen retained rest
          else work (mapInsert sym () seen) (snoc retained sym) rest
        else never
    in work (mapEmpty _compareSymbol) []

let _mkLL1Error
  : ([Symbol] -> SymSet)
  -> Option (NonTerminal, Symbol, [FullStackItem prodLabel])
  -> Option (Symbol, Symbol, [FullStackItem prodLabel])
  -> ParseError prodLabel
  = lam firstOfRhs. lam openInfo. lam workInfo.
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

let ll1ParseWithTable : Table parseLabel -> String -> String -> Either (ParseError parseLabel) Dyn = use ParserGenerated in use ParserConcrete in
  lam table. lam filename. lam contents. match table with {start = start, lits = lits, firstOfRhs = firstOfRhs} then
    let lastOpen = ref (None ()) in
    let getNextToken = lam stream.
      let res: NextTokenResult = nextToken stream in
        -- OPT(vipa, 2021-02-08): Could use the hash of the lit to maybe optimize this, either by using a hashmap, or by first checking against the hash in a bloom filter or something like that
      if if (eqString "" res.lit) then true else not (mapMem res.lit lits)
        then {token = Tok res.token, stream = res.stream}
        else {token = Lit {lit = res.lit, info = res.info}, stream = res.stream} in
    recursive
      let openNt = lam nt: {nt: NonTerminal, table: Unknown}. lam token. lam stack. lam stream.
        modref lastOpen (Some (nt.nt, token, stack));
        let table = deref nt.table in
        match mapLookup token table with Some r then
          let r: {syms: [Symbol], action: Action, label: prodLabel} = r in
          work (snoc stack {seen = [], rest = r.syms, action = r.action, label = r.label}) token stream
        else Left (_mkLL1Error firstOfRhs (deref lastOpen) (None ()))
      let work = lam stack : [FullStackItem prodLabel]. lam token. lam stream.
        match stack with stack ++ [curr & {rest = [NtSym nt] ++ rest}] then
          openNt nt token (snoc stack {curr with rest = rest}) stream
        else match stack with stack ++ [above & {seen = seenAbove}, {seen = seen, rest = [], action = action}] then
          work (snoc stack {above with seen = snoc seenAbove (UserSym (action seen))}) token stream
        else match stack with oldStack & (stack ++ [curr & {rest = [t] ++ rest, seen = seen}]) then
          if _eqSymbol t token then
            modref lastOpen (None ());
            let next = getNextToken stream in
            work (snoc stack {{curr with rest = rest} with seen = snoc seen token}) next.token next.stream
          else Left (_mkLL1Error firstOfRhs (deref lastOpen) (Some (t, token, oldStack)))
        else match stack with [{seen = seen, rest = [], action = action}] then
          match token with Tok (EOFTok _)
            then Right (action seen)
            else Left (_mkLL1Error firstOfRhs (deref lastOpen) (Some (Tok (EOFTok {info = NoInfo ()}), token, stack)))
        else print "ERROR: ";
             dprintLn (stack, token, stream);
             error "Unexpected parse error, this shouldn't happen"
    in
      let stream = {pos = initPos filename, str = contents} in
      match getNextToken stream with {token = token, stream = stream} then
        openNt start token [] stream
      else never
  else never

type GenError prodLabel = Map NonTerminal (Map Symbol [prodLabel])

let ll1GenParser : Grammar prodLabel -> Either (GenError prodLabel) (Table prodLabel) = use ParserSpec in lam grammar.
  match grammar with {productions = productions, start = startNt} then

    let emptySymSet = {eps = false, syms = mapEmpty _compareSymbol} in
    let eqSymSet = lam s1: SymSet. lam s2: SymSet.
      match (s1, s2) with ({eps = e1, syms = s1}, {eps = e2, syms = s2}) then
        and
          (eqBool e1 e2)
          (eqSeq (lam a: (Symbol, ()). lam b: (Symbol, ()). _eqSymbol a.0 b.0)
            (mapBindings s1)
            (mapBindings s2))
      else dprintLn (s1, s2);  never in

    let eqFirstSet = lam s1. lam s2.
      eqSeq
        (lam a: (String, Symbol). lam b: (String, Symbol). if eqString a.0 b.0 then eqSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let eqFollowSymSet = lam s1. lam s2.
      eqSeq (lam a: (Symbol, ()). lam b: (Symbol, ()). _eqSymbol a.0 b.0)
        (mapBindings s1)
        (mapBindings s2) in

    let eqFollowSet = lam s1. lam s2.
      eqSeq
        (lam a: (String, Unknown). lam b: (String, Unknown). if eqString a.0 b.0 then eqFollowSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let addProdToFirst : Map NonTerminal SymSet -> Production -> SymSet -> SymSet =
      lam prev. lam prod. lam symset.
        recursive let work = lam symset: SymSet. lam rhs.
          match rhs with [] then {symset with eps = true}
          else match rhs with [(Tok _ | Lit _) & t] ++ _ then
            {symset with syms = mapInsert t () symset.syms}
          else match rhs with [NtSpec nt] ++ rhs then
            let otherSymset = match mapLookup nt prev
              with Some s then s
              else {eps = false, syms = mapEmpty _compareSymbol} in
            let symset = {symset with syms = mapUnion symset.syms otherSymset.syms} in
            if otherSymset.eps then work symset rhs else symset
          else never
        in work symset prod.rhs in

    let groupedProds : Map NonTerminal [Production] =
      foldl
        (lam acc. lam prod: Production. mapInsert prod.nt (snoc (optionGetOr [] (mapLookup prod.nt acc)) prod) acc)
        (mapEmpty cmpString)
        productions in

    let addNtToFirstSet = lam prev. lam nt. lam symset.
      let prods = mapFindWithExn nt groupedProds in
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

    let firstSet : Map NonTerminal SymSet =
      _iterateUntilFixpoint eqFirstSet
        (lam prev. mapMapWithKey (addNtToFirstSet prev) prev)
        (mapMap (lam. emptySymSet) groupedProds) in

    -- let _ = print "\n\nFirsts:" in
    -- let _ = dprintFirstSet firstSet in

    let firstOfRhs : [Symbol] -> SymSet =
      recursive let work = lam symset: SymSet. lam rhs.
        -- NOTE(vipa, 2021-06-18): This will be called post generation
        -- as well, so it needs to handle NtSym, even thought it'll
        -- not be relevant when generating the table
        use ParserGenerated in
        match rhs with [] then {symset with eps = true}
        else match rhs with [(Tok _ | Lit _) & t] ++ _ then
          {symset with syms = mapInsert t () symset.syms}
        else match rhs with [NtSpec nt | NtSym {nt = nt}] ++ rhs then
          let otherSymset = match mapLookup nt firstSet
            with Some s then s
            else emptySymSet in
          let symset = {symset with syms = mapUnion symset.syms otherSymset.syms} in
          if otherSymset.eps then work symset rhs else symset
        else never
      in work {eps = false, syms = mapEmpty _compareSymbol} in

    let addProdToFollow : Production -> Map NonTerminal (Map Symbol ()) -> Map NonTerminal (Map Symbol ()) = lam prod. lam follow.
      match prod with {nt = prodNt, rhs = rhs} then
        recursive let work = lam follow. lam rhs.
          match rhs with [] then follow
          else match rhs with [NtSpec nt] ++ rhs then
            let ntFollow = match mapLookup nt follow
              with Some s then s
              else mapEmpty _compareSymbol in
            let otherSymset = firstOfRhs rhs in
            let ntFollow = mapUnion ntFollow otherSymset.syms in
            let ntFollow = if otherSymset.eps
              then mapUnion ntFollow (mapFindWithExn prodNt follow)
              else ntFollow in
            work (mapInsert nt ntFollow follow) rhs
          else match rhs with [_] ++ rhs then
            work follow rhs
          else never
        in work follow rhs
      else never in

    let followSet : Map NonTerminal (Map Symbol ()) =
      _iterateUntilFixpoint eqFollowSet
        (lam prev. foldl (lam prev. lam prod. addProdToFollow prod prev) prev productions)
        (mapInsert startNt (mapInsert (Tok (EOFTok {info = NoInfo ()})) () (mapEmpty _compareSymbol))
          (mapMap (lam. mapEmpty _compareSymbol) groupedProds)) in

    -- let _ = print "\n\nFollows:" in
    -- let _ = dprintFollowSet followSet in

    -- The first `Symbol` should be `ParserBase.Symbol`, the second should be `ParserGenerated.Symbol`
    let emptyTableTarget = ref (mapEmpty _compareSymbol) in
    let table : Map NonTerminal (Ref (Map Symbol {syms : [Symbol], action: Action})) =
      mapMap (lam. ref (mapEmpty _compareSymbol)) groupedProds in

    use ParserGenerated in

    let specSymToGenSym = lam sym.
      match sym with NtSpec nt
      then NtSym {nt = nt, table = optionGetOr emptyTableTarget (mapLookup nt table)}
      else sym
    in

    let hasLl1Error = ref false in
    let ll1Errors = mapMap (lam. ref (mapEmpty _compareSymbol)) groupedProds in

    let addProdToTable = lam prod: Production.
      let tableRef = mapFindWithExn prod.nt table in
      let prev = deref tableRef in
      let firstSymset = firstOfRhs prod.rhs in
      let symset = if firstSymset.eps
        then mapUnion firstSymset.syms (mapFindWithExn prod.nt followSet)
        else firstSymset.syms in
      let newProd = {action = prod.action, label = prod.label, syms = map specSymToGenSym prod.rhs} in
      let tableAdditions = mapMap (lam. newProd) symset in
      for_ (mapBindings tableAdditions)
        (lam binding: (Symbol, TableProd prodLabel).
          match binding with (sym, {label = label}) then
            match mapLookup sym prev with Some prevProd then
              let prevProd: TableProd prodLabel = prevProd in
              modref hasLl1Error true;
              let errRef = mapFindWithExn prod.nt ll1Errors in
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
      match sym with Lit {lit = lit}
        then mapInsert lit () lits
        else lits in
    let lits = foldl
      (lam acc. lam prod: Production. foldl addLitToLits acc prod.rhs)
      (mapEmpty cmpString)
      productions in

    -- let dprintTablePair = lam nt. lam actions.
    --   dprintLn (nt, mapBindings (deref actions))
    -- in
    -- printLn "\n\nParse table:";
    -- mapMapWithKey dprintTablePair table;

    if deref hasLl1Error
      then Left (mapFromSeq cmpString (filter (lam binding: (Unknown, Unknown). not (null (mapBindings binding.1))) (mapBindings (mapMap deref ll1Errors))))
      else Right {start = {nt = startNt, table = mapFindWithExn startNt table}, firstOfRhs = firstOfRhs, lits = lits}
  else never

let ll1NonTerminal : String -> NonTerminal = identity

let ll1Nt : NonTerminal -> Symbol = use ParserSpec in lam nt. NtSpec nt
let ll1Lit : String -> Symbol = use ParserSpec in lam str.
  let res: NextTokenResult = nextToken {str = str, pos = posVal "" 1 1} in
  match (res.stream.str, res.lit) with ([], ![]) then Lit {lit = str, info = NoInfo ()}
  else error (join ["A literal token does not lex as a single token: \"", res.stream.str, "\""])
let ll1LIdent : Symbol = use ParserSpec in Tok (LIdentTok {val = "", info = NoInfo ()})
let ll1UIdent : Symbol = use ParserSpec in Tok (UIdentTok {val = "", info = NoInfo ()})
let ll1Int : Symbol = use ParserSpec in Tok (IntTok {val = 0, info = NoInfo ()})
let ll1Float : Symbol = use ParserSpec in Tok (FloatTok {val = 0.0, info = NoInfo ()})
let ll1Operator : Symbol = use ParserSpec in Tok (OperatorTok {val = "", info = NoInfo ()})
let ll1LParen : Symbol = use ParserSpec in Tok (LParenTok {info = NoInfo ()})
let ll1RParen = use ParserSpec in Tok (RParenTok {info = NoInfo ()})
let ll1LBracket = use ParserSpec in Tok (LBracketTok {info = NoInfo ()})
let ll1RBracket = use ParserSpec in Tok (RBracketTok {info = NoInfo ()})
let ll1LBrace = use ParserSpec in Tok (LBraceTok {info = NoInfo ()})
let ll1RBrace = use ParserSpec in Tok (RBraceTok {info = NoInfo ()})
let ll1Semi = use ParserSpec in Tok (SemiTok {info = NoInfo ()})
let ll1Comma = use ParserSpec in Tok (CommaTok {info = NoInfo ()})
let ll1String = use ParserSpec in Tok (StringTok {val = "", info = NoInfo ()})
let ll1Char = use ParserSpec in Tok (CharTok {val = ' ', info = NoInfo ()})
let ll1HashString = use ParserSpec in
  lam hash. Tok (HashStringTok {val = "", hash = hash, info = NoInfo ()})

mexpr

use ParserSpec in

let genParser = ll1GenParser in
let parseWithTable = ll1ParseWithTable in

let nonTerminal = ll1NonTerminal in
let nt = ll1Nt in
let lit = ll1Lit in
let lident = ll1LIdent in
let uident = ll1UIdent in
let int = ll1Int in

let errorMapToBindingsExc = lam m.
  match m with Left m then
    mapBindings (mapMap mapBindings m)
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
con Wrapped : {label: String, val: [Symbol]} -> Wrapped in
let wrap = lam label. lam x. Wrapped {label = label, val = x} in

let gFailOnce : Grammar String =
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
  , [ ( ParserBase_Lit { lit = "let", info = NoInfo () }
      , [ "decllet" , "declletrec" ]
      )
    ]
  )
]
in

let gFailTwice : Grammar String =
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
  , [ ( ParserBase_Lit { lit = "let", info = NoInfo () }
      , [ "decllet" , "declletrec" , "declletmut" ]
      )
    ]
  )
]
in

let gFailLet : Grammar String =
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
  , [ ( ParserBase_Lit { lit = "let", info = NoInfo () }
      , [ "exprfollowsome" , "exprfollownone" ]
      )
    ]
  )
]
in

let g : Grammar String =
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
let parse = parseWithTable table "file" in

utest parse "let a = 1"
with Right
  ( Wrapped
    { label = "toptop"
    , val =
      [ ParserConcrete_UserSym
        ( Wrapped
          { label = "topdecl"
          , val =
            [ ParserConcrete_UserSym
              (Wrapped
                { label = "decllet"
                , val =
                  [ ParserBase_Lit
                    { lit = "let"
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
                    }
                  , ParserBase_Tok
                    ( LIdentTokenParser_LIdentTok
                      { val = "a"
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                      }
                    )
                  , ParserBase_Lit
                    { lit = "="
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
                    }
                  , ParserConcrete_UserSym
                    ( Wrapped
                      { label = "exprint"
                      , val =
                        [ ParserBase_Tok
                          ( UIntTokenParser_IntTok
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
      , ParserConcrete_UserSym (Wrapped { label = "topfollownone" , val = [] })
      ]
    }
  )
in

utest parse "let a = 1\nlet b = 4"
with Right
  ( Wrapped
    { label = "toptop"
    , val =
      [ ParserConcrete_UserSym
        ( Wrapped
          { label = "topdecl"
          , val =
            [ ParserConcrete_UserSym
              ( Wrapped
                { label = "decllet"
                , val =
                  [ ParserBase_Lit
                    { lit = "let"
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
                    }
                  , ParserBase_Tok
                    ( LIdentTokenParser_LIdentTok
                      { val = "a"
                      , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                      }
                    )
                  , ParserBase_Lit
                    { lit = "="
                    , info = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
                    }
                  , ParserConcrete_UserSym
                    ( Wrapped
                      { label = "exprint"
                      , val =
                        [ ParserBase_Tok
                          ( UIntTokenParser_IntTok
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
      , ParserConcrete_UserSym
        ( Wrapped
          { label = "topfollowsome"
          , val =
            [ ParserConcrete_UserSym (Wrapped { label = "topinfixjuxt" , val = [] })
            , ParserConcrete_UserSym
              ( Wrapped
                { label = "topdecl"
                , val =
                  [ ParserConcrete_UserSym
                    ( Wrapped
                      { label = "decllet"
                      , val =
                        [ ParserBase_Lit
                          { lit = "let"
                          , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 3 , col1 = 0 }
                          }
                        , ParserBase_Tok
                          ( LIdentTokenParser_LIdentTok
                            { val = "b"
                            , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 5 , col1 = 4 }
                            }
                          )
                        , ParserBase_Lit
                          { lit = "="
                          , info = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 7 , col1 = 6 }
                          }
                        , ParserConcrete_UserSym
                          ( Wrapped
                            { label = "exprint"
                            , val =
                              [ ParserBase_Tok
                                ( UIntTokenParser_IntTok
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
            , ParserConcrete_UserSym (Wrapped { label = "topfollownone" , val = [] })
            ]
          }
        )
      ]
    }
  )
in

utest parse "let"
with Left (UnexpectedToken
  { expected = (ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),info = (NoInfo ())}))
  , stack = (
    [ {label = ("toptop"),seen = ([]),rest = ([(ParserSpec_NtSpec ("FileFollow"))])}
    , {label = ("topdecl"),seen = ([]),rest = ([])}
    , { label = ("decllet")
      , seen = ([(ParserBase_Lit {lit = ("let"),info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 0})})])
      , rest = ([(ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),info = (NoInfo ())})),(ParserBase_Lit {lit = ("="), info = NoInfo ()}),(ParserSpec_NtSpec ("Expression"))])
      }
    ])
  , found = (ParserBase_Tok (EOFTokenParser_EOFTok {info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 3})}))
  })
in

utest parse "let x ="
with Left (UnexpectedFirst
  { expected =
    [ Tok (IntTok {info = NoInfo (), val = 0})
    ]
  , stack =
    [ { label = "toptop" , seen = [] , rest = [NtSpec "FileFollow"]}
    , { label = "topdecl" , seen = [] , rest = []}
    , { label = "decllet"
      , seen =
        [ Lit {info = Info {filename = "file", row2 = 1,row1 = 1, col2 = 3,col1 = 0} , lit = "let"}
        , Tok (LIdentTok {info = Info {filename = "file", row2 = 1,row1 = 1, col2 = 5,col1 = 4} , val = "x"})
        , Lit {info = Info {filename = "file", row2 = 1,row1 = 1, col2 = 7,col1 = 6} , lit = "="}
        ]
      , rest = ([])
      }
    ]
  , found = Tok (EOFTok {info = (Info {filename = "file",row2 = 1,row1 = 1, col2 = 7,col1 = 7})}
    )
  , nt = "Expression"
  })
in

utest parse "let let = 4"
with Left (UnexpectedToken
  { expected = (ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),info = (NoInfo ())}))
  , stack = (
    [ {label = ("toptop"),seen = ([]),rest = ([(ParserSpec_NtSpec ("FileFollow"))])}
    , {label = ("topdecl"),seen = ([]),rest = ([])}
    , { label = ("decllet")
      , seen = ([(ParserBase_Lit {lit = ("let"),info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 0})})])
      , rest = ([(ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),info = (NoInfo ())})),(ParserBase_Lit {lit = ("="), info = NoInfo ()}),(ParserSpec_NtSpec ("Expression"))])
      }
    ])
  , found = (ParserBase_Lit {lit = ("let"),info = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 7,col1 = 4})})
  })
in

()
