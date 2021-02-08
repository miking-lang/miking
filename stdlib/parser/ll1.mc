include "lexer.mc"
include "map.mc"
include "string.mc"
include "hashmap.mc"

type NonTerminal = String

-- NOTE(vipa, 2021-02-05): I want to create types that refer to
-- `Token`, which lives in a language fragment. There is no top-level
-- `use` (for fairly good reasons), and there is no type-level `use`
-- (just because it hasn't been done yet), so for the moment I create
-- a new language fragment to declare the types
lang ParserBase = Lexer
  syn Symbol =
  | Tok Token
  | Lit {hash: Int, lit: String}

  -- NOTE(vipa, 2021-02-08): This should be ParserConcrete.Symbol -> Dyn
  -- type Action = [Symbol] -> Dyn
end

lang ParserSpec = ParserBase
  -- type Production = {nt: NonTerminal, rhs: [Symbol], action: Action}
  -- type Grammar =
  --   { start: NonTerminal
  --   , productions: [Production]
  --   }

  syn Symbol =
  | NtSpec NonTerminal
end

lang ParserGenerated = ParserBase
  syn Symbol =
  -- NOTE(vipa, 2021-02-08): The `Ref` here is slightly undesirable, but I see no other way to construct a cyclic data structure
  -- NOTE(vipa, 2021-02-08): The first `Symbol` here should be `ParserBase.Symbol`
  | NtSym (Ref (Map Symbol {syms: [Symbol], action: Action}))
end

lang ParserConcrete = ParserBase
  syn Symbol =
  | UserSym Dyn
end

let _compareSymbol = use ParserBase in lam lsym. lam rsym.
  let pair = (lsym, rsym) in
  match pair with (Tok _, Lit _) then negi 1 else
  match pair with (Lit _, Tok _) then 1 else
  match pair with (Tok a, Tok b) then compareTokKind a b else
  match pair with (Lit {lit = a}, Lit {lit = b}) then cmpString a b else
  let _ = dprint pair in
  never

let _eqSymbol = lam a. lam b. eqi (_compareSymbol a b) 0

let _hashStr : String -> Int = hashmapStrTraits.hashfn

let _iterateUntilFixpoint : (a -> a -> Bool) -> (a -> a) -> a -> a =
  lam eq. lam f.
    recursive let work = lam a.
      let next = f a in
      if eq a next then a else work next
    in work

-- NOTE(vipa, 2021-02-08): This should be opaque, and the first `Symbol` should be `ParserBase.Symbol`, the second should be `ParserGenerated.Symbol`
type Table = {start: Map Symbol {syms: [Symbol], action: Action}, lits: Map String ()}

let dprintLn = lam x. let _ = dprint x in printLn ""

let parseWithTable : Table -> String -> String -> Dyn = use ParserGenerated in use ParserConcrete in
  lam table. lam filename. lam contents. match table with {start = start, lits = lits} then
    let openNt = lam table. lam token.
      match mapLookup token table with Some {syms = rest, action = action} then
        {seen = [], rest = rest, action = action}
      else let _ = dprintLn token in error "Unexpected token" in
    -- TODO(vipa, 2021-02-08): handle `Lit`s properly
    let getNextToken = lam stream.
      match nextToken stream with {token = token, lit = lit, stream = stream} then
        -- OPT(vipa, 2021-02-08): Could use the hash of the lit to maybe optimize this, either by using a hashmap, or by first checking against the hash in a bloom filter or something like that
        if if (eqString "" lit) then true else not (mapMem lit lits)
          then {token = Tok token, stream = stream}
          else {token = Lit {hash = _hashStr lit, lit = lit}, stream = stream}
      else never in
    recursive let work = lam stack : [{seen: Symbol, rest: Symbol, action: Action}]. lam token. lam stream.
      match stack with stack ++ [curr & {rest = [NtSym tabRef] ++ rest}] then
        work (snoc (snoc stack {curr with rest = rest}) (openNt (deref tabRef) token)) token stream
      else match stack with stack ++ [above & {seen = seenAbove}, {seen = seen, rest = [], action = action}] then
        work (snoc stack {above with seen = snoc seenAbove (UserSym (action seen))}) token stream
      else match stack with stack ++ [curr & {rest = [t] ++ rest, seen = seen}] then
        if _eqSymbol t token then
          let next = getNextToken stream in
          work (snoc stack {{curr with rest = rest} with seen = snoc seen token}) next.token next.stream
        else let _ = dprintLn (t, token) in error "Wrong token"
      else match (stack, token) with ([{seen = seen, rest = [], action = action}], Tok (EOFTok _)) then
        action seen
      else let _ = print "ERROR: " in let _ = dprintLn (stack, token, stream) in error "Failed to parse stuff"
    in
      let stream = {pos = initPos filename, str = contents} in
      match getNextToken stream with {token = token, stream = stream} then
        work [openNt start token] token stream
      else never
  else never

let genParser : Grammar -> Table = use ParserSpec in lam grammar.
  match grammar with {productions = productions, start = startNt} then
    type SymSet = {eps: Bool, syms: Map Symbol ()} in

    let eqSymSet = lam s1. lam s2.
      match (s1, s2) with ({eps = e1, syms = s1}, {eps = e2, syms = s2}) then
        and (eqBool e1 e2) (eqSeq (lam a. lam b. _eqSymbol a.0 b.0) (mapBindings s1) (mapBindings s2))
      else let _ = dprintLn (s1, s2) in never in

    let eqFirstSet = lam s1. lam s2.
      eqSeq
        (lam a. lam b. if eqString a.0 b.0 then eqSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let eqFollowSymSet = lam s1. lam s2.
      eqSeq (lam a. lam b. _eqSymbol a.0 b.0) (mapBindings s1) (mapBindings s2) in

    let eqFollowSet = lam s1. lam s2.
      eqSeq
        (lam a. lam b. if eqString a.0 b.0 then eqFollowSymSet a.1 b.1 else false)
        (mapBindings s1)
        (mapBindings s2) in

    let addProdToFirst : Map NonTerminal SymSet -> Production -> SymSet -> SymSet =
      lam prev. lam prod. lam symset.
        recursive let work = lam symset. lam rhs.
          match rhs with [] then {symset with eps = true}
          else match rhs with [(Tok _ | Lit _) & t] ++ _ then
            {symset with syms = mapInsert t () symset.syms}
          else match rhs with [NtSpec nt] ++ rhs then
            let otherSymset = mapFind nt prev in
            let symset = {symset with syms = mapUnion symset.syms otherSymset.syms} in
            if otherSymset.eps then work symset rhs else symset
          else never
        in work symset prod.rhs in

    let groupedProds : Map NonTerminal [Production] =
      foldl
        (lam acc. lam prod. mapInsert prod.nt (snoc (optionGetOr [] (mapLookup prod.nt acc)) prod) acc)
        (mapEmpty cmpString)
        productions in

    let addNtToFirstSet = lam prev. lam nt. lam symset.
      let prods = mapFind nt groupedProds in
      foldl (lam symset. lam prod. addProdToFirst prev prod symset) symset prods in

    let dprintFirstSet = lam firstSet.
      let _ = printLn "" in
      let _ = dprint (mapBindings (mapMap (lam symset. {symset with syms = mapBindings symset.syms}) firstSet)) in
      let _ = printLn "" in
      firstSet in

    let dprintFollowSet = lam followSet.
      let _ = printLn "" in
      let _ = dprint (mapBindings (mapMap mapBindings followSet)) in
      let _ = printLn "" in
      followSet in

    let firstSet : Map NonTerminal SymSet =
      _iterateUntilFixpoint eqFirstSet
        (lam prev. mapMapWithKey (addNtToFirstSet prev) prev)
        (mapMap (lam _. {eps = false, syms = mapEmpty _compareSymbol}) groupedProds) in

    let _ = print "\n\nFirsts:" in
    let _ = dprintFirstSet firstSet in

    let firstOfRhs : [Symbol] -> SymSet =
      recursive let work = lam symset. lam rhs.
        match rhs with [] then {symset with eps = true}
        else match rhs with [(Tok _ | Lit _) & t] ++ _ then
          {symset with syms = mapInsert t () symset.syms}
        else match rhs with [NtSpec nt] ++ rhs then
          let otherSymset = mapFind nt firstSet in
          let symset = {symset with syms = mapUnion symset.syms otherSymset.syms} in
          if otherSymset.eps then work symset rhs else symset
        else never
      in work {eps = false, syms = mapEmpty _compareSymbol} in

    let addProdToFollow : Production -> Map NonTerminal (Map Symbol ()) -> Map NonTerminal (Map Symbol ()) = lam prod. lam follow.
      match prod with {nt = prodNt, rhs = rhs} then
        recursive let work = lam follow. lam rhs.
          match rhs with [] then follow
          else match rhs with [NtSpec nt] ++ rhs then
            let ntFollow = mapFind nt follow in
            let otherSymset = firstOfRhs rhs in
            let ntFollow = mapUnion ntFollow otherSymset.syms in
            let ntFollow = if otherSymset.eps
              then mapUnion ntFollow (mapFind prodNt follow)
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
        (mapInsert startNt (mapInsert (Tok (EOFTok {fi = NoInfo ()})) () (mapEmpty _compareSymbol))
          (mapMap (lam _. mapEmpty _compareSymbol) groupedProds)) in

    let _ = print "\n\nFollows:" in
    let _ = dprintFollowSet followSet in

    -- The first `Symbol` should be `ParserBase.Symbol`, the second should be `ParserGenerated.Symbol`
    let table : Map NonTerminal (Ref (Map Symbol {syms : [Symbol], action: Action})) =
      mapMap (lam _. ref (mapEmpty _compareSymbol)) groupedProds in

    -- NOTE(vipa, 2021-02-08): This should possibly be in the stdlib, but it might depend on opinions on side effects down the line
    recursive let iter = lam f. lam xs.
      match xs with [x] ++ xs then
        let _ = f x in iter f xs
      else match xs with [] then
        ()
      else never in

    use ParserGenerated in

    let specSymToGenSym = lam sym.
      match sym with NtSpec nt then NtSym (mapFind nt table) else sym in

    let addProdToTable = lam prod. match prod with {nt = prodNt, rhs = rhs, action = action} then
      let tableRef = mapFind prodNt table in
      let prev = deref tableRef in
      let firstSymset = firstOfRhs rhs in
      let symset = if firstSymset.eps
        then mapUnion firstSymset.syms (mapFind prodNt followSet)
        else firstSymset.syms in
      let newProd = {action = action, syms = map specSymToGenSym rhs} in
      let tableAdditions = mapMap (lam _. newProd) symset in
      -- TODO(vipa, 2021-02-08): This will silently discard duplicate actions, i.e., if the grammar isn't LL(1) this will just silently ignore that
      modref tableRef (mapUnion prev tableAdditions)
    else never in

    let _ = iter addProdToTable productions in

    let addLitToLits = lam lits. lam sym.
      match sym with Lit {lit = lit}
        then mapInsert lit () lits
        else lits in
    let lits = foldl
      (lam acc. lam prod. foldl addLitToLits acc prod.rhs)
      (mapEmpty cmpString)
      productions in

    let dprintTablePair = lam nt. lam actions.
      dprintLn (nt, mapBindings (deref actions))
    in
    let _ = printLn "\n\nParse table:" in
    let _ = mapMapWithKey dprintTablePair table in

    {start = deref (mapFind startNt table), lits = lits}
  else never

let nonTerminal : String -> NonTerminal = identity

let nt : NonTerminal -> Symbol = use ParserSpec in lam nt. NtSpec nt
let lit : String -> Symbol = use ParserSpec in lam str.
  match nextToken {str = str, pos = posVal "" 1 1} with {lit = lit, stream = {str = unlexed}} then
    match (unlexed, lit) with ([], ![]) then Lit {hash = _hashStr str, lit = str}
    else error (join ["A literal token does not lex as a single token: \"", str, "\""])
  else never
let lident : Symbol = use ParserSpec in Tok (LIdentTok {val = "", fi = NoInfo ()})
let uident : Symbol = use ParserSpec in Tok (UIdentTok {val = "", fi = NoInfo ()})
let int : Symbol = use ParserSpec in Tok (IntTok {val = 0, fi = NoInfo ()})

mexpr

use ParserSpec in

let top = nonTerminal "File" in
let topAtom = nonTerminal "FileAtom" in
let topInfix = nonTerminal "FileInfix" in
let topFollow = nonTerminal "FileFollow" in
let decl = nonTerminal "Declaration" in
let expr = nonTerminal "Expression" in

let g =
  { start = top
  , productions =
    [ {nt = top, rhs = [nt topAtom, nt topFollow], action = identity}
    , {nt = topAtom, rhs = [nt decl], action = identity}
    , {nt = topFollow, rhs = [nt topInfix, nt topAtom, nt topFollow], action = identity}
    , {nt = topFollow, rhs = [], action = identity}
    , {nt = topInfix, rhs = [], action = identity}
    , {nt = decl, rhs = [lit "let", lident, lit "=", nt expr], action = identity}
    , {nt = expr, rhs = [int], action = identity}
    ]
  } in

let table = genParser g in
let res = parseWithTable table "file" "let a = 1" in
let _ = printLn "\n\nParse result:" in
let _ = dprintLn res in

()
