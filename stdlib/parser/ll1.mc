include "lexer.mc"
include "map.mc"
include "string.mc"
include "either.mc"

type NonTerminal = String

-- NOTE(vipa, 2021-02-05): I want to create types that refer to
-- `Token`, which lives in a language fragment. There is no top-level
-- `use` (for fairly good reasons), and there is no type-level `use`
-- (just because it hasn't been done yet), so for the moment I create
-- a new language fragment to declare the types
lang ParserBase = Lexer
  syn Symbol =
  | Tok Token
  | Lit {lit: String, fi: Info}

  -- NOTE(vipa, 2021-02-08): This should be ParserConcrete.Symbol -> Dyn
  -- type Action = [Symbol] -> Dyn
end

lang ParserSpec = ParserBase
  -- type Production prodLabel = {nt: NonTerminal, label: prodLabel, rhs: [Symbol], action: Action}
  -- type Grammar prodLabel =
  --   { start: NonTerminal
  --   , productions: [Production prodLabel]
  --   }

  syn Symbol =
  | NtSpec NonTerminal
end

lang ParserGenerated = ParserBase
  syn Symbol =
  -- NOTE(vipa, 2021-02-08): The `Ref` here is slightly undesirable, but I see no other way to construct a cyclic data structure
  -- NOTE(vipa, 2021-02-08): The first `Symbol` here should be `ParserBase.Symbol`
  | NtSym {nt: NonTerminal, table: (Ref (Map Symbol {syms: [Symbol], action: Action}))}
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

let _iterateUntilFixpoint : (a -> a -> Bool) -> (a -> a) -> a -> a =
  lam eq. lam f.
    recursive let work = lam a.
      let next = f a in
      if eq a next then a else work next
    in work

-- NOTE(vipa, 2021-02-08): This should be opaque, and the first `Symbol` should be `ParserBase.Symbol`, the second should be `ParserGenerated.Symbol`
type Table prodLabel = {start: {nt: NonTerminal, table: (Ref (Map Symbol {syms: [Symbol], label: prodLabel, action: Action}))}, lits: Map String ()}

let dprintLn = lam x. let _ = dprint x in printLn ""

type StackItem prodLabel = {seen: [Symbol], rest: [Symbol], label: String}

type ParseError prodLabel
con UnexpectedFirst : {nt : NonTerminal, stack : [StackItem prodLabel], found : Symbol, expected : [Symbol]} -> ParseError prodLabel
con UnexpectedToken : {stack : [StackItem prodLabel], found : Symbol, expected : Symbol} -> ParseError prodLabel

let _sanitizeStack = use ParserGenerated in use ParserSpec in lam stack.
  let genSymToSym = lam sym.
    match sym with NtSym {nt = nt} then NtSpec nt else sym in
  let work = lam item.
    {seen = item.seen, rest = map genSymToSym item.rest, label = item.label} in
  map work stack

let parseWithTable : Table parseLabel -> String -> String -> Either (ParseError parseLabel) Dyn = use ParserGenerated in use ParserConcrete in
  lam table. lam filename. lam contents. match table with {start = start, lits = lits} then
    let getNextToken = lam stream.
      match nextToken stream with {token = token, lit = lit, info = info, stream = stream} then
        -- OPT(vipa, 2021-02-08): Could use the hash of the lit to maybe optimize this, either by using a hashmap, or by first checking against the hash in a bloom filter or something like that
        if if (eqString "" lit) then true else not (mapMem lit lits)
          then {token = Tok token, stream = stream}
          else {token = Lit {lit = lit, fi = info }, stream = stream}
      else never in
    recursive
      let openNt = lam nt. lam token. lam stack. lam stream.
        match nt with {nt = nt, table = table} then
          let table = deref table in
          match mapLookup token table with Some {syms = rest, action = action, label = label} then
            work (snoc stack {seen = [], rest = rest, action = action, label = label}) token stream
          else Left (UnexpectedFirst
            { nt = nt
            , stack = _sanitizeStack stack
            , found = token
            , expected = map (lam x. x.0) (mapBindings table)
            })
        else let _ = dprint nt in never
      let work = lam stack : [{seen: Symbol, rest: Symbol, action: Action}]. lam token. lam stream.
        match stack with stack ++ [curr & {rest = [NtSym nt] ++ rest}] then
          openNt nt token (snoc stack {curr with rest = rest}) stream
        else match stack with stack ++ [above & {seen = seenAbove}, {seen = seen, rest = [], action = action}] then
          work (snoc stack {above with seen = snoc seenAbove (UserSym (action seen))}) token stream
        else match stack with oldStack & (stack ++ [curr & {rest = [t] ++ rest, seen = seen}]) then
          if _eqSymbol t token then
            let next = getNextToken stream in
            work (snoc stack {{curr with rest = rest} with seen = snoc seen token}) next.token next.stream
          else Left (UnexpectedToken
            { stack = _sanitizeStack oldStack
            , found = token
            , expected = t
            })
        else match stack with [{seen = seen, rest = [], action = action}] then
          match token with Tok (EOFTok _)
            then Right (action seen)
            else Left (UnexpectedToken
              { stack = _sanitizeStack stack
              , found = token
              , expected = Tok (EOFTok (NoInfo ()))
              })
        else let _ = print "ERROR: " in let _ = dprintLn (stack, token, stream) in error "Unexpected parse error, this shouldn't happen"
    in
      let stream = {pos = initPos filename, str = contents} in
      match getNextToken stream with {token = token, stream = stream} then
        openNt start token [] stream
      else never
  else never

let genParser : Grammar prodLabel -> Table prodLabel = use ParserSpec in lam grammar.
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
      match sym with NtSpec nt then NtSym {nt = nt, table = (mapFind nt table)} else sym in

    let addProdToTable = lam prod. match prod with {nt = prodNt, label = label, rhs = rhs, action = action} then
      let tableRef = mapFind prodNt table in
      let prev = deref tableRef in
      let firstSymset = firstOfRhs rhs in
      let symset = if firstSymset.eps
        then mapUnion firstSymset.syms (mapFind prodNt followSet)
        else firstSymset.syms in
      let newProd = {action = action, label = label, syms = map specSymToGenSym rhs} in
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

    {start = {nt = startNt, table = mapFind startNt table}, lits = lits}
  else never

let nonTerminal : String -> NonTerminal = identity

let nt : NonTerminal -> Symbol = use ParserSpec in lam nt. NtSpec nt
let lit : String -> Symbol = use ParserSpec in lam str.
  match nextToken {str = str, pos = posVal "" 1 1} with {lit = lit, stream = {str = unlexed}} then
    match (unlexed, lit) with ([], ![]) then Lit {lit = str}
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

let wrap = lam label. lam x. {label = label, val = x} in

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

let table = genParser g in
let parse = parseWithTable table "file" in
utest parse "let a = 1"
with Right
  { label = "toptop"
  , val =
    [ ParserConcrete_UserSym
      { label = "topdecl"
      , val =
        [ ParserConcrete_UserSym
          { label = "decllet"
          , val =
            [ ParserBase_Lit
              { lit = "let"
              , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
              }
            , ParserBase_Tok
              ( LIdentTokenParser_LIdentTok
                { val = "a"
                , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                }
              )
            , ParserBase_Lit
              { lit = "="
              , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
              }
            , ParserConcrete_UserSym
              { label = "exprint"
              , val =
                [ ParserBase_Tok
                  ( UIntTokenParser_IntTok
                    { val = 1
                    , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 9 , col1 = 8 }
                    }
                  )
                ]
              }
            ]
          }
        ]
      }
    , ParserConcrete_UserSym { label = "topfollownone" , val = [] }
    ]
  }

in

utest parse "let a = 1\nlet b = 4"
with Right
  { label = "toptop"
  , val =
    [ ParserConcrete_UserSym
      { label = "topdecl"
      , val =
        [ ParserConcrete_UserSym
          { label = "decllet"
          , val =
            [ ParserBase_Lit
              { lit = "let"
              , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 3 , col1 = 0 }
              }
            , ParserBase_Tok
              ( LIdentTokenParser_LIdentTok
                { val = "a"
                , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 5 , col1 = 4 }
                }
              )
            , ParserBase_Lit
              { lit = "="
              , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 7 , col1 = 6 }
              }
            , ParserConcrete_UserSym
              { label = "exprint"
              , val =
                [ ParserBase_Tok
                  ( UIntTokenParser_IntTok
                    { val = 1
                    , fi = Info { filename = "file" , row2 = 1 , row1 = 1 , col2 = 9 , col1 = 8 }
                    }
                  )
                ]
              }
            ]
          }
        ]
      }
    , ParserConcrete_UserSym
      { label = "topfollowsome"
      , val =
        [ ParserConcrete_UserSym { label = "topinfixjuxt" , val = [] }
        , ParserConcrete_UserSym
          { label = "topdecl"
          , val =
            [ ParserConcrete_UserSym
              { label = "decllet"
              , val =
                [ ParserBase_Lit
                  { lit = "let"
                  , fi = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 3 , col1 = 0 }
                  }
                , ParserBase_Tok
                  ( LIdentTokenParser_LIdentTok
                    { val = "b"
                    , fi = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 5 , col1 = 4 }
                    }
                  )
                , ParserBase_Lit
                  { lit = "="
                  , fi = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 7 , col1 = 6 }
                  }
                , ParserConcrete_UserSym
                  { label = "exprint"
                  , val =
                    [ ParserBase_Tok
                      ( UIntTokenParser_IntTok
                        { val = 4
                        , fi = Info { filename = "file" , row2 = 2 , row1 = 2 , col2 = 9 , col1 = 8 }
                        }
                      )
                    ]
                  }
                ]
              }
            ]
          }
        , ParserConcrete_UserSym { label = "topfollownone" , val = [] }
        ]
      }
    ]
  }
in

utest parse "let"
with Left (UnexpectedToken
  { expected = (ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),fi = (NoInfo ())}))
  , stack = (
    [ {label = ("toptop"),seen = ([]),rest = ([(ParserSpec_NtSpec ("FileFollow"))])}
    , {label = ("topdecl"),seen = ([]),rest = ([])}
    , { label = ("decllet")
      , seen = ([(ParserBase_Lit {lit = ("let"),fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 0})})])
      , rest = ([(ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),fi = (NoInfo ())})),(ParserBase_Lit {lit = ("=")}),(ParserSpec_NtSpec ("Expression"))])
      }
    ])
  , found = (ParserBase_Tok (EOFTokenParser_EOFTok {fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 3})}))
  })
in

utest parse "let x ="
with Left (UnexpectedFirst
  { expected =
    [ Tok (IntTok {fi = NoInfo (), val = 0})
    ]
  , stack = (
    [ {label = ("toptop"),seen = ([]),rest = ([(ParserSpec_NtSpec ("FileFollow"))])}
    , {label = ("topdecl"),seen = ([]),rest = ([])}
    , { label = ("decllet")
      , seen = ([(ParserBase_Lit {lit = ("let"),fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 0})}),(ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ("x"),fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 5,col1 = 4})})),(ParserBase_Lit {lit = ("="),fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 7,col1 = 6})})])
      , rest = ([])
      }
    ])
  , found = (ParserBase_Tok (EOFTokenParser_EOFTok {fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 7,col1 = 7})}))
  , nt = ("Expression")
  })
in

utest parse "let let = 4"
with Left (UnexpectedToken
  { expected = (ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),fi = (NoInfo ())}))
  , stack = (
    [ {label = ("toptop"),seen = ([]),rest = ([(ParserSpec_NtSpec ("FileFollow"))])}
    , {label = ("topdecl"),seen = ([]),rest = ([])}
    , { label = ("decllet")
      , seen = ([(ParserBase_Lit {lit = ("let"),fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 3,col1 = 0})})])
      , rest = ([(ParserBase_Tok (LIdentTokenParser_LIdentTok {val = ([]),fi = (NoInfo ())})),(ParserBase_Lit {lit = ("=")}),(ParserSpec_NtSpec ("Expression"))])
      }
    ])
  , found = (ParserBase_Lit {lit = ("let"),fi = (Info {filename = ("file"),row2 = 1,row1 = 1,col2 = 7,col1 = 4})})
  })
in

()
