-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

/-

This file implements breakable operators (`breakable.mc`) on top of a
more normal parsing strategy, in this case LL(1) (`ll1.mc`).

For more info on how precedence works, and basic ideas on how to break
productions into operators, see `breakable.mc`.

The primary entry-points to this module are `semanticGrammar` and
`semanticParseFile`. All other exported values are used to help define
a grammar, see the tests for examples on how to use them.

-/

include "lexer.mc"
include "ll1.mc"
include "breakable.mc"

type NonTerminal
type Production

type DefaultInclude
con DefaultIn : () -> DefaultInclude
con DefaultNotIn : () -> DefaultInclude

let semanticDefIn = DefaultIn ()
let semanticDefNotIn = DefaultNotIn ()

type ProdType
con Atom :
  { self : DefaultInclude
  } -> ProdType
con Prefix :
  { self : DefaultInclude
  , right : DefaultInclude
  } -> ProdType
con Postfix :
  { self : DefaultInclude
  , left : DefaultInclude
  } -> ProdType
con Infix :
  { self : DefaultInclude
  , left : DefaultInclude
  , right : DefaultInclude
  } -> ProdType

let _prodTypeSelf
  : ProdType
  -> DefaultInclude
  = lam pt.
    match pt
    with Atom {self = self}
       | Prefix {self = self}
       | Postfix {self = self}
       | Infix {self = self}
    then self
    else never

let semanticDefInfix = Infix
  { self = DefaultIn ()
  , left = DefaultIn ()
  , right = DefaultIn ()
  }

let semanticDefPrefix = Prefix
  { self = DefaultIn ()
  , right = DefaultIn ()
  }

let semanticDefPostfix = Postfix
  { self = DefaultIn ()
  , left = DefaultIn ()
  }

let semanticDefAtom = Atom
  { self = DefaultIn ()
  }

let _lopenType = lam x.
  match x with Postfix _ | Infix _ then true else false

let _ropenType = lam x.
  match x with Prefix _ | Infix _ then true else false

type Override
con LeftChild : { child : Production, parent : Production } -> Override
con RightChild : { child : Production, parent : Production } -> Override

type Precedence = { mayGroupLeft : Bool, mayGroupRight : Bool }

let semanticGroupEither = lam l. lam r. ((l, r), { mayGroupLeft = true, mayGroupRight = true })
let semanticGroupLeft = lam l. lam r. ((l, r), { mayGroupLeft = true, mayGroupRight = false })
let semanticGroupRight = lam l. lam r. ((l, r), { mayGroupLeft = false, mayGroupRight = true })
let semanticGroupNeither = lam l. lam r. ((l, r), { mayGroupLeft = false, mayGroupRight = false })

-- Take two lists of productions, make each production in the `high`
-- list have higher precedence than each production in the `low` list.
let semanticHighLowPrec
  : { high : [Production]
    , low : [Production]
    }
  -> [((Production, Production), Precedence)]
  = let mkGrouping = lam high. lam low.
      [ semanticGroupLeft high low
      , semanticGroupRight low high
      ] in
    lam spec. join (seqLiftA2 mkGrouping spec.high spec.low)

-- Take a precedence table, from high precedence to low precedence,
-- and impose the implied precedences. Note that no precedence is
-- applied between productions on the same precedence level.
recursive let semanticPrecTableNoEq
  : [[Production]]
  -> [((Production, Production) Precedence)]
  = lam table.
    match table with [high] ++ lows then
      concat (semanticHighLowPrec {high = high, low = join lows}) (semanticPrecTableNoEq lows)
    else []
end

let semanticLeftAssoc
  : Production
  -> ((Production, Production), Precedence)
  = lam prod. semanticGroupLeft prod prod

let semanticRightAssoc
  : Production
  -> ((Production, Production), Precedence)
  = lam prod. semanticGroupRight prod prod

let semanticNonAssoc
  : Production
  -> ((Production, Production), Precedence)
  = lam prod. semanticGroupNeither prod prod

let semanticAmbAssoc
  : Production
  -> ((Production, Production), Precedence)
  = lam prod. semanticGroupEither prod prod

/-
Apply the given grouping between all given operators, regardless of
order. For example, `semanticPairwiseGroup semanticGroupLeft [a, b,
c]` is equivalent with

```
[ semanticGroupLeft a b
, semanticGroupLeft b a
, semanticGroupLeft a c
, semanticGroupLeft c a
, semanticGroupLeft b c
, semanticGroupLeft c b
]
```
-/
recursive let semanticPairwiseGroup
  : (Production -> Production -> Precedence)
  -> [Production]
  -> [((Production, Production), Precedence)]
  = lam group.
    recursive let work = lam prods.
      match prods with [prod] ++ prods then
        concat
          (join (map (lam r. [group prod r, group r prod]) prods))
          (work prods)
      else []
    in work
end

-- Create a new non-terminal with the given name.
-- WARNING: not referentially transparent
let semanticNonTerminal
  : String
  -> NonTerminal
  = lam name.
    { sym = gensym (), name = name }

type ProductionSpec =
  { name : String -- For use in error messages
  , nt : NonTerminal
  , ptype : ProdType
  , rhs : [Symbol]
  -- This is ll1.mc/Action. In case of an operator the rhs will have
  -- a `UserSym` added on each open side (e.g., `ptype = defPrefix`,
  -- `rhs = [lit "!"]` gives `action [lit "!", UserSym res]`
  , action : Action
  }

-- Create a new production.
-- WARNING: not referentially transparent
let semanticProduction
  : ProductionSpec
  -> Production
  = lam prod.
    { sym = gensym (), spec = prod }

-- TODO(vipa, 2021-03-01): See the TODO at 2021-02-24 that also refers
-- to non-terminals.
let semanticNt
  : NonTerminal
  -> Symbol
  = lam nt. ll1Nt nt.name
let semanticLit
  : String
  -> Symbol
  = ll1Lit
let semanticInt : Symbol = ll1Int
let semanticFloat : Symbol = ll1Float
let semanticOperator : Symbol = ll1Operator
let semanticString : Symbol = ll1String
let semanticChar : Symbol = ll1Char
let semanticLIdent : Symbol = ll1LIdent
let semanticUIdent : Symbol = ll1UIdent
let semanticHashString
  : String
  -> Symbol
  = ll1HashString

type Parser

type SemanticGrammarError
con DuplicatedPrecedence : [((ProductionSpec, ProductionSpec), Precedence)] -> SemanticGrammarError
con UndefinedPrecedence : {left : ProductionSpec, right : ProductionSpec} -> SemanticGrammarError
con SemanticGrammarLL1Error : GenError String -> SemanticGrammarError

type SemanticParseError
con SemanticParseBreakableError : {nt : String, info : Info} -> SemanticParseError
con SemanticParseAmbiguityError : {info : Info, irrelevant : [Info]} -> SemanticParseError
con SemanticParseError : ParseError String -> SemanticParseError
-- NOTE(vipa, 2021-02-25): All ll1 productions generated here will
-- follow the convention that we can always get the range of a
-- Symbol. In particular, each `UserSym` that goes between
-- non-terminals (i.e., once we've finished a breakable parse) will
-- carry an `Either [SemanticParseError] (Info, res)`.
let _symInfo
  : Symbol
  -> Info
  = lam sym.
    use ParserConcrete in
    match sym with Lit {info = info} then info else
    match sym with UserSym (Right (info, _)) then info else
    match sym with Tok t then use Lexer in tokInfo t else
    never
let _seqSymInfo
  : [Symbol]
  -> Info
  = lam syms.
    match syms with [s] then _symInfo s else
    match syms with [s] ++ _ ++ [e] then mergeInfo (_symInfo s) (_symInfo e) else
    match syms with [] then NoInfo () else
    never

let _breakableErrorToSemanticErrors
  : BreakableError [Symbol]
  -> [SemanticParseError]
  = lam err.
    match err with Ambiguities ambs then
      map
        (lam amb. match amb with {first = f, last = l, irrelevant = irr} then
           SemanticParseAmbiguityError
             { info = mergeInfo (_seqSymInfo f) (_seqSymInfo l)
             , irrelevant = map (lam irr. mergeInfo (_seqSymInfo irr.first) (_seqSymInfo irr.last)) irr
             }
         else never)
        ambs
    else never

let _buildSurroundedAtom
  : [(BreakableInput res [Symbol] LClosed ROpen, [Symbol])]
  -> (BreakableInput res [Symbol] LClosed RClosed, [Symbol])
  -> [(BreakableInput res [Symbol] LOpen RClosed, [Symbol])]
  -> (Info, State res [Symbol] RClosed -> Option (State res [Symbol] RClosed))
  -> State res [Symbol] ROpen
  -> Option (State res [Symbol] RClosed)
  = lam pres. lam atom. lam posts. lam contFunc. lam st.
    let st = foldl (lam st. lam pre. breakableAddPrefix pre.0 pre.1 st) st pres in
    let st = breakableAddAtom atom.0 atom.1 st in
    let mSt = optionFoldlM (lam st. lam post. breakableAddPostfix post.0 post.1 st) st posts in
    optionBind mSt contFunc.1

let _surroundedAtomInfo
  : [(BreakableInput res [Symbol] LClosed ROpen, [Symbol])]
  -> (BreakableInput res [Symbol] LClosed RClosed, [Symbol])
  -> [(BreakableInput res [Symbol] LOpen RClosed, [Symbol])]
  -> (Info, State res [Symbol] RClosed -> Option (State res [Symbol] RClosed))
  -> Info
  = lam pres. lam atom. lam posts. lam contFunc.
      let res = join (join [map (lam x. x.1) pres, [atom.1], map (lam x. x.1) posts]) in
    match res with [first] ++ _ & _ ++ [last] then
      mergeInfo (mergeInfo (_symInfo first) (_symInfo last)) contFunc.0
    else never

-- NOTE(vipa, 2021-02-22): This assumes that we can impose a total
-- order on symbols via `sym2hash`, which is not guaranteed by its
-- interface
let _cmpSym = lam a. lam b. subi (sym2hash a) (sym2hash b)
let _cmpSymPair = lam a. lam b.
  let aint1 = sym2hash a.0 in
  let bint1 = sym2hash b.0 in
  let res = subi aint1 bint1 in
  if eqi res 0 then
    subi (sym2hash a.1) (sym2hash b.1)
  else res

-- Take a grammar and try to produce a parser.
let semanticGrammar
  : { start : NonTerminal
    , productions : [Production]
    , overrideAllow : [Override]
    , overrideDisallow : [Override]
    , precedences : [((Production, Production), Precedence)]
    }
  -> Either [SemanticGrammarError] Parser
  = lam grammar.
    let productions = grammar.productions in
    let precedences = grammar.precedences in
    let overrideAllow = grammar.overrideAllow in
    let overrideDisallow = grammar.overrideDisallow in
    let nonTerminals = foldl
      (lam acc. lam prod. mapInsert prod.spec.nt.sym prod.spec.nt.name acc)
      (mapEmpty _cmpSym)
      productions
    in
    let for = lam xs. lam f. map f xs in

    -- TODO(vipa, 2021-02-24): It might be nice to report inconsistent
    -- overrides, i.e., we're both overriding to allow *and* disallow
    -- the same production in the same position, but I'm punting on
    -- that for now, it should be a rare occurrence. Similarly, it
    -- might be nice to report overrides that don't make sense, i.e.,
    -- when the override is on left/right when the production isn't
    -- left/right-open.
    type MultiOverride =
      { left: {allow: [Symbol], disallow: [Symbol]}
      , right: {allow: [Symbol], disallow: [Symbol]}
      } in
    let emptyMultiOverride = {left = {allow = [], disallow = []}, right = {allow = [], disallow = []}} in
    let mergeMultiOverride =
      let mergeSide = lam a. lam b.
        { allow = concat a.allow b.allow
        , disallow = concat a.disallow b.disallow
        } in
      lam a. lam b.
      { left = mergeSide a.left b.left
      , right = mergeSide a.right b.right
      }
    in
    let overrides = foldl
      (lam acc. lam override.
        match override with LeftChild {child = {sym = child}, parent = {sym = parent}} then
          mapInsertWith mergeMultiOverride parent
            {emptyMultiOverride with left = {allow = [child], disallow = []}}
            acc
        else match override with RightChild {child = {sym = child}, parent = {sym = parent}} then
          mapInsertWith mergeMultiOverride parent
            {emptyMultiOverride with right = {allow = [child], disallow = []}}
            acc
        else never)
      (mapEmpty _cmpSym)
      overrideAllow in
    let overrides = foldl
      (lam acc. lam override.
        match override with LeftChild {child = {sym = child}, parent = {sym = parent}} then
          mapInsertWith mergeMultiOverride parent
            {emptyMultiOverride with left = {disallow = [child], allow = []}}
            acc
        else match override with RightChild {child = {sym = child}, parent = {sym = parent}} then
          mapInsertWith mergeMultiOverride parent
            {emptyMultiOverride with right = {disallow = [child], allow = []}}
            acc
        else never)
      overrides
      overrideDisallow
    in

    -- Make each non-terminal separately, since they should generate a
    -- breakable grammar each
    let res = for (mapBindings nonTerminals)
      (lam nt.
        let ntsym = nt.0 in
        let ntname = nt.1 in
        let precedences = filter
          (lam p. match p with (({spec = {ptype = ltype, nt = lnt}}, {spec = {ptype = rtype, nt = rnt}}), _) then
            and
             (and (eqsym lnt.sym ntsym) (eqsym rnt.sym ntsym))
             (and (_ropenType ltype) (_lopenType rtype))
           else false)
          precedences in
        let productions = filter
          (lam prod. eqsym prod.spec.nt.sym ntsym)
          productions in

        let getSyms = lam p. match p with (({sym = lsym}, {sym = rsym}), _)
          then (lsym, rsym)
          else never in
        let groupedPrecs = foldl
          (lam acc. lam p. mapInsertWith concat (getSyms p) [p] acc)
          (mapEmpty _cmpSymPair)
          precedences in

        let dupPrecErrs =
          let asSpecs = lam p. match p with (({spec = lspec}, {spec = rspec}), prec)
            then ((lspec, rspec), prec)
            else never in
          let duplicatedPrecs = filter
            (lam x. gti (length x) 1)
            (map (lam x. x.1) (mapBindings groupedPrecs)) in
          let mkDupErr = lam ps. DuplicatedPrecedence (map asSpecs ps) in
          map mkDupErr duplicatedPrecs
        in

        let undefPrecErrs =
          let allLOpen = filter
            (lam prod. _lopenType prod.spec.ptype)
            productions in
          let allROpen = filter
            (lam prod. _ropenType prod.spec.ptype)
            productions in
          let paired = seqLiftA2 (lam a. lam b. (a, b)) allROpen allLOpen in
          let undef = filter
            (lam p. match p with ({sym = lsym, spec = lspec}, {sym = rsym, spec = rspec}) then
               not (mapMem (lsym, rsym) groupedPrecs)
             else never)
            paired in
          map (lam x. UndefinedPrecedence {left = x.0, right = x.1}) undef
        in

        let emptyAllowSet = AllowSet (mapEmpty _cmpSym) in
        let defaultAllowSet =
          let defaultDisallow = filter
            (lam prod. match _prodTypeSelf prod.spec.ptype with DefaultNotIn _ then true else false)
            productions in
          let syms = map (lam x. x.sym) defaultDisallow in
          DisallowSet (mapFromList _cmpSym syms)
        in

        let baseAllowSet
          : DefaultInclude
          -> AllowSet Symbol
          = lam d.
            match d with DefaultIn _ then defaultAllowSet else
            match d with DefaultNotIn _ then emptyAllowSet else
            never
        in

        let makeProductionBreakable = lam prod.
          use ParserConcrete in
          match prod with {sym = sym, spec = {name = name, nt = nt, ptype = ptype, rhs = rhs, action = action}} then
            let unwrapChildren = map
              (lam sym. match sym with UserSym (Right (_, x))
                then UserSym x
                else sym) in
            match ptype with Atom _ then
              BreakableAtom {label = sym, construct = lam mid. action (unwrapChildren mid)}
            else match ptype with Prefix {right = right} then
              let overrides = match mapLookup sym overrides
                with Some {right = overrides} then overrides
                else {allow = [], disallow = []} in
              let rightAllow = baseAllowSet right in
              let rightAllow = foldl
                (lam acc. lam toAdd. breakableInsertAllowSet toAdd acc)
                rightAllow
                overrides.allow in
              let rightAllow = foldl
                (lam acc. lam toRem. breakableRemoveAllowSet toRem acc)
                rightAllow
                overrides.disallow in
              let construct = lam mid. lam r. action (snoc (unwrapChildren mid) (UserSym r)) in
              BreakablePrefix {label = sym, construct = construct, rightAllow = rightAllow}
            else match ptype with Postfix {left = left} then
              let overrides = match mapLookup sym overrides
                with Some {left = overrides} then overrides
                else {allow = [], disallow = []} in
              let leftAllow = baseAllowSet left in
              let leftAllow = foldl
                (lam acc. lam toAdd. breakableInsertAllowSet toAdd acc)
                leftAllow
                overrides.allow in
              let leftAllow = foldl
                (lam acc. lam toRem. breakableRemoveAllowSet toRem acc)
                leftAllow
                overrides.disallow in
              let construct = lam mid. lam l. action (cons (UserSym l) (unwrapChildren mid)) in
              BreakablePostfix {label = sym, construct = construct, leftAllow = leftAllow}
            else match ptype with Infix {left = left, right = right} then
              let overrides = match mapLookup sym overrides
                with Some overrides then overrides
                else emptyMultiOverride in
              let leftAllow = baseAllowSet left in
              let leftAllow = foldl
                (lam acc. lam toAdd. breakableInsertAllowSet toAdd acc)
                leftAllow
                overrides.left.allow in
              let leftAllow = foldl
                (lam acc. lam toRem. breakableRemoveAllowSet toRem acc)
                leftAllow
                overrides.left.disallow in
              let rightAllow = baseAllowSet right in
              let rightAllow = foldl
                (lam acc. lam toAdd. breakableInsertAllowSet toAdd acc)
                rightAllow
                overrides.right.allow in
              let rightAllow = foldl
                (lam acc. lam toRem. breakableRemoveAllowSet toRem acc)
                rightAllow
                overrides.right.disallow in
              let construct = lam mid. lam l. lam r. action (cons (UserSym l) (snoc (unwrapChildren mid) (UserSym r))) in
              BreakableInfix {label = sym, construct = construct, leftAllow = leftAllow, rightAllow = rightAllow}
            else never
          else never
        in

        let breakablePrecomputed = breakableGenGrammar _cmpSym
          { productions = map makeProductionBreakable productions
          , precedences = map
            (lam pair. (pair.0, (head pair.1).1))
            (mapBindings groupedPrecs)
          } in
        let atom = lam sym. mapFind sym breakablePrecomputed.atoms in
        let prefix = lam sym. mapFind sym breakablePrecomputed.prefixes in
        let postfix = lam sym. mapFind sym breakablePrecomputed.postfixes in
        let infix = lam sym. mapFind sym breakablePrecomputed.infixes in

        -- TODO(vipa, 2021-02-24): There will be a bug if multiple
        -- non-terminals have the same name, they will be merged, even
        -- though the interface (not referentially transparent) suggests
        -- this is not the case. See also the TODO at 2021-03-01.
        let topNt = ntname in
        let contNt = concat ntname " continuation" in
        let atomNt = concat "atomic " ntname in
        let prefixNt = concat "prefix " ntname in
        let prefixesNt = concat ntname " prefixes" in
        let infixNt = concat "infix " ntname in
        let postfixNt = concat "postfix " ntname in
        let postfixesNt = concat ntname " postfixes" in

        let makeProductionLL1 = lam prod.
          match prod with {sym = sym, spec = {name = name, nt = nt, ptype = ptype, rhs = rhs, action = action}} then
            match ptype with Atom _ then
              let input = atom sym in
              {nt = atomNt, label = name, rhs = rhs, action = lam x. (input, x)}
            else match ptype with Prefix {right = right} then
              let input = prefix sym in
              {nt = prefixNt, label = name, rhs = rhs, action = lam x. (input, x)}
            else match ptype with Postfix {left = left} then
              let input = postfix sym in
              {nt = postfixNt, label = name, rhs = rhs, action = lam x. (input, x)}
            else match ptype with Infix {left = left, right = right} then
              let input = infix sym in
              {nt = infixNt, label = name, rhs = rhs, action = lam x. (input, x)}
            else never
          else never
        in
        use ParserConcrete in
        match concat dupPrecErrs undefPrecErrs with errs & [_] ++ _ then
          Left errs
        else Right (concat
          (map makeProductionLL1 productions)
          [ { nt = topNt
            , label = ntname
            , rhs = [ll1Nt prefixesNt, ll1Nt atomNt, ll1Nt postfixesNt, ll1Nt contNt]
            , action = lam xs.
              match xs with [UserSym pres, UserSym atom, UserSym posts, UserSym contFunc] then
                let syms = join
                  [ join (map (lam x. x.1) pres)
                  , atom.1
                  , join (map (lam x. x.1) posts)
                  , contFunc.2
                  ] in
                let errs = join
                  (map
                    (lam sym. match sym with UserSym (Left es) then es else [])
                    syms) in
                let st = breakableInitState () in
                let mSt = _buildSurroundedAtom pres atom posts contFunc st in
                let info = _surroundedAtomInfo pres atom posts contFunc in
                match optionBind mSt breakableFinalizeParse with Some st then
                  match errs with [] then
                    eitherBiMap
                      _breakableErrorToSemanticErrors
                      (lam x. (info, x))
                      (breakableConstructResult st)
                  else
                    Left errs
                else
                  Left (cons (SemanticParseBreakableError {nt = ntname, info = info}) errs)
              else never
            }
          , { nt = contNt
            , label = concat "empty " contNt
            , rhs = []
            , action = lam. (NoInfo (), lam x. Some x, [])
            }
          , { nt = contNt
            , label = contNt
            , rhs = [ll1Nt infixNt, ll1Nt prefixesNt, ll1Nt atomNt, ll1Nt postfixesNt, ll1Nt contNt]
            , action = lam xs.
              match xs with [UserSym infix, UserSym pres, UserSym atom, UserSym posts, UserSym contFunc] then
                let syms = join
                  [ infix.1
                  , join (map (lam x. x.1) pres)
                  , atom.1
                  , join (map (lam x. x.1) posts)
                  , contFunc.2
                  ] in
                let newContFunc = lam st.
                  optionBind
                    (breakableAddInfix infix.0 infix.1 st)
                    (_buildSurroundedAtom pres atom posts contFunc) in
                let contInfo = _surroundedAtomInfo pres atom posts contFunc in
                (contInfo, newContFunc, syms)
              else never
            }
          , { nt = prefixesNt
            , label = concat "empty " prefixesNt
            , rhs = []
            , action = lam. []
            }
          , { nt = prefixesNt
            , label = prefixesNt
            , rhs = [ll1Nt prefixNt, ll1Nt prefixesNt]
            , action = lam xs.
              match xs with [UserSym pre, UserSym pres] then
                cons pre pres
              else never
            }
          , { nt = postfixesNt
            , label = concat "empty " postfixesNt
            , rhs = []
            , action = lam. []
            }
          , { nt = postfixesNt
            , label = postfixesNt
            , rhs = [ll1Nt postfixNt, ll1Nt postfixesNt]
            , action = lam xs.
              match xs with [UserSym post, UserSym posts] then
                cons post posts
              else never
            }
          ])
        )
    in

    let res = eitherPartition res in
    match res with ([], productions) then
      eitherMapLeft
        (lam x. SemanticGrammarLL1Error x)
        (ll1GenParser {productions = join productions, start = grammar.start.name})
    else Left (join res.0)

let semanticParseFile
  : Grammar
  -> String -- Filename
  -> String -- Content
  -> Either SemanticParseError Dyn
  = lam ll1table. lam filename. lam content.
    let res = ll1ParseWithTable ll1table filename content in
    match res with Left err then Left [SemanticParseError err] else
    match res with Right (Left err) then Left err else
    match res with Right (Right (_, res)) then Right res else
    never

mexpr

-- Small helper to make smaller errors by discarding information that
-- is typically not interesting
let shortenError = lam p.
  match p with UndefinedPrecedence {left = {spec = {name = lname}}, right = {spec = {name = rname}}} then
    ("undefPrec", join [lname, " -?- ", rname])
  else match p with DuplicatedPrecedence ([(({name = lname}, {name = rname}), _)] ++ _ & precs) then
    let precs = map (lam x. x.1) precs in
    let precs = map
      (lam x. join ["'", if x.mayGroupLeft then "<" else "", "-", if x.mayGroupRight then ">" else "", "'"])
      precs in
    ("dupPrec", join [lname, " -?- ", rname, " in {", strJoin ", " precs, "}"])
  else dprintLn p; never
in

let wrap = lam label. lam x. (label, x) in

let exprNT = semanticNonTerminal "expression" in
let declNT = semanticNonTerminal "declaration" in

let intP = semanticProduction
  { name = "int"
  , nt = exprNT
  , ptype = semanticDefAtom
  , rhs = [semanticInt]
  , action = wrap "int"
  } in

let addP = semanticProduction
  { name = "add"
  , nt = exprNT
  , ptype = semanticDefInfix
  , rhs = [semanticLit "+"]
  , action = wrap "add"
  } in

let minusP = semanticProduction
  { name = "minus"
  , nt = exprNT
  , ptype = semanticDefInfix
  , rhs = [semanticLit "-"]
  , action = wrap "minus"
  } in

let mulP = semanticProduction
  { name = "mul"
  , nt = exprNT
  , ptype = semanticDefInfix
  , rhs = [semanticLit "*"]
  , action = wrap "mul"
  } in

let negP = semanticProduction
  { name = "neg"
  , nt = exprNT
  , ptype = semanticDefPrefix
  , rhs = [semanticLit "-"]
  , action = wrap "neg"
  } in

let parP = semanticProduction
  { name = "par"
  , nt = exprNT
  , ptype = semanticDefAtom
  , rhs = [semanticLit "(", semanticNt exprNT, semanticLit ")"]
  , action = wrap "par"
  } in

let fieldAccessP = semanticProduction
  { name = "fieldAccess"
  , nt = exprNT
  , ptype = semanticDefPostfix
  , rhs = [semanticLit ".", semanticLIdent]
  , action = wrap "fieldAccess"
  } in

let ifP = semanticProduction
  { name = "if"
  , nt = exprNT
  , ptype = semanticDefPrefix
  , rhs = [semanticLit "if", semanticNt exprNT, semanticLit "then"]
  , action = wrap "if"
  } in

let elseP = semanticProduction
  { name = "else"
  , nt = exprNT
  , ptype = Infix
    { self = semanticDefIn
    , left = semanticDefNotIn
    , right = semanticDefIn
    }
  , rhs = [semanticLit "else"]
  , action = wrap "else"
  } in

let defP = semanticProduction
  { name = "def"
  , nt = declNT
  , ptype = semanticDefAtom
  , rhs = [semanticLit "def", semanticLIdent, semanticLit "=", semanticNt exprNT]
  , action = wrap "def"
  } in

let twoDefP = semanticProduction
  { name = "twoDef"
  , nt = declNT
  , ptype = semanticDefInfix
  , rhs = []
  , action = wrap "twoDef"
  } in

-- NOTE(vipa, 2021-02-25): The tests in this file are mostly written
-- to only check some parts of the produced value, through pattern
-- matching, which gives somewhat strange formatting, but works pretty
-- nicely
utest semanticGrammar
  { start = exprNT
  , productions = [intP, addP]
  , overrideAllow = []
  , overrideDisallow = []
  , precedences = []
  } with () using lam x. lam. match x
with Left
  [ UndefinedPrecedence
    { left = {spec = {name = "add"}}
    , right = {spec = {name = "add"}}
    }
  ]
then true else false in

let g =
  let res = semanticGrammar
    { start = exprNT
    , productions = [intP, addP]
    , overrideAllow = []
    , overrideDisallow = []
    , precedences = join
      [ [semanticAmbAssoc addP]
      ]
    } in
  utest res with () using lam x. lam. match x
  with Right _
  then true else false in
  match res with Right x then x else never
in

utest semanticParseFile g "file" ""
with () using lam x. lam. use ParserConcrete in match x
with Left [SemanticParseError (UnexpectedFirst
  { expected = [Tok (IntTok _)]
  , found = Tok (EOFTok _)
  })]
then true else false in

utest semanticParseFile g "file" "7"
with () using lam x. lam. use ParserConcrete in match x
with Right ("int",
  [ Tok (IntTok {val = 7})
  ])
then true else false in

utest semanticParseFile g "file" "7 +"
with () using lam x. lam. use ParserConcrete in match x
with Left [SemanticParseError (UnexpectedFirst
  { expected = [Tok (IntTok _)]
  , stack = [{label = "expression"}] ++ _
  , nt = "expression prefixes"
  , found = Tok (EOFTok _)
  })]
then true else false in

utest semanticParseFile g "file" "7 + 43"
with () using lam x. lam. use ParserConcrete in match x
with Right ("add",
  [ UserSym ("int", [Tok (IntTok {val = 7})])
  , Lit {lit = "+"}
  , UserSym ("int", [Tok (IntTok {val = 43})])
  ])
then true else false in

-- TODO(vipa, 2021-02-26): The tests with ambiguities will presently
-- check that nothing is marked as irrelevant, even though some parts
-- should be considered irrelevant. They will then blow up once that
-- code is implemented, at which point we'll update the tests
-- properly.
utest semanticParseFile g "file" "7 + 43 + 9"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 0, row2 = 1, col2 = 10}
    , irrelevant = []
    }
  ]
then true else false in

let g =
  let res = semanticGrammar
    { start = exprNT
    , productions = [intP, addP, negP, mulP, minusP]
    , overrideAllow = []
    , overrideDisallow = []
    , precedences = join
      [ map semanticLeftAssoc [addP, minusP]
      , map semanticAmbAssoc [mulP]
      , semanticPrecTableNoEq
        [ [negP]
        , [mulP]
        , [addP, minusP]
        ]
      , semanticPairwiseGroup semanticGroupLeft [addP, minusP]
      ]
    } in
  utest res with () using lam x. lam. match x
  with Right _
  then true else false in
  match res with Right x then x else never
in

utest semanticParseFile g "file" "7 + 43 + 9"
with () using lam x. lam. use ParserConcrete in match x
with Right ("add",
  [ UserSym ("add",
    [ UserSym ("int", [Tok (IntTok {val = 7})])
    , Lit {lit = "+"}
    , UserSym ("int", [Tok (IntTok {val = 43})])
    ])
  , Lit {lit = "+"}
  , UserSym ("int", [Tok (IntTok {val = 9})])
  ])
then true else false in

utest semanticParseFile g "file" "7 + 43 * 8 * 9"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 4, row2 = 1, col2 = 14}
    , irrelevant = []
    }
  ]
then true else false in

utest semanticParseFile g "file" "-1"
with () using lam x. lam. use ParserConcrete in match x
with Right ("neg",
  [ Lit {lit = "-"}
  , UserSym ("int", [Tok (IntTok {val = 1})])
  ])
then true else false in

utest semanticParseFile g "file" "-1 + 8 * -2"
with () using lam x. lam. use ParserConcrete in match x
with Right ("add",
  [ UserSym ("neg", [Lit {lit = "-"}, UserSym ("int", [Tok (IntTok {val = 1})])])
  , Lit {lit = "+"}
  , UserSym ("mul",
    [ UserSym ("int", [Tok (IntTok {val = 8})])
    , Lit {lit = "*"}
    , UserSym ("neg", [Lit {lit = "-"}, UserSym ("int", [Tok (IntTok {val = 2})])])
    ])
  ])
then true else false in

utest semanticParseFile g "file" "-1 - - 8"
with () using lam x. lam. use ParserConcrete in match x
with Right ("minus",
  [ UserSym ("neg", [Lit {lit = "-"}, UserSym ("int", [Tok (IntTok {val = 1})])])
  , Lit {lit = "-"}
  , UserSym ("neg", [Lit {lit = "-"}, UserSym ("int", [Tok (IntTok {val = 8})])])
  ])
then true else false in

let g =
  let res = semanticGrammar
    { start = exprNT
    , productions = [intP, addP, negP, mulP, minusP, parP, fieldAccessP]
    , overrideAllow = []
    , overrideDisallow = []
    , precedences = join
      [ map semanticLeftAssoc [addP, minusP]
      , map semanticAmbAssoc [mulP]
      , semanticPrecTableNoEq
        [ [negP, fieldAccessP]
        , [mulP]
        , [addP, minusP]
        ]
      , semanticPairwiseGroup semanticGroupLeft [addP, minusP]
      , semanticPairwiseGroup semanticGroupEither [negP, fieldAccessP]
      ]
    } in
  utest res with () using lam x. lam. match x
  with Right _
  then true else false in
  match res with Right x then x else never
in

utest semanticParseFile g "file" "1 .foo"
with () using lam x. lam. use ParserConcrete in match x
with Right ("fieldAccess",
  [ UserSym ("int", [Tok (IntTok {val = 1})])
  , Lit {lit = "."}
  , Tok (LIdentTok {val = "foo"})
  ])
then true else false in

utest semanticParseFile g "file" "-1 .foo"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 0, row2 = 1, col2 = 7}
    , irrelevant = []
    }
  ]
then true else false in

utest semanticParseFile g "file" "-1 .foo + 32"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 0, row2 = 1, col2 = 7}
    , irrelevant = []
    }
  ]
then true else false in

utest semanticParseFile g "file" "(-1).foo"
with () using lam x. lam. use ParserConcrete in match x
with Right ("fieldAccess",
  [ UserSym ("par",
    [ Lit {lit = "("}
    , UserSym ("neg",
      [ Lit {lit = "-"}
      , UserSym ("int", [Tok (IntTok {val = 1})])
      ])
    , Lit {lit = ")"}
    ])
  , Lit {lit = "."}
  , Tok (LIdentTok {val = "foo"})
  ])
then true else false in

utest semanticParseFile g "file" "(1 * 2 * 3) * 8 * 9"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 1, row2 = 1, col2 = 10}
    , irrelevant = []
    }
  ]
  -- NOTE(vipa, 2021-03-01): This should actually be two ambiguity
  -- errors, but we presently can't get an ambiguity error out without
  -- trying to construct the final result. The latter can't be done if
  -- there is an error in a descendant, which is the case when there
  -- is a nested ambiguity error.
then true else false in

utest semanticGrammar
  { start = exprNT
  , productions = [intP, addP, negP, mulP, minusP, parP, fieldAccessP, ifP, elseP]
  , overrideAllow = [LeftChild{parent = elseP, child = ifP}]
  , overrideDisallow = []
  , precedences = join
    [ map semanticLeftAssoc [addP, minusP]
    , map semanticAmbAssoc [mulP]
    , semanticPrecTableNoEq
      [ [negP, fieldAccessP]
      , [mulP]
      , [addP, minusP]
      , [ifP]
      ]
    , semanticPairwiseGroup semanticGroupLeft [addP, minusP]
    , semanticPairwiseGroup semanticGroupEither [negP, fieldAccessP]
    , map semanticLeftAssoc [elseP]
    , seqLiftA2 semanticGroupRight [elseP] [fieldAccessP]
    , seqLiftA2 semanticGroupEither [elseP] [addP, mulP, minusP, ifP, fieldAccessP]
    , seqLiftA2 semanticGroupEither [addP, negP, mulP, minusP, ifP] [elseP]
    ]
  }
with () using lam x. lam. match x
with Left
  [ DuplicatedPrecedence
    [ (({name = "else"}, {name = "fieldAccess"}), {mayGroupLeft = false, mayGroupRight = true})
    , (({name = "else"}, {name = "fieldAccess"}), {mayGroupLeft = true, mayGroupRight = true})
    ]
  ]
then true else false in

let g =
  let res = semanticGrammar
    { start = exprNT
    , productions = [intP, addP, negP, mulP, minusP, parP, fieldAccessP, ifP, elseP]
    , overrideAllow = [LeftChild{parent = elseP, child = ifP}]
    , overrideDisallow = []
    , precedences = join
      [ map semanticLeftAssoc [addP, minusP]
      , map semanticAmbAssoc [mulP]
      , semanticPrecTableNoEq
        [ [negP, fieldAccessP]
        , [mulP]
        , [addP, minusP]
        , [ifP]
        ]
      , semanticPairwiseGroup semanticGroupLeft [addP, minusP]
      , semanticPairwiseGroup semanticGroupEither [negP, fieldAccessP]
      , map semanticLeftAssoc [elseP]
      , seqLiftA2 semanticGroupRight [elseP] [fieldAccessP, addP, mulP, minusP]
      , seqLiftA2 semanticGroupEither [addP, negP, mulP, minusP, ifP] [elseP]
      ]
    } in
  utest eitherMapLeft (map shortenError) res with () using lam x. lam. match x
  with Right _
  then true else false in
  match res with Right x then x else never
in

utest semanticParseFile g "file" "2 else 3"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseBreakableError
    { info = Info {filename = "file", row1 = 1, row2 = 1, col1 = 0, col2 = 8}
    , nt = "expression"
    }
  ]
then true else false in

utest semanticParseFile g "file" "if 1 then 2 else 3"
with () using lam x. lam. use ParserConcrete in match x
with Right ("else",
  [ UserSym ("if",
    [ Lit {lit = "if"}
    , UserSym ("int", [Tok (IntTok {val = 1})])
    , Lit {lit = "then"}
    , UserSym ("int", [Tok (IntTok {val = 2})])
    ])
  , Lit {lit = "else"}
  , UserSym ("int", [Tok (IntTok {val = 3})])
  ])
then true else false in

utest semanticParseFile g "file" "if 1 + 11 then 2 * 22 else 3 - 33"
with () using lam x. lam. use ParserConcrete in match x
with Right ("else",
  [ UserSym ("if",
    [ Lit {lit = "if"}
    , UserSym ("add",
      [ UserSym ("int", [Tok (IntTok {val = 1})])
      , Lit {lit = "+"}
      , UserSym ("int", [Tok (IntTok {val = 11})])
      ])
    , Lit {lit = "then"}
    , UserSym ("mul",
      [ UserSym ("int", [Tok (IntTok {val = 2})])
      , Lit {lit = "*"}
      , UserSym ("int", [Tok (IntTok {val = 22})])
      ])
    ])
  , Lit {lit = "else"}
  , UserSym ("minus",
    [ UserSym ("int", [Tok (IntTok {val = 3})])
    , Lit {lit = "-"}
    , UserSym ("int", [Tok (IntTok {val = 33})])
    ])
  ])
then true else false in

utest semanticParseFile g "file" "if 0 then if 1 then 2 else 3"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 0, row2 = 1, col2 = 28}
    , irrelevant = []
    }
  ]
then true else false in

utest semanticParseFile g "file" "if 0 then -if 1 then 2 else 3"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 0, row2 = 1, col2 = 29}
    , irrelevant = []
    }
  ]
then true else false in

utest semanticParseFile g "file" "if 0 then 1 + if 1 then 2 else 3"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 0, row2 = 1, col2 = 32}
    , irrelevant = []
    }
  ]
then true else false in

utest semanticParseFile g "file" "if 0 then if 1 then 2 else 3 .foo"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseAmbiguityError
    { info = Info {filename = "file", row1 = 1, col1 = 0, row2 = 1, col2 = 33}
    , irrelevant = []
    }
  ]
then true else false in

utest semanticParseFile g "file" "if 1 then 2 else 3 .foo"
with () using lam x. lam. use ParserConcrete in match x
with Right ("else",
  [ UserSym ("if",
    [ Lit {lit = "if"}
    , UserSym ("int", [Tok (IntTok {val = 1})])
    , Lit {lit = "then"}
    , UserSym ("int", [Tok (IntTok {val = 2})])
    ])
  , Lit {lit = "else"}
  , UserSym ("fieldAccess",
    [ UserSym ("int", [Tok (IntTok {val = 3})])
    , Lit {lit = "."}
    , Tok (LIdentTok {val = "foo"})
    ])
  ])
then true else false in

let g =
  let res = semanticGrammar
    { start = declNT
    , productions = [intP, addP, negP, mulP, minusP, parP, fieldAccessP, ifP, elseP, defP, twoDefP]
    , overrideAllow = [LeftChild{parent = elseP, child = ifP}]
    , overrideDisallow = []
    , precedences = join
      [ map semanticLeftAssoc [twoDefP]

      , map semanticLeftAssoc [addP, minusP]
      , map semanticAmbAssoc [mulP]
      , semanticPrecTableNoEq
        [ [negP, fieldAccessP]
        , [mulP]
        , [addP, minusP]
        , [ifP]
        ]
      , semanticPairwiseGroup semanticGroupLeft [addP, minusP]
      , semanticPairwiseGroup semanticGroupEither [negP, fieldAccessP]
      , map semanticLeftAssoc [elseP]
      , seqLiftA2 semanticGroupRight [elseP] [fieldAccessP, addP, mulP, minusP]
      , seqLiftA2 semanticGroupEither [addP, negP, mulP, minusP, ifP] [elseP]
      ]
    } in
  utest eitherMapLeft (map shortenError) res with () using lam x. lam. match x
  with Right _
  then true else false in
  match res with Right x then x else never
in

utest semanticParseFile g "file" ""
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseError
    (UnexpectedFirst
      { expected = [Lit {lit = "def"}]
      , stack = []
      , found = Tok (EOFTok _)
      , nt = "declaration"
      }
    )
  ]
then true else false in

utest semanticParseFile g "file" "7"
with () using lam x. lam. use ParserConcrete in match x
with Left
  [ SemanticParseError
    (UnexpectedFirst
      { expected = [Lit {lit = "def"}]
      , stack = []
      , found = Tok (IntTok {val = 7})
      , nt = "declaration"
      }
    )
  ]
then true else false in

utest semanticParseFile g "file" "def x = 7"
with () using lam x. lam. use ParserConcrete in match x
with Right ("def",
  [ Lit {lit = "def"}
  , Tok (LIdentTok {val = "x"})
  , Lit {lit = "="}
  , UserSym ("int", [Tok (IntTok {val = 7})])
  ])
then true else false in

utest semanticParseFile g "file" "def x = 7 def y = 8"
with () using lam x. lam. use ParserConcrete in match x
with Right ("twoDef",
  [ UserSym ("def",
    [ Lit {lit = "def"}
    , Tok (LIdentTok {val = "x"})
    , Lit {lit = "="}
    , UserSym ("int", [Tok (IntTok {val = 7})])
    ])
  , UserSym ("def",
    [ Lit {lit = "def"}
    , Tok (LIdentTok {val = "y"})
    , Lit {lit = "="}
    , UserSym ("int", [Tok (IntTok {val = 8})])
    ])
  ])
then true else false in

utest semanticParseFile g "file" "def x = 7\ndef y = 8\ndef z = 1 + 2"
with () using lam x. lam. use ParserConcrete in match x
with Right ("twoDef",
  [ UserSym ("twoDef",
    [ UserSym ("def",
      [ Lit {lit = "def"}
      , Tok (LIdentTok {val = "x"})
      , Lit {lit = "="}
      , UserSym ("int", [Tok (IntTok {val = 7})])
      ])
    , UserSym ("def",
      [ Lit {lit = "def"}
      , Tok (LIdentTok {val = "y"})
      , Lit {lit = "="}
      , UserSym ("int", [Tok (IntTok {val = 8})])
      ])
    ])
  , UserSym ("def",
    [ Lit {lit = "def"}
    , Tok (LIdentTok {val = "z"})
    , Lit {lit = "="}
    , UserSym ("add",
      [ UserSym ("int", [Tok (IntTok {val = 1})])
      , Lit {lit = "+"}
      , UserSym ("int", [Tok (IntTok {val = 2})])
      ])
    ])
  ])
then true else false in

()
