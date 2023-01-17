-- LR(k >= 1)

include "bool.mc"
include "common.mc"
include "map.mc"
include "name.mc"
include "option.mc"
include "seq.mc"
include "set.mc"


lang LRTokens
  syn LRToken =
  | LRTokenEOF ()

  sem token2string : LRToken -> String
  sem token2string =
  | LRTokenEOF _ -> "EOF"

  sem tokenId : LRToken -> Int
  sem tokenId =
  | LRTokenEOF _ -> negi 100

  sem tokenCmp : LRToken -> LRToken -> Int
  sem tokenCmp other =
  | t -> subi (tokenId other) (tokenId t)

  sem tokenEq : LRToken -> LRToken -> Bool
  sem tokenEq other =
  | t -> eqi (tokenCmp other t) 0
end

lang LRBase = LRTokens
  syn LRTerm =
  | Terminal LRToken
  | NonTerminal Name

  type LRRule = {
    name: Name,
    terms: [LRTerm]
  }

  type LRSyntaxDef = {
    entrypoint: Name,
    rules: [LRRule]
  }

  type LRStateItem = {
    name: Name,
    terms: [LRTerm],
    stackPointer: Int,
    lookahead: [LRToken],
    ruleIdx: Int -- index of the rule that this item originates from
  }

  type LRParseTable = {
    k_lookahead: Int,
    entrypointIdx: Int,
    _debugStates: [Set LRStateItem],
    nStates: Int,
    syntaxDef: LRSyntaxDef,
    shifts: Map Int [{lookahead: [LRToken], toIdx: Int}],
    gotos: Map Int [{name: Name, lookahead: [LRToken], toIdx: Int}],
    reductions: Map Int [{lookahead: [LRToken], ruleIdx: Int}]
  }


  sem lrTerm2string : LRTerm -> String
  sem lrTerm2string =
  | Terminal t -> join (["Term(", token2string t, ")"])
  | NonTerminal n -> join (["NonTerminal(", nameGetStr n, ")"])


  sem lrTermCmp2 : (LRTerm, LRTerm) -> Int
  sem lrTermCmp2 =
  | (Terminal t1, Terminal t2) -> tokenCmp t1 t2
  | (NonTerminal n1, NonTerminal n2) -> nameCmp n1 n2
  | (Terminal _, NonTerminal _) -> negi 1
  | (NonTerminal _, Terminal _) -> 1


  sem lrTermCmp : LRTerm -> LRTerm -> Int
  sem lrTermCmp other =
  | t -> lrTermCmp2 (other, t)


  sem lrtermEq : LRTerm -> LRTerm -> Bool
  sem lrtermEq other =
  | t -> eqi (lrTermCmp other t) 0


  sem lrStateItemCmp2 : (LRStateItem, LRStateItem) -> Int
  sem lrStateItemCmp2 =
  | (lhs, rhs) ->
    let cName = nameCmp lhs.name rhs.name in
    if neqi cName 0 then cName else
    let cTerms = seqCmp lrTermCmp lhs.terms rhs.terms in
    if neqi cTerms 0 then cTerms else
    let cStackPointer = subi lhs.stackPointer rhs.stackPointer in
    if neqi cStackPointer 0 then cStackPointer else
    let cLookahead = seqCmp tokenCmp lhs.lookahead rhs.lookahead in
    if neqi cLookahead 0 then cLookahead else
    let cRuleIdx = subi lhs.ruleIdx rhs.ruleIdx in
    cRuleIdx


  sem lrStateItemCmp : LRStateItem -> LRStateItem -> Int
  sem lrStateItemCmp lhs =
  | rhs -> lrStateItemCmp2 (lhs, rhs)


  -- The ComposeFirst function
  --   if seq = [Y_1]:
  --     -- take the FIRST_n available
  --     return {[t_1,...,t_n] | [t_1,t_2,t_3,t_4,...] in FIRST_k(Y_1)}
  --   else if seq = [Y_1] ++ rest:
  --     ret <- {}
  --     for [t_1,..t_i] in FIRST_k(Y_1):
  --       if i >= n:
  --         ret <- ret U {[t_1,...,t_n]}
  --       else:
  --         for [t_{i+1},...t_j] in ComposeFirst(n - i, rest):
  --           ret <- ret U {[t_1,..t_i,t_{i+1},...t_j]}
  --     return ret
  sem lrComposeFirst: Int -> Map LRTerm (Set [LRToken]) -> [LRTerm] -> Set [LRToken]
  sem lrComposeFirst k firstMap =
  | [y1] ->
    -- Return first k from the firstMap
    setFold (lam acc: Set [LRToken]. lam y1_tokens: [LRToken].
      setInsert (subsequence y1_tokens 0 k) acc
    ) (setEmpty (seqCmp tokenCmp)) (mapLookupOrElse (lam. setEmpty (seqCmp tokenCmp)) y1 firstMap)
  | [y1, y2] ++ rest ->
    setFold (lam acc: Set [LRToken]. lam y1_tokens: [LRToken].
      if geqi (length y1_tokens) k then
        setInsert (subsequence y1_tokens 0 k) acc
      else
        setFold (lam acc: Set [LRToken]. lam rest_tokens: [LRToken].
          setInsert (concat y1_tokens rest_tokens) acc
        ) acc (lrComposeFirst (subi k (length y1_tokens)) firstMap (cons y2 rest))
    ) (setEmpty (seqCmp tokenCmp)) (mapLookupOrElse (lam. setEmpty (seqCmp tokenCmp)) y1 firstMap)
  | [] ->
    setInsert [] (setEmpty (seqCmp tokenCmp))


  -- FIRST_k(S) is the set of sequences of all non-terminals that can appear
  -- for a term S, truncated to the first k symbols.
  sem lrFirst : Int -> LRSyntaxDef -> Map LRTerm (Set [LRToken])
  sem lrFirst k =
  | syntaxDef ->
    -- Compile a set of all terms in the syntax definition
    let allTerms: Set LRTerm = foldl (lam acc: Set LRTerm. lam rule: LRRule.
      let acc = setInsert (NonTerminal rule.name) acc in
      foldl (lam acc: Set LRTerm. lam term: LRTerm. setInsert term acc) acc rule.terms
    ) (setEmpty lrTermCmp) syntaxDef.rules in

    -- Initialize FIRST_k:
    --   for all terminals t:
    --     FIRSK_k(t) = {[t]}
    --   for all non-terminals S:
    --     FIRST_k(S) = {}
    let firstK: Map LRTerm (Set [LRToken]) = setFold (lam acc: Map LRTerm (Set [LRToken]). lam term: LRTerm.
      switch term
      case Terminal t then mapInsert term (setInsert [t] (setEmpty (seqCmp tokenCmp))) acc
      case NonTerminal _ then mapInsert term (setEmpty (seqCmp tokenCmp)) acc
      end
    ) (mapEmpty lrTermCmp) allTerms in

    -- Convenience functions for insertions
    let firstInsert: LRTerm -> Set [LRToken] -> Map LRTerm (Set [LRToken]) -> Map LRTerm (Set [LRToken]) = lam term. lam tokenSet. lam firstMap.
      mapInsert term
                (setUnion tokenSet
                          (mapLookupOrElse (lam. setEmpty (seqCmp tokenCmp))
                                           term
                                           firstMap))
                firstMap
    in

    -- loop until convergence:
    --   for each production S -> Y_1 Y_2 ... Y_n do:
    --     if n = 0:
    --       FIRST_k(S) <- FIRST_k(S) U {[]}  -- empty production
    --     else if for all Y_i, FIRST_k(Y_i) != ø:
    --       FIRST_k(S) <- FIRST_k(S) U ComposeFirst(k, [Y_1,Y_2,...,Y_n])
    recursive let iterate = lam firstMap: Map LRTerm (Set [LRToken]).
      let resultMap = foldl (lam firstMap: Map LRTerm (Set [LRToken]). lam rule: LRRule.
        if eqi (length rule.terms) 0 then
          firstInsert (NonTerminal rule.name) (setInsert [] (setEmpty (seqCmp tokenCmp))) firstMap
        else if any (lam term: LRTerm. setIsEmpty (mapLookupOrElse (lam. setEmpty (seqCmp tokenCmp)) term firstMap)) rule.terms then
          firstMap -- one of symbols for these rules lack an instance of firskK, skip this for now
        else
          firstInsert (NonTerminal rule.name) (lrComposeFirst k firstMap rule.terms) firstMap
      ) firstMap (syntaxDef.rules) in
      if mapEq setEq resultMap firstMap then
        resultMap
      else
        iterate resultMap
    in
    iterate firstK


  -- Computes the closure for the input set as
  -- Closure(I) =
  --   repeat
  --     for any item (A -> a.Xb, L) in I
  --       for any production X -> y
  --         for any W in FIRST_k (bL)
  --           I <- I U {(X -> .y, W)}
  --   until I does not change
  --   return I
  sem lrClosure: Int -> LRSyntaxDef -> Map LRTerm (Set [LRToken]) -> Set LRStateItem -> Set LRStateItem
  sem lrClosure k syntaxDef firstMap =
  | inSet ->
    -- OPT(johnwikman, 2023-01-14): This performs a bunch of unnecessary checks
    -- on new iterations, as it only needs to check the latest items that were
    -- added to the set. But to keep things simple initially, I didn't bother
    -- to implement this optimization.
    recursive let iterate = lam inSet: Set LRStateItem.
      let resultSet = setFold (lam accSet: Set LRStateItem. lam item: LRStateItem.
        match subsequence item.terms item.stackPointer (length item.terms)
        with [NonTerminal x] ++ b then
          let bL: [LRTerm] = concat b (map (lam t. Terminal t) item.lookahead) in
          let firstK_bL: Set [LRToken] = lrComposeFirst k firstMap bL in
          foldli (lam accSet: Set LRStateItem. lam ruleIdx: Int. lam rule: LRRule.
            if nameEq x rule.name then
              -- Process this rule
              setFold (lam accSet: Set LRStateItem. lam w: [LRToken].
                let newItem: LRStateItem = {
                  name = x,
                  terms = rule.terms,
                  stackPointer = 0,
                  lookahead = w,
                  ruleIdx = ruleIdx
                } in
                setInsert newItem accSet
              ) accSet firstK_bL
            else
              accSet
          ) accSet syntaxDef.rules
        else
          accSet
      ) inSet inSet in
      if setEq resultSet inSet then
        resultSet
      else
        iterate resultSet
    in
    iterate inSet


  -- GOTO(I, X) =
  --   J <- {}
  --   for any item (A -> a.Xb, L) in I
  --     add (A -> aX.b, L) to J
  --   return Closure(J)
  sem lrGoto: Int -> LRSyntaxDef -> Map LRTerm (Set [LRToken]) -> Set LRStateItem -> LRTerm -> Set LRStateItem
  sem lrGoto k syntaxDef firstMap inSet =
  | x ->
    let j = setFold (lam jAcc: Set LRStateItem. lam item: LRStateItem.
      if lti item.stackPointer (length item.terms) then
        if lrtermEq x (get item.terms item.stackPointer) then
          setInsert {item with stackPointer = addi item.stackPointer 1} jAcc
        else
          jAcc
      else
        jAcc
    ) (setEmpty lrStateItemCmp) inSet in
    lrClosure k syntaxDef firstMap j


  -- Initialize T to {Closure(({S' -> .S$}, $))}
  -- Initialize E to empty
  -- repeat
  --  for each state I in T
  --    for each item (A -> a.Xb, z) in I
  --      let J be GOTO(I, X)
  --      T <- T U {J}
  --      E <- E U {I --X-> J}
  -- until E and T did not change in this iteration
  -- R <- {}
  -- for each state I in T
  --   for each item (A -> a., z) in I
  --     R <- R U {(I, z, A -> a)}
  sem lrCreateParseTable: Int -> LRSyntaxDef -> LRParseTable
  sem lrCreateParseTable k =
  | syntaxDef ->
    let initRule: LRRule = {
      name = nameSym "_entrypoint_",
      terms = [NonTerminal syntaxDef.entrypoint, Terminal (LRTokenEOF ())]
    } in
    let syntaxDef = {syntaxDef with rules = snoc syntaxDef.rules initRule} in
    let firstK = lrFirst k syntaxDef in
    let initState: Set LRStateItem = setInsert {
      name = initRule.name,
      terms = initRule.terms,
      stackPointer = 0,
      lookahead = [],
      ruleIdx = subi (length syntaxDef.rules) 1 -- We inserted the initial rule at the back
    } (setEmpty lrStateItemCmp) in
    let initState: Set LRStateItem = lrClosure k syntaxDef firstK initState in
    let table: LRParseTable = {
      k_lookahead = k,
      entrypointIdx = 0,
      _debugStates = [initState],
      nStates = 1,
      syntaxDef = syntaxDef,
      shifts = mapEmpty subi,
      gotos = mapEmpty subi,
      reductions = mapEmpty subi
    } in

    -- Iterate to create all states and transitions
    recursive let iterate = lam table: LRParseTable. lam stateIdxLookup: Map (Set LRStateItem) Int. lam nextStateIdx: Int.
      if geqi nextStateIdx table.nStates then
        table
      else --continue
      let state = get table._debugStates nextStateIdx in

      let cmpShift = lam lhs. lam rhs.
        let cLookahead = seqCmp tokenCmp lhs.lookahead rhs.lookahead in
        if neqi cLookahead 0 then cLookahead
        else subi lhs.toIdx rhs.toIdx
      in
      let cmpGoto = lam lhs. lam rhs.
        let cName = nameCmp lhs.name rhs.name in
        let cLookahead = seqCmp tokenCmp lhs.lookahead rhs.lookahead in
        if neqi cName 0 then cName
        else if neqi cLookahead 0 then cLookahead
        else subi lhs.toIdx rhs.toIdx
      in

      let result = setFold (lam acc: (LRParseTable, Map (Set LRStateItem) Int, Set {lookahead: [LRToken], toIdx: Int}, Set {name: Name, lookahead: [LRToken], toIdx: Int}). lam item: LRStateItem.
        match acc with (table, stateIdxLookup, stateShifts, stateGotos) in
        match subsequence item.terms item.stackPointer (length item.terms)
        with ([x] ++ b) & postStackTerms then
          let j = lrGoto k syntaxDef firstK state x in

          let jInsertResult =
            match mapLookup j stateIdxLookup with Some jIdx then
              (table, stateIdxLookup, jIdx)
            else
              -- the state j is new, add it to the table
              let jIdx = length table._debugStates in
              let table = {table with _debugStates = snoc table._debugStates j, nStates = addi table.nStates 1} in
              let stateIdxLookup = mapInsert j jIdx stateIdxLookup in
              (table, stateIdxLookup, jIdx)
          in
          match jInsertResult with (table, stateIdxLookup, jIdx) in

          switch x
          case Terminal t then
            -- This is a shift action
            let possibleLookaheads = lrComposeFirst k firstK (concat postStackTerms (map (lam t2. Terminal t2) item.lookahead)) in
            let stateShifts = setFold (lam acc. lam lh. setInsert {lookahead = lh, toIdx = jIdx} acc) stateShifts possibleLookaheads in
            (table, stateIdxLookup, stateShifts, stateGotos)
          case NonTerminal n then
            -- This is a Goto action
            let possibleLookaheads = lrComposeFirst k firstK (concat b (map (lam t2. Terminal t2) item.lookahead)) in
            let stateGotos = setFold (lam acc. lam lh. setInsert {name = n, lookahead = lh, toIdx = jIdx} acc) stateGotos possibleLookaheads in
            (table, stateIdxLookup, stateShifts, stateGotos)
          end
        else
          acc
      ) (table, stateIdxLookup, setEmpty cmpShift, setEmpty cmpGoto) state in
      match result with (table, stateIdxLookup, stateShifts, stateGotos) in

      -- Only keep track of unique state transitions
      let stateShifts = setToSeq stateShifts in
      let stateGotos = setToSeq stateGotos in
      let table = {table with shifts = mapInsert nextStateIdx stateShifts table.shifts,
                              gotos = mapInsert nextStateIdx stateGotos table.gotos} in
      iterate table stateIdxLookup (addi nextStateIdx 1)
    in
    let table = iterate table (mapInsert initState 0 (mapEmpty setCmp)) 0 in

    -- Construct the reductions
    let table = foldli (lam tableAcc: LRParseTable. lam stateIdx: Int. lam state: Set LRStateItem.
      let stateReductions = setFold (lam redAcc: [{lookahead: [LRToken], ruleIdx: Int}]. lam item: LRStateItem.
        if eqi item.stackPointer (length item.terms) then
          snoc redAcc {lookahead = item.lookahead, ruleIdx = item.ruleIdx}
        else
          redAcc
      ) [] state in
      {tableAcc with reductions = mapInsert stateIdx stateReductions tableAcc.reductions}
    ) table table._debugStates in

    -- Table is now constructed
    table
end

lang LRBaseTest = LRBase
  syn LRToken =
  | LRTokenIdentifier String
  | LRTokenLParen {}
  | LRTokenRParen {}
  | LRTokenComma {}
  | LRTokenStar {}
  | LRTokenEquals {}

  sem token2string =
  | LRTokenIdentifier s -> join ["Ident\"", s, "\""]
  | LRTokenLParen {} -> "("
  | LRTokenRParen {} -> ")"
  | LRTokenComma {} -> ","
  | LRTokenStar {} -> "*"
  | LRTokenEquals {} -> "="

  sem tokenId =
  | LRTokenIdentifier _ -> 1
  | LRTokenLParen {} -> 2
  | LRTokenRParen {} -> 3
  | LRTokenComma {} -> 4
  | LRTokenStar {} -> 5
  | LRTokenEquals {} -> 6
end


mexpr
use LRBaseTest in


type LRTestCase = {
  name: String,
  syntaxDef: LRSyntaxDef,
  first1: Map LRTerm (Set [LRToken]),
  first2: Map LRTerm (Set [LRToken]),
  first3: Map LRTerm (Set [LRToken])
} in


let testcases = [
  -- LR1 example from the book by Appel
  let _S = nameSym "S" in
  let _E = nameSym "E" in
  let _V = nameSym "V" in
  {
    name = "LR1 Example",
    syntaxDef = {
      entrypoint = _S,
      rules = [
        {name = _S, terms = [NonTerminal _V, Terminal (LRTokenEquals ()), NonTerminal _E]},
        {name = _S, terms = [NonTerminal _E]},
        {name = _E, terms = [NonTerminal _V]},
        {name = _V, terms = [Terminal (LRTokenIdentifier "")]},
        {name = _V, terms = [Terminal (LRTokenStar ()), NonTerminal _E]}
      ]
    },
    first1 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""], [LRTokenStar ()]
       ]),
      (NonTerminal _E, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""], [LRTokenStar ()]
       ]),
      (NonTerminal _V, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""], [LRTokenStar ()]
       ])
    ],
    first2 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""],
        [LRTokenIdentifier "", LRTokenEquals ()],
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar ()]
       ]),
      (NonTerminal _E, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar ()]
       ]),
      (NonTerminal _V, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar ()]
       ])
    ],
    first3 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""],
        [LRTokenIdentifier "", LRTokenEquals (), LRTokenStar ()],
        [LRTokenIdentifier "", LRTokenEquals (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier "", LRTokenEquals ()],
        [LRTokenStar (), LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar (), LRTokenStar ()]
       ]),
      (NonTerminal _E, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar (), LRTokenStar ()]
       ]),
      (NonTerminal _V, setOfSeq (seqCmp tokenCmp) [
        [LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenStar (), LRTokenStar ()]
       ])
    ]
  },
  -- LR2 example from https://stackoverflow.com/questions/62075086/what-is-an-lr2-parser-how-does-it-differ-from-an-lr1-parser
  let _S = nameSym "S" in
  let _R = nameSym "R" in
  let _T = nameSym "T" in
  {
    name = "LR2 Example",
    syntaxDef = 
    {
      entrypoint = _S,
      rules = [
        {name = _S, terms = [NonTerminal _R, NonTerminal _S]},
        {name = _S, terms = [NonTerminal _R]},
        {name = _R, terms = [Terminal (LRTokenStar ()), Terminal (LRTokenIdentifier ""), NonTerminal _T]},
        {name = _T, terms = [Terminal (LRTokenStar ())]},
        {name = _T, terms = [Terminal (LRTokenEquals ())]},
        {name = _T, terms = []}
      ]
    },
    first1 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar ()]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar ()]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [LRTokenEquals ()], [LRTokenStar ()], []
       ])
    ],
    first2 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenIdentifier ""]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenIdentifier ""]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [LRTokenEquals ()], [LRTokenStar ()], []
       ])
    ],
    first3 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier "", LRTokenStar ()],
        [LRTokenStar (), LRTokenIdentifier "", LRTokenEquals ()]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenIdentifier ""],
        [LRTokenStar (), LRTokenIdentifier "", LRTokenStar ()],
        [LRTokenStar (), LRTokenIdentifier "", LRTokenEquals ()]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [LRTokenEquals ()], [LRTokenStar ()], []
       ])
    ]
  },
  -- Custom example showing GOTO lookaheads
  let _S = nameSym "S" in
  let _R = nameSym "R" in
  let _T = nameSym "T" in
  {
    name = "GOTO Example",
    syntaxDef = 
    {
      entrypoint = _S,
      rules = [
        {name = _S, terms = [Terminal (LRTokenStar ()), NonTerminal _R, NonTerminal _S, Terminal (LRTokenEquals ()), Terminal (LRTokenStar ())]},
        {name = _S, terms = [Terminal (LRTokenStar ()), NonTerminal _R, NonTerminal _T, Terminal (LRTokenStar ()), Terminal (LRTokenEquals ())]},
        {name = _R, terms = [Terminal (LRTokenStar ()), Terminal (LRTokenIdentifier ""), Terminal (LRTokenEquals ())]},
        {name = _T, terms = [Terminal (LRTokenStar ()), Terminal (LRTokenEquals ())]},
        {name = _T, terms = [Terminal (LRTokenStar ()), Terminal (LRTokenIdentifier "")]}
      ]
    },
    first1 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar ()]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar ()]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar ()]
       ])
    ],
    first2 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenStar ()]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenIdentifier ""]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (),  LRTokenIdentifier ""], [LRTokenStar (),  LRTokenEquals ()]
       ])
    ],
    first3 = mapFromSeq lrTermCmp [
      (Terminal (LRTokenEquals ()), setOfSeq (seqCmp tokenCmp) [[LRTokenEquals ()]]),
      (Terminal (LRTokenIdentifier ""), setOfSeq (seqCmp tokenCmp) [[LRTokenIdentifier ""]]),
      (Terminal (LRTokenStar ()), setOfSeq (seqCmp tokenCmp) [[LRTokenStar ()]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenStar (), LRTokenIdentifier ""]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (), LRTokenIdentifier "", LRTokenEquals ()]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [LRTokenStar (),  LRTokenIdentifier ""], [LRTokenStar (),  LRTokenEquals ()]
       ])
    ]
  }
] in


let printFirst: Int -> Map LRTerm (Set [LRToken]) -> () = lam k. lam firstMap.
  mapFoldWithKey (lam. lam term: LRTerm. lam first1: Set [LRToken].
    match term with NonTerminal _ then
      printLn (join ["First_", int2string k, "(", lrTerm2string term, "):"]);
      setFold (lam. lam tokens: [LRToken].
        printLn (join ["  [", strJoin ", " (map token2string tokens), "]"])
      ) () first1
    else
      ()
  ) () firstMap
in


let printStates: [Set LRStateItem] -> () = lam states.
  printLn "  States:";
  foldli (lam. lam stateIdx: Int. lam state: Set LRStateItem.
    printLn (join ["    State ", int2string stateIdx, ":"]);
    let stateStrs = setFold (lam acc: [(String, String)]. lam item: LRStateItem.
      let prefix = ["      ", nameGetStr item.name, " ->"] in
      let prefix = foldli (lam pfxacc. lam termIdx: Int. lam term: LRTerm.
        if eqi item.stackPointer termIdx then
          concat pfxacc [" [STACK]", " ", lrTerm2string term]
        else
          concat pfxacc [" ", lrTerm2string term]
      ) prefix item.terms in
      let prefix = if eqi item.stackPointer (length item.terms) then snoc prefix " [STACK]" else prefix in
      let suffix = join [
        " | (rule ", int2string item.ruleIdx, ")",
        " | (lookahead [", strJoin ", " (map token2string item.lookahead), "])"
      ] in
      snoc acc (join prefix, suffix)
    ) [] state in
    let maxLen = foldl (lam cand. lam s. match s with (prefix, _) in maxi cand (length prefix)) 0 stateStrs in
    foldl (lam. lam pfxsfx: (String, String).
      match pfxsfx with (prefix, suffix) in
      print prefix;
      print (make (subi maxLen (length prefix)) ' ');
      printLn suffix
    ) () stateStrs
  ) () states
in


let printShifts: Map Int [{lookahead: [LRToken], toIdx: Int}] -> () = lam shifts.
  printLn "  Shifts:";
  mapFoldWithKey (lam. lam stateIdx: Int. lam stateShifts: [{lookahead: [LRToken], toIdx: Int}].
    foldl (lam. lam shift: {lookahead: [LRToken], toIdx: Int}.
      printLn (join ["    ", int2string stateIdx, " --[", strJoin "," (map token2string shift.lookahead), "]--> ", int2string shift.toIdx])
    ) () stateShifts
  ) () shifts
in


let printGotos: Map Int [{name: Name, lookahead: [LRToken], toIdx: Int}] -> () = lam gotos.
  printLn "  Gotos:";
  mapFoldWithKey (lam. lam stateIdx: Int. lam stateGotos: [{name: Name, lookahead: [LRToken], toIdx: Int}].
    foldl (lam. lam goto: {name: Name, lookahead: [LRToken], toIdx: Int}.
      printLn (join ["    ", int2string stateIdx, " --(", nameGetStr goto.name, ")--[", strJoin "," (map token2string goto.lookahead), "]--> ", int2string goto.toIdx])
    ) () stateGotos
  ) () gotos
in


let printReductions: Map Int [{lookahead: [LRToken], ruleIdx: Int}] -> () = lam reductions.
  printLn "  Reductions:";
  mapFoldWithKey (lam. lam stateIdx: Int. lam stateReductions: [{lookahead: [LRToken], ruleIdx: Int}].
    foldl (lam. lam red: {lookahead: [LRToken], ruleIdx: Int}.
      printLn (join [
        "    in state ", int2string stateIdx,
        ", reduce by rule ", int2string red.ruleIdx,
        " on lookahead [", strJoin ", " (map token2string red.lookahead), "]"])
    ) () stateReductions
  ) () reductions
in



-- Run tests
foldl (lam. lam tc: LRTestCase.
  print (join ["Running testcase ", tc.name, " "]);
  utest lrFirst 1 tc.syntaxDef with tc.first1 using mapEq setEq in
  utest lrFirst 2 tc.syntaxDef with tc.first2 using mapEq setEq in
  utest lrFirst 3 tc.syntaxDef with tc.first3 using mapEq setEq in
  printLn "";
  let lrtable = lrCreateParseTable 2 tc.syntaxDef in
  printStates lrtable._debugStates;
  printShifts lrtable.shifts;
  printGotos lrtable.gotos;
  printReductions lrtable.reductions;
  printLn "\n\n";
  ()
) () testcases
