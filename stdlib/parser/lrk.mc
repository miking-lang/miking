-- LR(k >= 1)

include "bool.mc"
include "common.mc"
include "either.mc"
include "error.mc"
include "map.mc"
include "name.mc"
include "option.mc"
include "seq.mc"
include "set.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/info.mc"

lang LRTokens
  syn LRToken =
  | LRTokenEOF {info: Info}

  sem lrtoken2string : LRToken -> String
  sem lrtoken2string =
  | LRTokenEOF _ -> "EOF"

  sem tokenCmp : LRToken -> LRToken -> Int
  sem tokenCmp other =
  | t -> subi (constructorTag other) (constructorTag t)

  sem tokenEq : LRToken -> LRToken -> Bool
  sem tokenEq other =
  | t -> eqi (tokenCmp other t) 0
end

lang LRParser = LRTokens + MExprAst
  syn LRTerm =
  | Terminal LRToken
  | NonTerminal Name

  type LRRule = {
    name: Name,
    terms: [LRTerm],
    prodfun: {name: Name, ty: Type}
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
    states: [Set LRStateItem],
    syntaxDef: LRSyntaxDef,
    shifts: Map Int [{lookahead: [LRToken], toIdx: Int}],
    gotos: Map Int [{name: Name, toIdx: Int}],
    reductions: Map Int [{lookahead: [LRToken], ruleIdx: Int}]
  }


  sem lrTerm2string : LRTerm -> String
  sem lrTerm2string =
  | Terminal t -> join (["Term(", lrtoken2string t, ")"])
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
  sem lrCreateParseTable: Int -> LRSyntaxDef -> Either LRParseTable ErrorSection
  sem lrCreateParseTable k =
  | syntaxDef ->
    let initRule: LRRule = {
      name = nameSym "_entrypoint_",
      terms = [NonTerminal syntaxDef.entrypoint, Terminal (LRTokenEOF {info = NoInfo ()})],
      prodfun = {name = nameNoSym "TODO, infer the type here...", ty = tyunknown_}
    } in
    let syntaxDef = {syntaxDef with rules = snoc syntaxDef.rules initRule} in
    let firstK: Map LRTerm (Set [LRToken]) = lrFirst k syntaxDef in

    if not (mapAll (lam fst. not (setIsEmpty fst)) firstK) then
      Right {errorDefault with msg = "Invalid grammar. The FIRST set is not defined for one or more of its non-terminals."}
    else --continue

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
      states = [initState],
      syntaxDef = syntaxDef,
      shifts = mapEmpty subi,
      gotos = mapEmpty subi,
      reductions = mapEmpty subi
    } in

    -- Iterate to create all states and transitions
    recursive let iterate = lam table: LRParseTable. lam stateIdxLookup: Map (Set LRStateItem) Int. lam nextStateIdx: Int.
      if geqi nextStateIdx (length table.states) then
        table
      else --continue
      let state = get table.states nextStateIdx in

      let cmpShift = lam lhs. lam rhs.
        let cLookahead = seqCmp tokenCmp lhs.lookahead rhs.lookahead in
        if neqi cLookahead 0 then cLookahead
        else subi lhs.toIdx rhs.toIdx
      in
      let cmpGoto = lam lhs. lam rhs.
        let cName = nameCmp lhs.name rhs.name in
        if neqi cName 0 then cName
        else subi lhs.toIdx rhs.toIdx
      in

      let result = setFold (lam acc: (LRParseTable, Map (Set LRStateItem) Int, Set {lookahead: [LRToken], toIdx: Int}, Set {name: Name, toIdx: Int}). lam item: LRStateItem.
        match acc with (table, stateIdxLookup, stateShifts, stateGotos) in
        match subsequence item.terms item.stackPointer (length item.terms)
        with ([x] ++ b) & postStackTerms then
          let j = lrGoto k syntaxDef firstK state x in

          let jInsertResult =
            match mapLookup j stateIdxLookup with Some jIdx then
              (table, stateIdxLookup, jIdx)
            else
              -- the state j is new, add it to the table
              let jIdx = length table.states in
              let table = {table with states = snoc table.states j} in
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
            let stateGotos = setInsert {name = n, toIdx = jIdx} stateGotos in
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
    ) table table.states in

    -- Check for conflicts
    let conflicts = foldli (lam acc. lam stateIdx. lam.
      match (mapLookup stateIdx table.shifts, mapLookup stateIdx table.reductions) with (Some shifts, Some reductions) then
        foldli (lam acc. lam reduceIdx. lam r1: {lookahead: [LRToken], ruleIdx: Int}.
          -- reduce-reduce check
          let acc = foldl (lam acc. lam r2: {lookahead: [LRToken], ruleIdx: Int}.
            if and (eqSeq tokenEq r1.lookahead r2.lookahead) (neqi r1.ruleIdx r2.ruleIdx) then
              snoc acc (join [
                "reduce-reduce conflict in state ", int2string stateIdx, " on lookahead ",
                "[", strJoin ", " (map lrtoken2string r1.lookahead), "] (reduce by rule ",
                int2string r1.ruleIdx, " and ", int2string r2.ruleIdx, ")"
              ])
            else
              acc
          ) acc (subsequence reductions (addi reduceIdx 1) (length reductions)) in
          -- shift-reduce check
          foldl (lam acc. lam sh: {lookahead: [LRToken], toIdx: Int}.
            if eqSeq tokenEq r1.lookahead sh.lookahead then
              snoc acc (join [
                "shift-reduce conflict in state ", int2string stateIdx, " on lookahead ",
                "[", strJoin ", " (map lrtoken2string r1.lookahead), "] (reduce by rule ",
                int2string r1.ruleIdx, " and shift into state ", int2string sh.toIdx, ")"
              ])
            else
              acc
          ) acc shifts
        ) acc reductions
      else
        acc
    ) [] table.states in

    match conflicts with [] then
      -- Table is now constructed and well-formed
      Left table
    else
      Right {errorDefault with msg = strJoin "\n" (cons "Found following conflicts:" (map (concat " - ") conflicts))}


  -- Creates a multi-line representation of the LR parse table, with each line
  -- indented by the specified amount of whitespaces.
  sem lrtable2string : Int -> LRParseTable -> String
  sem lrtable2string indent =
  | lrtable ->
    let lines = [] in

    let lines = snoc lines (concat (make indent ' ') "Rules:") in
    let ruleIndent = addi (addi indent 2) (length (int2string (length lrtable.syntaxDef.rules))) in
    let lines = foldli (lam lines. lam ruleIdx. lam rule: LRRule.
      let rulenum = int2string ruleIdx in
      snoc lines (join [
        make (subi ruleIndent (length rulenum)) ' ', rulenum, ": ",
        nameGetStr rule.name, " -> ",
        strJoin " " (map lrTerm2string rule.terms)
      ])
    ) lines lrtable.syntaxDef.rules in

    let lines = snoc lines (concat (make indent ' ') "States:") in
    let lines = foldli (lam lines. lam stateIdx. lam state: Set LRStateItem.
      let lines = snoc lines (join [make (addi indent 2) ' ', "State ", int2string stateIdx, ":"]) in
      let stateStrs = setFold (lam acc: [(String, String)]. lam item: LRStateItem.
        let prefix = [make (addi indent 4) ' ', nameGetStr item.name, " ->"] in
        let prefix = foldli (lam pfxacc. lam termIdx: Int. lam term: LRTerm.
          if eqi item.stackPointer termIdx then
            concat pfxacc [" [STACK]", " ", lrTerm2string term]
          else
            concat pfxacc [" ", lrTerm2string term]
        ) prefix item.terms in
        let prefix = if eqi item.stackPointer (length item.terms) then snoc prefix " [STACK]" else prefix in
        let suffix = join [
          " | (rule ", int2string item.ruleIdx, ")",
          " | (lookahead [", strJoin ", " (map lrtoken2string item.lookahead), "])"
        ] in
        snoc acc (join prefix, suffix)
      ) [] state in
      let maxLen = foldl (lam cand. lam s. match s with (prefix, _) in maxi cand (length prefix)) 0 stateStrs in
      foldl (lam lines. lam pfxsfx: (String, String).
        match pfxsfx with (prefix, suffix) in
        snoc lines (join [prefix, make (subi maxLen (length prefix)) ' ', suffix])
      ) lines stateStrs
    ) lines lrtable.states in

    let lines = snoc lines (concat (make indent ' ') "Shifts:") in
    let lines = mapFoldWithKey (lam lines. lam stateIdx: Int. lam stateShifts: [{lookahead: [LRToken], toIdx: Int}].
      foldl (lam lines. lam shift: {lookahead: [LRToken], toIdx: Int}.
        snoc lines (join [make (addi indent 2) ' ', int2string stateIdx, " --[", strJoin "," (map lrtoken2string shift.lookahead), "]--> ", int2string shift.toIdx])
      ) lines stateShifts
    ) lines lrtable.shifts in

    let lines = snoc lines (concat (make indent ' ') "Gotos:") in
    let lines = mapFoldWithKey (lam lines. lam stateIdx: Int. lam stateGotos: [{name: Name, toIdx: Int}].
      foldl (lam lines. lam goto: {name: Name, toIdx: Int}.
        snoc lines (join [make (addi indent 2) ' ', int2string stateIdx, " --(", nameGetStr goto.name, ")--> ", int2string goto.toIdx])
      ) lines stateGotos
    ) lines lrtable.gotos in

    let lines = snoc lines (concat (make indent ' ') "Reductions:") in
    let lines = mapFoldWithKey (lam lines. lam stateIdx: Int. lam stateReductions: [{lookahead: [LRToken], ruleIdx: Int}].
      foldl (lam lines. lam red: {lookahead: [LRToken], ruleIdx: Int}.
        snoc lines (join [
          make (addi indent 2) ' ',
          "in state ", int2string stateIdx,
          ", reduce by rule ", int2string red.ruleIdx,
          " on lookahead [", strJoin ", " (map lrtoken2string red.lookahead), "]"
        ])
      ) lines stateReductions
    ) lines lrtable.reductions in

    strJoin "\n" lines
end




lang LRParserTest = LRParser
  syn LRToken =
  | LRTokenIdentifier {info: Info, val: String}
  | LRTokenLParen {info: Info}
  | LRTokenRParen {info: Info}
  | LRTokenComma {info: Info}
  | LRTokenStar {info: Info}
  | LRTokenEquals {info: Info}

  sem lrtoken2string =
  | LRTokenIdentifier r -> join ["Ident\"", r.val, "\""]
  | LRTokenLParen _ -> "("
  | LRTokenRParen _ -> ")"
  | LRTokenComma _ -> ","
  | LRTokenStar _ -> "*"
  | LRTokenEquals _ -> "="
end


mexpr
use LRParserTest in

let tokEOF = LRTokenEOF {info = NoInfo ()} in
let tokIdent = LRTokenIdentifier {info = NoInfo (), val = ""} in
let tokLParen = LRTokenLParen {info = NoInfo ()} in
let tokRParen = LRTokenRParen {info = NoInfo ()} in
let tokComma = LRTokenComma {info = NoInfo ()} in
let tokStar = LRTokenStar {info = NoInfo ()} in
let tokEquals = LRTokenEquals {info = NoInfo ()} in

type LRTestCase = {
  name: String,
  syntaxDef: LRSyntaxDef,
  isLR1: Bool,
  first1: Map LRTerm (Set [LRToken]),
  first2: Map LRTerm (Set [LRToken]),
  first3: Map LRTerm (Set [LRToken])
} in


let testcases: [LRTestCase] = [
  -- LR1 example from the book by Appel
  let _S = nameSym "S" in
  let _E = nameSym "E" in
  let _V = nameSym "V" in
  {
    name = "LR1 Example",
    syntaxDef = {
      entrypoint = _S,
      rules = [
        {name = _S, terms = [NonTerminal _V, Terminal tokEquals, NonTerminal _E], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _S, terms = [NonTerminal _E], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _E, terms = [NonTerminal _V], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _V, terms = [Terminal tokIdent], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _V, terms = [Terminal tokStar, NonTerminal _E], prodfun = {name = nameNoSym "", ty = tyunknown_ }}
      ]
    },
    isLR1 = true,
    first1 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokIdent], [tokStar]
       ]),
      (NonTerminal _E, setOfSeq (seqCmp tokenCmp) [
        [tokIdent], [tokStar]
       ]),
      (NonTerminal _V, setOfSeq (seqCmp tokenCmp) [
        [tokIdent], [tokStar]
       ])
    ],
    first2 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokIdent],
        [tokIdent, tokEquals],
        [tokStar, tokIdent],
        [tokStar, tokStar]
       ]),
      (NonTerminal _E, setOfSeq (seqCmp tokenCmp) [
        [tokIdent],
        [tokStar, tokIdent],
        [tokStar, tokStar]
       ]),
      (NonTerminal _V, setOfSeq (seqCmp tokenCmp) [
        [tokIdent],
        [tokStar, tokIdent],
        [tokStar, tokStar]
       ])
    ],
    first3 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokIdent],
        [tokIdent, tokEquals, tokStar],
        [tokIdent, tokEquals, tokIdent],
        [tokStar, tokIdent],
        [tokStar, tokIdent, tokEquals],
        [tokStar, tokStar, tokIdent],
        [tokStar, tokStar, tokStar]
       ]),
      (NonTerminal _E, setOfSeq (seqCmp tokenCmp) [
        [tokIdent],
        [tokStar, tokIdent],
        [tokStar, tokStar, tokIdent],
        [tokStar, tokStar, tokStar]
       ]),
      (NonTerminal _V, setOfSeq (seqCmp tokenCmp) [
        [tokIdent],
        [tokStar, tokIdent],
        [tokStar, tokStar, tokIdent],
        [tokStar, tokStar, tokStar]
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
        {name = _S, terms = [NonTerminal _R, NonTerminal _S], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _S, terms = [NonTerminal _R], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _R, terms = [Terminal tokStar, Terminal tokIdent, NonTerminal _T], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _T, terms = [Terminal tokStar], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _T, terms = [Terminal tokEquals], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _T, terms = [], prodfun = {name = nameNoSym "", ty = tyunknown_ }}
      ]
    },
    isLR1 = false,
    first1 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokStar]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [tokStar]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [tokEquals], [tokStar], []
       ])
    ],
    first2 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokIdent]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokIdent]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [tokEquals], [tokStar], []
       ])
    ],
    first3 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokIdent],
        [tokStar, tokIdent, tokStar],
        [tokStar, tokIdent, tokEquals]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokIdent],
        [tokStar, tokIdent, tokStar],
        [tokStar, tokIdent, tokEquals]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [tokEquals], [tokStar], []
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
        {name = _S, terms = [Terminal tokStar, NonTerminal _R, NonTerminal _T, Terminal tokEquals, Terminal tokStar], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _S, terms = [Terminal tokStar, NonTerminal _R, NonTerminal _T, Terminal tokStar, Terminal tokEquals], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _R, terms = [Terminal tokStar, Terminal tokIdent, Terminal tokEquals], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _T, terms = [Terminal tokStar, Terminal tokEquals], prodfun = {name = nameNoSym "", ty = tyunknown_ }},
        {name = _T, terms = [Terminal tokStar, Terminal tokIdent], prodfun = {name = nameNoSym "", ty = tyunknown_ }}
      ]
    },
    isLR1 = true,
    first1 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokStar]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [tokStar]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [tokStar]
       ])
    ],
    first2 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokStar]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokIdent]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [tokStar,  tokIdent], [tokStar,  tokEquals]
       ])
    ],
    first3 = mapFromSeq lrTermCmp [
      (Terminal tokEquals, setOfSeq (seqCmp tokenCmp) [[tokEquals]]),
      (Terminal tokIdent, setOfSeq (seqCmp tokenCmp) [[tokIdent]]),
      (Terminal tokStar, setOfSeq (seqCmp tokenCmp) [[tokStar]]),
      (NonTerminal _S, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokStar, tokIdent]
       ]),
      (NonTerminal _R, setOfSeq (seqCmp tokenCmp) [
        [tokStar, tokIdent, tokEquals]
       ]),
      (NonTerminal _T, setOfSeq (seqCmp tokenCmp) [
        [tokStar,  tokIdent], [tokStar,  tokEquals]
       ])
    ]
  }
] in


let printFirst: Int -> Map LRTerm (Set [LRToken]) -> () = lam k. lam firstMap.
  mapFoldWithKey (lam. lam term: LRTerm. lam first1: Set [LRToken].
    match term with NonTerminal _ then
      printLn (join ["First_", int2string k, "(", lrTerm2string term, "):"]);
      setFold (lam. lam tokens: [LRToken].
        printLn (join ["  [", strJoin ", " (map lrtoken2string tokens), "]"])
      ) () first1
    else
      ()
  ) () firstMap
in



-- Run tests
foldl (lam. lam tc: LRTestCase.
  print (join ["Running testcase ", tc.name, " "]);
  utest lrFirst 1 tc.syntaxDef with tc.first1 using mapEq setEq in
  utest lrFirst 2 tc.syntaxDef with tc.first2 using mapEq setEq in
  utest lrFirst 3 tc.syntaxDef with tc.first3 using mapEq setEq in

  let isLR1_table = match lrCreateParseTable 1 tc.syntaxDef with Left _ then true else false in
  utest isLR1_table with tc.isLR1 in

  printLn "";
  switch lrCreateParseTable 2 tc.syntaxDef
  case Left lrtable then
    printLn (lrtable2string 2 lrtable);
    printLn "\n\n"
  case Right err then
    errorGeneral [err] {single = "", multi = ""}
  end
) () testcases
