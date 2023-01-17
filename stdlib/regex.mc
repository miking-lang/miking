include "dfa.mc"
include "eqset.mc"

-- Represents basic regular expressions.
type RegEx a
con Empty   : all a. ()                 -> RegEx a
con Epsilon : all a. ()                 -> RegEx a
con Symbol  : all a. a                  -> RegEx a
con Union   : all a. (RegEx a, RegEx a) -> RegEx a
con Concat  : all a. (RegEx a, RegEx a) -> RegEx a
con Kleene  : all a. RegEx a            -> RegEx a

let prec = lam reg.
  match reg with Empty () then 2 else
  match reg with Epsilon () then 2 else
  match reg with Symbol _ then 2 else
  match reg with Union _ then 1 else
  match reg with Concat _ then 1 else
  match reg with Kleene _ then 1 else
  error "Unknown regex in prec"

let regEx2str = lam sym2str. lam reg.
  recursive
    let enclose = lam parent. lam child.
      if leqi (prec child) (prec parent) then (join ["(", pprint child, ")"])
      else pprint child

    let pprint = lam reg.
      match reg with Epsilon () then "(eps)" else
      match reg with Empty () then "(empty)" else
      match reg with Symbol (a) then sym2str a else
      match reg with Union (r1, r2) then
        join [enclose reg r1, "|", enclose reg r2] else
      match reg with Concat (r1, r2) then
        join [enclose reg r1, " ", enclose reg r2] else
      match reg with Kleene r then
        join [enclose reg r, "*"] else
      error "Not a regExPprint of a RegEx"
  in
  pprint reg

let regExPprint = lam sym2str. lam reg.
  print (regEx2str sym2str reg);
  print "\n"

-- Checks structural equivalence of two regexes.
-- Does NOT check whether the regexes describe the same language.
let eqr = lam eqsym. lam re1. lam re2.
  recursive let eqrAux = lam re1. lam re2.
    match re1 with Epsilon () then (match re2 with Epsilon () then true else false) else
    match re1 with Empty () then (match re2 with Empty () then true else false) else
    match re1 with Symbol a then (match re2 with Symbol b then eqsym a b else false) else
    match re1 with Union (r1, r2) then
      (match re2 with Union (w1, w2) then and (eqrAux r1 w1) (eqrAux r2 w2) else false)
    else
    match re1 with Concat (r1, r2) then
      (match re2 with Concat (w1, w2) then and (eqrAux r1 w1) (eqrAux r2 w2) else false)
    else
    match re1 with Kleene r then (match re2 with Kleene w then eqrAux r w else false) else
    error ("Not eqr of a RegEx")
in eqrAux re1 re2

-- Implements some basic simplification rules (not idempotent)
recursive let simplifyS = lam reg.
  match reg with Kleene(Empty ()) then Epsilon () else
  match reg with Concat(Empty (), r) | Concat(r, Empty ()) then Empty () else
  match reg with Concat(Epsilon (), r) | Concat(r, Epsilon ()) then simplifyS r else
  match reg with Union(Empty (), r) | Union(r, Empty ()) then simplifyS r else

  match reg with Empty () | Epsilon () | Symbol _ then reg else
  match reg with Union (r1, r2) then Union (simplifyS r1, simplifyS r2) else
  match reg with Concat (r1, r2) then Concat (simplifyS r1, simplifyS r2) else
  match reg with Kleene r then Kleene (simplifyS r) else

  error "Unknown RegEx in simplifyS"
end

-- Idempotent simplification
recursive let simplifyD = lam eqr. lam reg.
  let sReg = simplifyS reg in
  -- We reached a fixpoint
  if eqr reg sReg then reg
  -- We might be able to simplify more
  else simplifyD eqr sReg
end

-- Convert a DFA into a regular expression using State Elimination Method.
-- From the book: John E. Hopcroft, Jeffrey D. Ullman (1979). Introduction
-- to Automata Theory, Languages, and Computation.
let regexFromDFA = lam dfa.
  -- ** Helper functions **
  -- Merge transitions for state pair s1 and s2
  let pairMergeTrans = lam dfa. lam s1. lam s2.
    let arcsBetween = nfaTransitionsBetween s1 s2 dfa in
    match arcsBetween with [] then None () else
    match arcsBetween with [t] then
       Some (t.0, t.1, Symbol t.2)
    else
      let symbs = map (lam t. t.2) arcsBetween in
      let mergedSyms = foldl (lam acc. lam s. (Union (acc, Symbol s))) (Symbol (head symbs)) (tail symbs) in
      Some (s1, s2, mergedSyms)
  in

  -- Return the replacing transition between q and p when s is removed
  let replaceTrans = lam dfa. lam p. lam s. lam q.
    let psRE = (head (nfaTransitionsBetween p s dfa)).2 in
    let sqRE = (head (nfaTransitionsBetween s q dfa)).2 in
    -- Loop from s to s?
    let maybeLoop = nfaTransitionsBetween s s dfa in
    let isLoop = not (null maybeLoop) in
    -- Compute Regex for p->s->q replacement
    let psqRE = if isLoop then
                  let ssRE = (head maybeLoop).2 in
                  -- PS*Q
                  Concat (psRE, Concat(Kleene(ssRE), sqRE))
                else
                  -- PQ
                  Concat (psRE, sqRE)
    in
    -- Create regex for the p->q transition
    let maybePQTrans = nfaTransitionsBetween p q dfa in
    let finalPQReg =
      if not (null maybePQTrans) then
        let pqRE = (head maybePQTrans).2 in
        Union (pqRE, psqRE)
      else
        psqRE
     in (p, q, finalPQReg)
  in

  -- Eliminate state s from the DFA
  let eliminate = lam s. lam dfa.
    -- Compute transitions to add
    let inStates = nfaInStates s dfa in
    let outStates = nfaOutStates s dfa in
    -- Filter out s from inStates and outStates
    let inStates = filter (lam i. not ((nfaGetEqv dfa) s i)) inStates in
    let outStates = filter (lam o. not ((nfaGetEqv dfa) s o)) outStates in
    let addTrans =
      foldl (lam acc. lam i.
               let newTrans = map (lam o. replaceTrans dfa i s o) outStates in
               concat acc newTrans)
      []
      inStates
    in
    -- Compute transitions to keep
    let keepTrans = filter
                    (lam t.
                       let eqv = (nfaGetEqv dfa) in
                       if eqv s t.0 then false else
                       if eqv s t.1 then false else
                       if and (eqsetMem eqv t.0 inStates)
                              (eqsetMem eqv t.1 outStates) then false
                       else true)
                    (nfaTransitions dfa)
    in
    -- Keep all the states except s
    let newStates = filter (lam st. not ((nfaGetEqv dfa) s st)) (nfaStates dfa) in
    let newTrans = concat keepTrans addTrans in
    -- Create a new dfa where s has been eliminated
    let newDFA = dfaConstr newStates newTrans (nfaStartState dfa) (nfaAcceptStates dfa) (nfaGetCmp dfa) (nfaGetEql dfa)in
    newDFA
  in

  -- Extract regex from canonical 1-state or 2-state DFA
  let regExFromGeneric = lam dfa.
    -- Get the symbol between from and to, or an empty regex if none exists
    let getSymOrEmpty = lam dfa. lam from. lam to.
      let trans = nfaTransitionsBetween from to dfa in
      match trans with [] then Empty () else
      match trans with [t] then t.2 else
      error (join ["getSymOrEmpty expected 0 or 1 transitions, was ", int2string (length trans)])

    in
    -- Handle 1-state DFA
    let generic1State = lam dfa.
      let trans = nfaTransitions dfa in
      match trans with [] then Epsilon () else
      match trans with [t] then Kleene(t.2) else
      error (join ["Expected 0 or 1 transitions in 1-state DFA, not ", int2string (length trans)])
    in
    -- Handle 2-state DFA
    let generic2State = lam dfa.
      let trans = nfaTransitions dfa in
      match trans with [] then (error (join ["Expected DFA with at least one transition"])) else
      -- Start and accept state only states left
      let p = nfaStartState dfa in
      let q = match (nfaAcceptStates dfa) with [a] then a else error "Expected DFA with exactly one accept state" in
      if (nfaGetEqv dfa) p q then error (join ["Expected start state and accept state to be different"]) else
      -- Extract the regexes from the 4 potential transitions
      let pq = getSymOrEmpty dfa p q in
      let qp = getSymOrEmpty dfa q p in
      let pp = getSymOrEmpty dfa p p in
      let qq = getSymOrEmpty dfa q q in
      -- Construct the regex
      let leftRE = Concat(pq, Kleene(qq)) in
      simplifyD (nfaGetEql dfa)
                (Concat (Kleene (Union (pp, Concat (leftRE, qp))),
                         leftRE))
    in
    let nStates = length (nfaStates dfa) in
    match nStates with 1 then generic1State dfa else
    match nStates with 2 then generic2State dfa else
    error (join ["Expected DFA of size 1 or 2, not ", int2string nStates, "."])
  in

  -- Get the regex from a DFA with one accept state
  let regexOneAccept = lam dfa. lam acceptState.
    -- Turn acceptState into the only accepting state
    let dfa = dfaConstr (nfaStates dfa) (nfaTransitions dfa) (nfaStartState dfa)
                        [acceptState] (nfaGetCmp dfa) (nfaGetEql dfa) in

    let startState = nfaStartState dfa in
    let toEliminate = filter
                      (lam s. and
                              (not ((nfaGetEqv dfa) startState s))
                              (not ((nfaGetEqv dfa) acceptState s)))
                      (nfaStates dfa) in
    -- Eliminate states and extract regex
    let finalDFA = foldl (lam accDFA. lam s. eliminate s accDFA)
                   dfa
                   toEliminate
    in
    let finalRE = regExFromGeneric finalDFA in
    finalRE
  in

  -- ** Actual Algorithm **

  -- Step 1: Initialisation.
  -- For every pair of states, merge the transitions between them and replace by a regex.
  -- Established invariant: for every pair of state, there is at most one transition between them.
  let states = nfaStates dfa in

  -- Create the merged transitions
  let mergedTrans = foldl (lam acc. lam s.
                      let mergedSuccessors =
                        map (lam s1.
                              optionGetOrElse
                                (lam. error "Expected transition between states")
                                (pairMergeTrans dfa s s1))
                            (nfaOutStates s dfa) in
                      concat acc mergedSuccessors)
                    []
                    states
  in
  -- Create the DFA with the merged transitions
  let dfa = dfaConstr states mergedTrans (nfaStartState dfa) (nfaAcceptStates dfa) (nfaGetCmp dfa) (eqr (nfaGetEql dfa)) in

  -- Step 2: State Elimination.
  -- Iteratively eliminate states and replace by regexes
  let acceptStates = nfaAcceptStates dfa in
  match acceptStates with [] then Empty () else
  match acceptStates with [a] then regexOneAccept dfa a else
  foldl (lam acc. lam astate. Union (acc, regexOneAccept dfa astate))
        (regexOneAccept dfa (head acceptStates))
        (tail acceptStates)

mexpr

let l1 = "l1" in
let l2 = "l2" in
let l3 = "l3" in
let l4 = "l4" in
let l5 = "l5" in

let r1 = Symbol l1 in
let r2 = Symbol l2 in
let r3 = Concat (r1, r2) in
let r4 = Union(Kleene(Concat(r1, r2)), Symbol(l3)) in
let r5 = Kleene (Union(Empty (), Concat (r1, Kleene (Empty ())))) in

let eqrStr = eqr eqString in
utest eqrStr r1 r1 with true in
utest eqrStr r1 r2 with false in
utest eqrStr r3 r3 with true in
utest eqrStr r3 r1 with false in
utest eqrStr r4 r3 with false in
utest eqrStr r4 r4 with true in
utest eqrStr r4 (Union(Kleene(Concat(r1, r2)), Symbol(l3))) with true in
utest eqrStr r4 (Union(Kleene(Concat(r1, r2)), Symbol(l2))) with false in

utest simplifyD eqrStr r2 with r2 in
utest simplifyD eqrStr r5 with Kleene r1 in

-- ┌───────┐  start   ╔═══╗
-- │ start │ ───────▶ ║ 1 ║
-- └───────┘          ╚═══╝
let states = [1] in
let transitions = [] in
let startState = 1 in
let acceptStates = [1] in
let dfa = dfaConstr states transitions startState acceptStates subi eqString in

utest regexFromDFA dfa with Epsilon () in

--                        l1
--                      ┌────┐
--                      ▼    │
-- ┌───────┐  start   ╔════════╗
-- │ start │ ───────▶ ║   1    ║
-- └───────┘          ╚════════╝
--                      ▲ l2 │
--                      └────┘
--
let states = [1] in
let transitions = [(1,1,l1), (1,1,l2)] in
let startState = 1 in
let acceptStates = [1] in
let dfa = dfaConstr states transitions startState acceptStates subi eqString in

-- (l1 | l2)*
utest regexFromDFA dfa with Kleene (Union (Symbol l1, Symbol l2)) in

--                      ┌────────────────┐
--                      │                │
-- ┌───────┐  start   ┌───┐  l1   ╔═══╗  │
-- │ start │ ───────▶ │   │ ────▶ ║ 2 ║  │
-- └───────┘          │   │       ╚═══╝  │
--                    │   │  l3          │ l5
--                    │ 1 │ ◀───────┐    │
--                    │   │         │    │
--                    │   │  l2   ┌───┐  │
--                    │   │ ────▶ │ 3 │ ◀┘
--                    └───┘       └───┘
--                      │   l4      ▲
--                      └───────────┘
let states = [1,2,3] in
let transitions = [(1,2,l1),(3,1,l3),(1,3,l2),(1,3,l4),(1,3,l5)] in
let startState = 1 in
let acceptStates = [2] in
let dfa = dfaConstr states transitions startState acceptStates subi eqString in

-- ((l2 | l4 | l5) l3)* l1
utest regexFromDFA dfa with Concat (Kleene (Concat (Union (Union (Symbol l2, Symbol l4), Symbol l5),
                                                    Symbol l3)),
                                    Symbol l1) in

-- Accept state same as start state
--                      ┌────────────────┐
--                      │                │
-- ┌───────┐  start   ╔═══╗  l1   ┌───┐  │
-- │ start │ ───────▶ ║   ║ ────▶ │ 2 │  │
-- └───────┘          ║   ║       └───┘  │
--                    ║   ║  l3          │ l4
--                    ║ 1 ║ ◀───────┐    │
--                    ║   ║         │    │
--                    ║   ║  l5   ┌───┐  │
--                    ║   ║ ────▶ │ 3 │ ◀┘
--                    ╚═══╝       └───┘
--                      │   l2      ▲
--                      └───────────┘
let states = [1,2,3] in
let transitions = [(1,2,l1),(3,1,l3),(1,3,l2),(1,3,l4),(1,3,l5)] in
let startState = 1 in
let acceptStates = [1] in
let dfa = dfaConstr states transitions startState acceptStates subi eqString in

-- ((l2 | l4 | l5) l3)*
utest regexFromDFA dfa with Kleene (Concat (Union (Union (Symbol l2, Symbol l4), Symbol l5),
                                            Symbol l3)) in

-- Several accept states
--
--                      ┌────────────────┐
--                      │                │
-- ┌───────┐  start   ╔═══╗  l1   ╔═══╗  │
-- │ start │ ───────▶ ║   ║ ────▶ ║ 2 ║  │
-- └───────┘          ║   ║       ╚═══╝  │
--                    ║   ║  l3          │ l4
--                    ║ 1 ║ ◀───────┐    │
--                    ║   ║         │    │
--                    ║   ║  l2   ┌───┐  │
--                    ║   ║ ────▶ │ 3 │ ◀┘
--                    ╚═══╝       └───┘
--                      │   l5      ▲
--                      └───────────┘
--
let states = [1,2,3] in
let transitions = [(1,2,l1),(3,1,l3),(1,3,l2),(1,3,l4),(1,3,l5)] in
let startState = 1 in
let acceptStates = [1,2] in
let dfa = dfaConstr states transitions startState acceptStates subi eqString in

-- (((l2 | l4 | l5) l3)*) | ((l2 | l4 | l5) l3)* l1
utest regexFromDFA dfa with Union (Kleene (Concat (Union (Union (Symbol l2, Symbol l4), Symbol l5), Symbol l3)),
                                   Concat (Kleene (Concat (Union (Union (Symbol l2, Symbol l4), Symbol l5),Symbol l3)),Symbol l1)) in

-- ┌───────┐  start   ┌───┐  a    ┌─────┐  c    ┌───┐
-- │ start │ ───────▶ │ 1 │ ────▶ │     │ ────▶ │ 3 │
-- └───────┘          └───┘       │     │       └───┘
--                                │     │  b      │
--                                │  2  │ ◀───────┘
--                                │     │
--                                │     │
--                                │     │ ◀┐
--                                └─────┘  │
--                                  │      │
--                                  │ e    │ d
--                                  ▼      │
--                                ╔═════╗  │
--                                ║  4  ║ ─┘
--                                ╚═════╝
--
let acceptStates = [4] in
let startState = 1 in
let states = [1,2,3,4] in
let transitions = [(1,2,"a"),(2,3,"c"),(2,4,"e"),(3,2,"b"),(4,2,"d")] in
let dfa = dfaConstr states transitions startState acceptStates subi eqString in

()
