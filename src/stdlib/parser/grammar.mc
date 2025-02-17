include "common.mc"
include "map.mc"
include "math.mc"
include "name.mc"
include "set.mc"
include "string.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"

-- Base language for tokens
lang TokenReprBase
  syn TokenRepr =

  sem tokReprCmp2 : (TokenRepr, TokenRepr) -> Int
  sem tokReprCmp2 =
  | (l, r) -> subi (constructorTag l) (constructorTag r)

  sem tokReprCmp l =
  | r -> tokReprCmp2 (l, r)

  sem tokReprEq : TokenRepr -> TokenRepr -> Bool
  sem tokReprEq l =
  | r -> eqi 0 (tokReprCmp l r)

  sem tokReprToStr : TokenRepr -> String
end


lang TokenReprEOF = TokenReprBase
  syn TokenRepr =
  | EOFRepr ()

  sem tokReprToStr =
  | EOFRepr _ -> "<EOF>"
end

-- TODO(johnwikman, 2023-05-13): Ast inclusion is temporary until polymorphism
-- properly works in MLang. Remove this when polymorhpism works such that the
-- type is available in the body, and generalize the Expr uses
lang ContextFreeGrammar = TokenReprBase + MExprAst + MExprCmp
  syn Term =
  | Terminal TokenRepr
  | NonTerminal Name

  type Production = {
    -- Name of the non-terminal associated with this rule
    nt: Name,
    -- The terms associated with this rule
    terms: [Term],
    -- The semantic action to take when reducing on this rule. This action
    -- expression has to be fully typed, with a type on the form
    --   tyState -> tyArg1 -> tyArg2 -> ... -> tyArgn -> tyRet
    -- where tyState is an arbitrary state type that has to be the same type
    -- for all actions in the syntax definition.
    action: Expr
  }

  type SyntaxDef = {
    entrypoint: Name,
    productions: [Production],
    -- thing that generates the initial action state, i.e. let state = <Expr> in
    initActionState: Expr
  }

  sem cfgTerm2string : Term -> String
  sem cfgTerm2string =
  | Terminal t -> tokReprToStr t
  | NonTerminal n -> join (["NT(", nameGetStr n, ")"])

  sem cfgTermCmp2 : (Term, Term) -> Int
  sem cfgTermCmp2 =
  | (Terminal t1, Terminal t2) -> tokReprCmp t1 t2
  | (NonTerminal n1, NonTerminal n2) -> nameCmp n1 n2
  | (l, r) -> subi (constructorTag l) (constructorTag r)

  sem cfgTermCmp : Term -> Term -> Int
  sem cfgTermCmp other =
  | t -> cfgTermCmp2 (other, t)

  sem cfgTermEq : Term -> Term -> Bool
  sem cfgTermEq other =
  | t -> eqi (cfgTermCmp other t) 0

  -- Comparison between two grammars. This ignores the order in which
  -- productions are specified, but is strict in the naming equivalence.
  sem cfgCmp2 : (SyntaxDef, SyntaxDef) -> Int
  sem cfgCmp2 =
  | (l, r) ->
    -- OPT(johnwikman, 2023-05-15): We could try to set up a bijection between
    -- names of non-terminals in both grammars, which would allow for semantic
    -- equivalence between the grammars instead of just considering a more
    -- structural one. But maybe this should be its own comparison function.
    let cEntrypoint = nameCmp l.entrypoint r.entrypoint in
    if neqi cEntrypoint 0 then cEntrypoint else --continue
    let cInitActionState = cmpExpr l.initActionState r.initActionState in
    if neqi cInitActionState 0 then cInitActionState else --continue

    let prodCmp: Production -> Production -> Int = lam lp. lam rp.
      let cNt = nameCmp lp.nt rp.nt in
      if neqi cNt 0 then cNt else --continue
      let cTerms = seqCmp cfgTermCmp lp.terms rp.terms in
      if neqi cTerms 0 then cTerms else --continue
      cmpExpr lp.action rp.action
    in
    let lprods = sort prodCmp l.productions in
    let rprods = sort prodCmp r.productions in
    seqCmp prodCmp lprods rprods

  sem cfgCmp : SyntaxDef -> SyntaxDef -> Int
  sem cfgCmp other =
  | syntaxDef -> cfgCmp2 (other, syntaxDef)

  sem cfgEq : SyntaxDef -> SyntaxDef -> Bool
  sem cfgEq other =
  | syntaxDef -> eqi (cfgCmp other syntaxDef) 0


  sem cfg2string : SyntaxDef -> String
  sem cfg2string =
  | syntaxDef ->
    let m = foldl (lam m: Map Name [Production]. lam prod: Production.
      mapInsertWith concat prod.nt [prod] m
    ) (mapEmpty nameCmp) syntaxDef.productions in

    let lines = mapFoldWithKey (lam lines. lam name. lam prods.
      -- separating newline
      let lines = if null lines then lines else snoc lines "" in
      -- <name> ::= TERMS
      --          | TERMS
      let firstLinePrefix = join [nameGetStr name, " ::= "] in
      let nextLinePrefix = join [make (subi (length firstLinePrefix) 2) ' ', "| "] in
      foldli (lam lines. lam i. lam prod.
        let prodStr = strJoin " " (map cfgTerm2string prod.terms) in
        let prefix = if eqi i 0 then firstLinePrefix else nextLinePrefix in
        snoc lines (concat prefix prodStr)
      ) lines prods
    ) [] m in
    strJoin "\n" lines


  -- The ComposeFirst_n(FIRST_k, a1...an) function for any sequence of terms a1 to an
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
  sem cfgComposeFirst: Int -> Map Term (Set [TokenRepr]) -> [Term] -> Set [TokenRepr]
  sem cfgComposeFirst n firstMap =
  | [y1] ->
    -- Return first n from the firstMap
    setFold (lam acc: Set [TokenRepr]. lam y1_tokens: [TokenRepr].
    setInsert (subsequence y1_tokens 0 n) acc
    ) (setEmpty (seqCmp tokReprCmp)) (mapLookupOrElse (lam. setEmpty (seqCmp tokReprCmp)) y1 firstMap)
  | [y1, y2] ++ rest ->
    setFold (lam acc: Set [TokenRepr]. lam y1_tokens: [TokenRepr].
    if geqi (length y1_tokens) n then
      setInsert (subsequence y1_tokens 0 n) acc
    else
      setFold (lam acc: Set [TokenRepr]. lam rest_tokens: [TokenRepr].
        setInsert (concat y1_tokens rest_tokens) acc
      ) acc (cfgComposeFirst (subi n (length y1_tokens)) firstMap (cons y2 rest))
    ) (setEmpty (seqCmp tokReprCmp)) (mapLookupOrElse (lam. setEmpty (seqCmp tokReprCmp)) y1 firstMap)
  | [] ->
    setInsert [] (setEmpty (seqCmp tokReprCmp))


  -- Constructs the FIRST(k) set for any syntax definition
  sem cfgFirstK : Int -> SyntaxDef -> Map Term (Set [TokenRepr])
  sem cfgFirstK k =
  | syntaxDef ->
    -- Compile a set of all terms in the syntax definition
    let allTerms: Set Term = foldl (lam acc: Set Term. lam production: Production.
      let acc = setInsert (NonTerminal production.nt) acc in
      foldl (lam acc: Set Term. lam term: Term. setInsert term acc) acc production.terms
    ) (setEmpty cfgTermCmp) syntaxDef.productions in

    -- Initialize FIRST_k:
    --   for all terminals t:
    --     FIRSK_k(t) = {[t]}
    --   for all non-terminals S:
    --     FIRST_k(S) = {}
    let firstK: Map Term (Set [TokenRepr]) = setFold (lam acc: Map Term (Set [TokenRepr]). lam term: Term.
      switch term
      case Terminal t then mapInsert term (setInsert [t] (setEmpty (seqCmp tokReprCmp))) acc
      case NonTerminal _ then mapInsert term (setEmpty (seqCmp tokReprCmp)) acc
      end
    ) (mapEmpty cfgTermCmp) allTerms in

    -- loop until convergence:
    --   for each production S -> Y_1 Y_2 ... Y_n do:
    --     if n = 0:
    --       FIRST_k(S) <- FIRST_k(S) U {[]}  -- empty production
    --     else if for all Y_i, FIRST_k(Y_i) != ø:
    --       FIRST_k(S) <- FIRST_k(S) U ComposeFirst_k(FIRST_k, [Y_1,Y_2,...,Y_n])
    recursive let iterate = lam firstMap: Map Term (Set [TokenRepr]).
      let resultMap = foldl (lam firstMap: Map Term (Set [TokenRepr]). lam production: Production.
        if eqi (length production.terms) 0 then
          mapInsertWith setUnion (NonTerminal production.nt) (setInsert [] (setEmpty (seqCmp tokReprCmp))) firstMap
        else if any (lam term: Term. setIsEmpty (mapLookupOrElse (lam. setEmpty (seqCmp tokReprCmp)) term firstMap)) production.terms then
          firstMap -- one of symbols for these productions lack an instance of firskK, skip this for now
        else
          mapInsertWith setUnion (NonTerminal production.nt) (cfgComposeFirst k firstMap production.terms) firstMap
      ) firstMap (syntaxDef.productions) in
      if mapEq setEq resultMap firstMap then
        resultMap
      else
        iterate resultMap
    in
    iterate firstK


  -- Removes all productions that are unreachable from the entrypoint
  sem cfgRemoveUnreachable : SyntaxDef -> SyntaxDef
  sem cfgRemoveUnreachable =
  | syntaxDef ->
    let ntToIdx : Map Name [Int] = foldli (lam m. lam i. lam prod: Production.
      mapInsertWith concat prod.nt [i] m
    ) (mapEmpty nameCmp) syntaxDef.productions in
    let visited : Set Name = setEmpty nameCmp in
    let visited = setInsert syntaxDef.entrypoint visited in
    let idxQueue = mapLookupOr [] syntaxDef.entrypoint ntToIdx in
    recursive let iterate = lam idxQueue. lam visited.
      match idxQueue with [idx] ++ idxQueue then
        let prod: Production = get syntaxDef.productions idx in
        match foldl (lam acc. lam term.
          match acc with (visited, idxQueue) in
          match term with NonTerminal nt then
            if not (setMem nt visited) then
              let visited = setInsert nt visited in
              let idxQueue = concat idxQueue (mapLookupOr [] nt ntToIdx) in
              (visited, idxQueue)
            else acc
          else acc
        ) (visited, idxQueue) prod.terms with (visited, idxQueue) in
        iterate idxQueue visited
      else
        visited
    in
    let visited = iterate idxQueue visited in
    {syntaxDef with productions = filter (lam prod. setMem prod.nt visited) syntaxDef.productions}


  -- A stronger version of cfgRemoveUnreachable. Also removes any productions
  -- that contain non-terminals without any production.
  --
  -- loop until convergence:
  --   R <- reachable non-terminals in Grammar G
  --   G <- remove productions in G that references a non-terminal not in R
  sem cfgRemoveUnparsable : SyntaxDef -> SyntaxDef
  sem cfgRemoveUnparsable =
  | syntaxDef ->
    recursive let convergenceLoop = lam syntaxDef: SyntaxDef.
      let ntToIdx : Map Name [Int] = foldli (lam m. lam i. lam prod: Production.
        mapInsertWith concat prod.nt [i] m
      ) (mapEmpty nameCmp) syntaxDef.productions in
      -- Step 1, identify all reachable productions
      let visited : Set Name = setEmpty nameCmp in
      let idxQueue = mapLookupOr [] syntaxDef.entrypoint ntToIdx in
      let queued = setInsert syntaxDef.entrypoint visited in
      recursive let iterate = lam idxQueue. lam queued. lam visited.
        match idxQueue with [idx] ++ idxQueue then
          let prod: Production = get syntaxDef.productions idx in
          let visited = setInsert prod.nt visited in
          match foldl (lam acc. lam term.
            match acc with (queued, idxQueue) in
            match term with NonTerminal nt then
              if not (setMem nt queued) then
                let idxQueue = concat idxQueue (mapLookupOr [] nt ntToIdx) in
                (queued, idxQueue)
              else acc
            else acc
          ) (queued, idxQueue) prod.terms with (queued, idxQueue) in
          iterate idxQueue queued visited
        else
          visited
      in
      let visited = iterate idxQueue queued visited in
      -- Step 2, strip any production with references to unseen non-terminals
      let visitedTerm = lam t: Term. match t with NonTerminal nt then setMem nt visited else true in
      match foldl (lam acc. lam prod.
        match acc with (modified, newProductions) in
        if and (setMem prod.nt visited) (forAll visitedTerm prod.terms) then
          (modified, snoc newProductions prod)
        else
          (true, newProductions) -- modified, removed production
      ) (false, []) syntaxDef.productions with (modified, newProductions) in
      if modified then
        convergenceLoop {syntaxDef with productions = newProductions}
      else
        syntaxDef
    in
    convergenceLoop syntaxDef
end




lang GrammarTestLanguage = TokenReprBase + TokenReprEOF + ContextFreeGrammar
  syn TokenRepr =
  | LParenRepr ()
  | RParenRepr ()
  | PlusRepr ()
  | TimesRepr ()
  | IntRepr ()

  sem tokReprToStr =
  | LParenRepr _ -> "<LParen>"
  | RParenRepr _ -> "<RParen>"
  | PlusRepr _ -> "<Plus>"
  | TimesRepr _ -> "<Times>"
  | IntRepr _ -> "<INT>"
end


mexpr

use GrammarTestLanguage in

let t_EOF = Terminal (EOFRepr {}) in
let t_LParen = Terminal (LParenRepr {}) in
let t_RParen = Terminal (RParenRepr {}) in
let t_Plus = Terminal (PlusRepr {}) in
let t_Times = Terminal (TimesRepr {}) in
let t_Int = Terminal (IntRepr {}) in

let _Ex = nameSym "Example" in
let _Ex2 = nameSym "Example2" in
let _Ex3 = nameSym "Example3" in
let _Ex4 = nameSym "Example4" in
let nt_Ex = NonTerminal _Ex in
let nt_Ex2 = NonTerminal _Ex2 in
let nt_Ex3 = NonTerminal _Ex3 in
let nt_Ex4 = NonTerminal _Ex4 in

utest cfgTermCmp t_EOF t_EOF with 0 using eqSign in
utest cfgTermCmp nt_Ex nt_Ex with 0 using eqSign in
utest cfgTermCmp t_EOF t_RParen with 0 using neqi in
utest cfgTermCmp t_RParen t_EOF with cfgTermCmp t_EOF t_RParen using neqSign in
utest cfgTermCmp t_EOF nt_Ex with 0 using neqi in
utest cfgTermCmp nt_Ex t_EOF with cfgTermCmp t_EOF nt_Ex using neqSign in
utest cfgTermCmp nt_Ex2 nt_Ex with 0 using neqi in
utest cfgTermCmp nt_Ex nt_Ex2 with cfgTermCmp nt_Ex2 nt_Ex using neqSign in

utest cfgTermEq t_EOF t_EOF with true in
utest cfgTermEq nt_Ex nt_Ex with true in
utest cfgTermEq nt_Ex t_EOF with false in

-- A == B, but C != A
let gramA: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [t_Plus], action = unit_},
    {nt = _Ex2, terms = [t_Times], action = unit_}
  ],
  initActionState = unit_
} in
let gramB: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex2, terms = [t_Plus], action = unit_},
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [t_Times], action = unit_}
  ],
  initActionState = unit_
} in
let gramC: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [nt_Ex], action = unit_},
    {nt = _Ex2, terms = [t_Times], action = unit_}
  ],
  initActionState = unit_
} in

utest cfgCmp gramA gramA with 0 using eqSign in
utest cfgCmp gramA gramB with 0 using eqSign in
utest cfgCmp gramB gramA with 0 using eqSign in
utest cfgCmp gramA gramC with 0 using neqi in
utest cfgCmp gramA gramC with cfgCmp gramC gramA using neqSign in
utest cfgCmp gramB gramC with 0 using neqi in
utest cfgCmp gramB gramC with cfgCmp gramC gramB using neqSign in

utest cfgEq gramA gramA with true in
utest cfgEq gramA gramB with true in
utest cfgEq gramB gramA with true in
utest cfgEq gramA gramC with false in
utest cfgEq gramC gramA with false in
utest cfgEq gramB gramC with false in
utest cfgEq gramC gramB with false in


let tokEmptyTy = tyrecord_ [("info", tycon_ "Info")] in
let tokStrvalTy = tyrecord_ [("info", tycon_ "Info"), ("val", tystr_)] in
let tokIntvalTy = tyrecord_ [("info", tycon_ "Info"), ("val", tyint_)] in

let mkFirstEntry: Term -> [[Term]] -> (Term, Set [TokenRepr]) = lam term. lam firsts.
  (term, setOfSeq (seqCmp tokReprCmp) (map (map (lam t.
           match t with Terminal x then x else error "expected terminals only in firsts")
         ) firsts))
in

let mkFirsts: [(Term, [[Term]])] -> Map Term (Set [TokenRepr]) = lam firstlist.
  mapFromSeq cfgTermCmp (map (lam t.
    match t with (term, fsts) in
    mkFirstEntry term fsts
  ) firstlist)
in

let first2string: Int -> Map Term (Set [TokenRepr]) -> String = lam k. lam firstMap.
  let lines = mapFoldWithKey (lam lines. lam term: Term. lam first: Set [TokenRepr].
    match term with NonTerminal _ then
      let lines = snoc lines (join ["First_", int2string k, "(", cfgTerm2string term, "):"]) in
      setFold (lam lines. lam tokens: [TokenRepr].
        snoc lines (join ["  [", strJoin ", " (map tokReprToStr tokens), "]"])
      ) lines first
    else
      lines
  ) [] firstMap in
  strJoin "\n" lines
in


type FirstKTestCase = {
  name: String,
  syntaxDef: SyntaxDef,
  first1: Map Term (Set [TokenRepr]),
  first2: Map Term (Set [TokenRepr]),
  first3: Map Term (Set [TokenRepr])
} in


let firstKTestCases: [FirstKTestCase] = [
  let _Expr = nameSym "Expr" in
  let _Term = nameSym "Term" in
  let _Factor = nameSym "Factor" in
  let nt_Expr = NonTerminal _Expr in
  let nt_Term = NonTerminal _Term in
  let nt_Factor = NonTerminal _Factor in
  {
    name = "Calculator Syntax",
    syntaxDef = {
      entrypoint = _Expr,
      productions = [
        { nt = _Expr, terms = [nt_Expr, t_Plus, nt_Term],
          action = withType (tyarrows_ [tyunit_, tyint_, tokEmptyTy, tyint_, tyint_])
                            (ulams_ ["actionState", "l", "op", "r"]
                                    (addi_ (var_ "l") (var_ "r")))},
        { nt = _Expr, terms = [nt_Term],
          action = withType (tyarrows_ [tyunit_, tyint_, tyint_])
                            (ulams_ ["actionState", "t"]
                                    (var_ "t"))},
        { nt = _Term, terms = [nt_Term, t_Times, nt_Factor],
          action = withType (tyarrows_ [tyunit_, tyint_, tokEmptyTy, tyint_, tyint_])
                            (ulams_ ["actionState", "l", "op", "r"]
                                    (muli_ (var_ "l") (var_ "r")))},
        { nt = _Term, terms = [nt_Factor],
          action = withType (tyarrows_ [tyunit_, tyint_, tyint_])
                            (ulams_ ["actionState", "f"]
                                    (var_ "f"))},
        { nt = _Factor, terms = [t_Int],
          action = withType (tyarrows_ [tyunit_, tokIntvalTy, tyint_])
                            (ulams_ ["actionState", "i"]
                                    (recordproj_ "val" (var_ "i")))},
        { nt = _Factor, terms = [t_LParen, nt_Expr, t_RParen],
          action = withType (tyarrows_ [tyunit_, tokEmptyTy, tyint_, tokEmptyTy, tyint_])
                            (ulams_ ["actionState", "lp", "e", "rp"]
                                    (var_ "e"))}
      ],
      initActionState = unit_
    },
    first1 = mkFirsts [
      (t_Plus,   [[t_Plus]]),
      (t_Times,  [[t_Times]]),
      (t_Int,    [[t_Int]]),
      (t_LParen, [[t_LParen]]),
      (t_RParen, [[t_RParen]]),
      (nt_Expr,   [[t_Int], [t_LParen]]),
      (nt_Term,   [[t_Int], [t_LParen]]),
      (nt_Factor, [[t_Int], [t_LParen]])
    ],
    first2 = mkFirsts [
      (t_Plus,   [[t_Plus]]),
      (t_Times,  [[t_Times]]),
      (t_Int,    [[t_Int]]),
      (t_LParen, [[t_LParen]]),
      (t_RParen, [[t_RParen]]),
      (nt_Expr,   [[t_Int], [t_LParen, t_LParen], [t_LParen, t_Int],
                   [t_Int, t_Plus], [t_Int, t_Times]]),
      (nt_Term,   [[t_Int], [t_LParen, t_LParen], [t_LParen, t_Int],
                   [t_Int, t_Times]]),
      (nt_Factor, [[t_Int], [t_LParen, t_LParen], [t_LParen, t_Int]])
    ],
    first3 = mkFirsts [
      (t_Plus,   [[t_Plus]]),
      (t_Times,  [[t_Times]]),
      (t_Int,    [[t_Int]]),
      (t_LParen, [[t_LParen]]),
      (t_RParen, [[t_RParen]]),
      (nt_Expr,   [[t_Int], [t_LParen, t_LParen, t_LParen], [t_LParen, t_LParen, t_Int],
                   [t_LParen, t_Int, t_RParen], [t_LParen, t_Int, t_Plus], [t_LParen, t_Int, t_Times],
                   [t_Int, t_Times, t_Int], [t_Int, t_Times, t_LParen],
                   [t_Int, t_Plus, t_Int], [t_Int, t_Plus, t_LParen]]),
      (nt_Term,   [[t_Int], [t_LParen, t_LParen, t_LParen], [t_LParen, t_LParen, t_Int],
                   [t_LParen, t_Int, t_RParen], [t_LParen, t_Int, t_Plus], [t_LParen, t_Int, t_Times],
                   [t_Int, t_Times, t_Int], [t_Int, t_Times, t_LParen]]),
      (nt_Factor, [[t_Int], [t_LParen, t_LParen, t_LParen], [t_LParen, t_LParen, t_Int],
                   [t_LParen, t_Int, t_RParen], [t_LParen, t_Int, t_Plus], [t_LParen, t_Int, t_Times]])
    ]
  },
  let _LeftOnly = nameSym "LeftOnly" in
  let _LeftRight = nameSym "LeftRight" in
  let nt_LeftOnly = NonTerminal _LeftOnly in
  let nt_LeftRight = NonTerminal _LeftRight in
  {
    name = "non-LL Example (more left parentheses than right parentheses)",
    syntaxDef = {
      entrypoint = _LeftOnly,
      productions = [
        {nt = _LeftOnly, terms = [t_LParen, nt_LeftOnly],
         action = withType (tyarrows_ [tyunit_, tokEmptyTy, tystr_, tystr_])
                           (ulams_ ["actionState", "lparen", "lprod"]
                                   (cons_ (char_ '(') (var_ "lprod")))},
        {nt = _LeftOnly, terms = [nt_LeftRight],
         action = withType (tyarrows_ [tyunit_, tystr_, tystr_])
                           (ulams_ ["actionState", "lrprod"]
                                   (cons_ (char_ '|') (var_ "lrprod")))},
        {nt = _LeftRight, terms = [t_LParen, nt_LeftRight, t_RParen],
         action = withType (tyarrows_ [tyunit_, tokEmptyTy, tystr_, tokEmptyTy, tystr_])
                           (ulams_ ["actionState", "lparen", "middle", "rparen"]
                                   (cons_ (char_ '(') (snoc_ (var_ "middle") (char_ ')'))))},
        {nt = _LeftRight, terms = [],
         action = withType (tyarrows_ [tyunit_, tystr_])
                           (ulams_ ["actionState"]
                                   (str_ "e"))}
      ],
      initActionState = unit_
    },
    first1 = mkFirsts [
      (t_LParen, [[t_LParen]]),
      (t_RParen, [[t_RParen]]),
      (nt_LeftOnly, [[t_LParen], []]),
      (nt_LeftRight, [[t_LParen], []])
    ],
    first2 = mkFirsts [
      (t_LParen, [[t_LParen]]),
      (t_RParen, [[t_RParen]]),
      (nt_LeftOnly, [[t_LParen, t_LParen], [t_LParen, t_RParen],
                     [t_LParen], []]),
      (nt_LeftRight, [[t_LParen, t_LParen], [t_LParen, t_RParen],
                      []])
    ],
    first3 = mkFirsts [
      (t_LParen, [[t_LParen]]),
      (t_RParen, [[t_RParen]]),
      (nt_LeftOnly, [[t_LParen, t_LParen, t_LParen], [t_LParen, t_RParen],
                     [t_LParen, t_LParen, t_RParen],
                     [t_LParen, t_LParen], [t_LParen, t_RParen],
                     [t_LParen], []]),
      (nt_LeftRight, [[t_LParen, t_LParen, t_LParen], [t_LParen, t_RParen],
                      [t_LParen, t_LParen, t_RParen], []])
    ]
  }
] in

let suppressPrints = true in
let tprint = lam s. if suppressPrints then () else print s in
let tprintLn = lam s. if suppressPrints then () else printLn s in

-- Run FirstK tests
foldl (lam. lam tc: FirstKTestCase.
  tprintLn (join ["------------- ", tc.name, " -------------"]);
  tprintLn (cfg2string tc.syntaxDef);
  tprintLn (cons '\n' (first2string 1 (cfgFirstK 1 tc.syntaxDef)));
  tprintLn (cons '\n' (first2string 2 (cfgFirstK 2 tc.syntaxDef)));
  tprintLn (cons '\n' (first2string 3 (cfgFirstK 3 tc.syntaxDef)));
  utest cfgFirstK 1 tc.syntaxDef with tc.first1 using mapEq setEq in
  utest cfgFirstK 2 tc.syntaxDef with tc.first2 using mapEq setEq in
  utest cfgFirstK 3 tc.syntaxDef with tc.first3 using mapEq setEq in
  tprintLn ""
) () firstKTestCases;


-- Testing removing unreachable productions
let gramA: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [t_Plus], action = unit_},
    {nt = _Ex2, terms = [t_Times], action = unit_}
  ],
  initActionState = unit_
} in
let gramB: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [t_Plus], action = unit_},
    {nt = _Ex2, terms = [t_Times], action = unit_},
    {nt = _Ex3, terms = [t_Plus, nt_Ex, t_Plus], action = unit_},
    {nt = _Ex3, terms = [nt_Ex4], action = unit_}
  ],
  initActionState = unit_
} in
let strippedGramB = cfgRemoveUnreachable gramB in

utest cfgEq gramA gramB with false in
utest cfgEq gramA strippedGramB with true in


-- Testing removing unparsable productions
let gramA: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [t_Plus], action = unit_},
    {nt = _Ex2, terms = [t_Times], action = unit_}
  ],
  initActionState = unit_
} in
let gramB: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [t_Plus], action = unit_},
    {nt = _Ex2, terms = [t_Times], action = unit_},
    {nt = _Ex2, terms = [t_LParen, nt_Ex3, t_RParen], action = unit_},
    {nt = _Ex3, terms = [nt_Ex4], action = unit_}
  ],
  initActionState = unit_
} in
let gramC: SyntaxDef = {
  entrypoint = _Ex,
  productions = [
    {nt = _Ex, terms = [t_LParen, nt_Ex2, t_RParen], action = unit_},
    {nt = _Ex2, terms = [t_LParen, nt_Ex3, t_RParen], action = unit_},
    {nt = _Ex3, terms = [nt_Ex4], action = unit_}
  ],
  initActionState = unit_
} in
let strippedGramB = cfgRemoveUnparsable gramB in
let strippedGramC = cfgRemoveUnparsable gramC in

utest cfgEq gramA gramB with false in
utest cfgEq gramA strippedGramB with true in
utest cfgEq {gramA with productions = []} strippedGramC with true in


()
