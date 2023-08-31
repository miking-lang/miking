-- A parser generator for LR(k >= 1).
--
-- The implementation is based on the algorithm for LR(1) described in the book
-- by Appel (2002), but extended to LR(k). This parser generator does not work
-- for LR(0) since the implemented lookahead checks for LR(k) is not compatible
-- with the shift semantics of LR(0).

include "bool.mc"
include "common.mc"
include "error.mc"
include "map.mc"
include "math.mc"
include "name.mc"
include "option.mc"
include "result.mc"
include "seq.mc"
include "set.mc"
include "sys.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/cmp.mc"
include "mexpr/info.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/type-check.mc"
include "ocaml/mcore.mc"

include "grammar.mc"
include "lexer.mc"

lang LRParser = ContextFreeGrammar + TokenReprEOF + MExprAst + MExprCmp
  type LRStateItem = {
    nt: Name,
    terms: [Term],
    stackPointer: Int,
    lookahead: [TokenRepr],
    prodIdx: Int -- index of the rule that this item originates from
  }

  type LRState = Set LRStateItem

  type LRParseTable = {
    -- k_lookahead as in LR(k)
    k_lookahead: Int,
    -- Index of the initial LR state
    entrypointIdx: Int,
    entrypointProdIdx: Int,
    -- The original syntax definition
    syntaxDef: SyntaxDef,
    -- Types for non-terminal symbols and tokens
    nonTerminalTypes: Map Name Type,
    tokenConTypes: Map TokenRepr {conIdent: Name, conArg: Type},
    -- The generated LR states, shifts, gotos, and reductions
    states: [Set LRStateItem],
    shifts: Map Int [{lookahead: [TokenRepr], toIdx: Int}],
    gotos: Map Int [{nt: Name, toIdx: Int}],
    reductions: Map Int [{lookahead: [TokenRepr], prodIdx: Int}]
  }


  sem lrStateItemCmp2 : (LRStateItem, LRStateItem) -> Int
  sem lrStateItemCmp2 =
  | (lhs, rhs) ->
    let cName = nameCmp lhs.nt rhs.nt in
    if neqi cName 0 then cName else
    let cTerms = seqCmp cfgTermCmp lhs.terms rhs.terms in
    if neqi cTerms 0 then cTerms else
    let cStackPointer = subi lhs.stackPointer rhs.stackPointer in
    if neqi cStackPointer 0 then cStackPointer else
    let cLookahead = seqCmp tokReprCmp lhs.lookahead rhs.lookahead in
    if neqi cLookahead 0 then cLookahead else
    let cRuleIdx = subi lhs.prodIdx rhs.prodIdx in
    cRuleIdx


  sem lrStateItemCmp : LRStateItem -> LRStateItem -> Int
  sem lrStateItemCmp lhs =
  | rhs -> lrStateItemCmp2 (lhs, rhs)


  -- Computes the closure for the input set as
  -- Closure(I) =
  --   repeat
  --     for any item (A -> a.Xb, L) in I
  --       for any production X -> y
  --         for any W in FIRST_k (bL)
  --           I <- I U {(X -> .y, W)}
  --   until I does not change
  --   return I
  sem lrClosure: Int -> SyntaxDef -> Map Term (Set [TokenRepr]) -> Set LRStateItem -> Set LRStateItem
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
          let bL: [Term] = concat b (map (lam t. Terminal t) item.lookahead) in
          let firstK_bL: Set [TokenRepr] = cfgComposeFirst k firstMap bL in
          foldli (lam accSet: Set LRStateItem. lam prodIdx: Int. lam prod: Production.
            if nameEq x prod.nt then
              -- Process this production
              setFold (lam accSet: Set LRStateItem. lam w: [TokenRepr].
                let newItem: LRStateItem = {
                  nt = x,
                  terms = prod.terms,
                  stackPointer = 0,
                  lookahead = w,
                  prodIdx = prodIdx
                } in
                setInsert newItem accSet
              ) accSet firstK_bL
            else
              accSet
          ) accSet syntaxDef.productions
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
  sem lrGoto: Int -> SyntaxDef -> Map Term (Set [TokenRepr]) -> Set LRStateItem -> Term -> Set LRStateItem
  sem lrGoto k syntaxDef firstMap inSet =
  | x ->
    let j = setFold (lam jAcc: Set LRStateItem. lam item: LRStateItem.
      if lti item.stackPointer (length item.terms) then
        if cfgTermEq x (get item.terms item.stackPointer) then
          setInsert {item with stackPointer = addi item.stackPointer 1} jAcc
        else
          jAcc
      else
        jAcc
    ) (setEmpty lrStateItemCmp) inSet in
    lrClosure k syntaxDef firstMap j


  /-
  -- Generate the LR(k) parse table.
  --
  -- Arguments:
  --  - k: Int
  --      Lookahead for the parser. Must be greater than or equal to 1.
  --  - tokenConTypes: Map TokenRepr {conIdent: Name, conArg: Type}
  --      A lookup for each token representation to its constructor name in the
  --      tokenType ADT as well as the type of its argument.
  --  - syntaxDef: SyntaxDef
  --      The syntax definition for the grammar to be parsed. See documentation
  --      for Production for how each rule must be specified.
  --
  -- Returns:
  --   A result type containing the generated parse table on success. Otherwise
  --   a list of errors.
  -/
  sem lrCreateParseTable: Int -> Map TokenRepr {conIdent: Name, conArg: Type} -> SyntaxDef -> Result String String LRParseTable
  sem lrCreateParseTable k tokenConTypes =
  | syntaxDef ->
    let nonTerminalTypesResult = foldl (lam acc: ([Name], Map Name Type). lam prod: Production.
      recursive let getFinalType = lam ty: Type.
        match ty with TyArrow r then getFinalType r.to else ty
      in
      match acc with (errs, mapAcc) in
      match mapLookup prod.nt mapAcc with Some prevTy then
        if neqi 0 (cmpTypeH (prevTy, getFinalType (tyTm prod.action))) then
          (snoc errs prod.nt, mapAcc)
        else
          acc
      else
        (errs, mapInsert prod.nt (getFinalType (tyTm prod.action)) mapAcc)
    ) ([], mapEmpty nameCmp) syntaxDef.productions in
    match nonTerminalTypesResult with (([_] ++ _) & errs, _) then
      result.err (join ["Conflicting types for the non-terminal(s): ", strJoin ", " (map nameGetStr (distinct nameEq errs))])
    else match nonTerminalTypesResult with (_, nonTerminalTypes) in

    -- Type-check the type signature, make sure the production function
    -- correspond to the types of the symbols that it consumes
    let ruleArgTypesResult = foldli (lam errs: [String]. lam prodIdx: Int. lam prod: Production.
      recursive let getArgTypes = lam acc: [Type]. lam ty: Type.
        match ty with TyArrow r
          then getArgTypes (snoc acc r.from) r.to
          else acc -- skip the final return type
      in
      let argtypes = getArgTypes [] (tyTm prod.action) in
      if neqi (length argtypes) (addi 1 (length prod.terms)) then
        snoc errs (join [
          "Argument type mismatch for production ", int2string prodIdx, ". Got ",
          int2string (length argtypes), " argument in production function, expected ",
          int2string (addi 1 (length prod.terms)), " arguments."
        ])
      else --continue
      let stackTypes = tail argtypes in -- these can be part of arguments on the stack
      let maybeErrs = zipWith (lam term: Term. lam ty: Type.
        switch term
        case NonTerminal n then
          match mapLookup n nonTerminalTypes with Some ntType then
            if neqi 0 (cmpTypeH (ty, ntType))
              then
                use MExprPrettyPrint in
                let env = pprintEnvEmpty in
                Some (join [
                  "Type mismatch for non-terminal \"", nameGetStr n, "\", between ",
                  (getTypeStringCode 0 env ty).1, " and ", (getTypeStringCode 0 env ntType).1, "."])
              else None ()
          else
            Some (join ["Unrecognized non-terminal \"", nameGetStr n, "\""])
        case Terminal t then
          -- NOTE(johnwikman, 2022-01-20): Maybe we want more than one type for tokens?
          match mapLookup t tokenConTypes with Some tokCon then
            if neqi 0 (cmpTypeH (ty, tokCon.conArg))
              then
                use MExprPrettyPrint in
                let env = pprintEnvEmpty in
                Some (join ["Type mismatch for token ", tokReprToStr t, ", between ",
                (getTypeStringCode 0 env ty).1, " and ", (getTypeStringCode 0 env tokCon.conArg).1, "."])
              else None ()
          else
            Some (join ["could not find a type for token ", tokReprToStr t])
        end
      ) prod.terms stackTypes in
      match filterOption maybeErrs with ([_] ++ _) & actualErrs then
        snoc errs (strJoin "\n - " (
          cons (join ["Argument type mismatch for rule ", int2string prodIdx, ":"])
               actualErrs
        ))
      else
        errs
    ) [] syntaxDef.productions in
    match ruleArgTypesResult with ([_] ++ _) & errs then
      result.err (strJoin "\n" errs)
    else -- Types are OK! Continue

    let _noEOFtype = nameSym "NoEOF" in
    let entryType = mapLookupOrElse (lam. tyunknown_) syntaxDef.entrypoint nonTerminalTypes in
    let eofCon = mapLookupOrElse (lam. {conIdent = _noEOFtype, conArg = tyunknown_}) (EOFRepr {}) tokenConTypes in

    if nameEq eofCon.conIdent _noEOFtype then
      result.err "No type provided for EOF tokens"
    else --continue

    -- create the entrypoint production
    let initProd: Production = {
      nt = nameSym "_entrypoint_",
      terms = [NonTerminal syntaxDef.entrypoint, Terminal (EOFRepr {})],
      action = let entryArgName = nameSym "entryArg" in
               withType (tyarrows_ [tyunknown_, entryType, eofCon.conArg, entryType])
                        (nlams_ [(nameNoSym "state", tyunknown_),
                                 (entryArgName, entryType),
                                 (nameNoSym "eofToken", eofCon.conArg)]
                                (nvar_ entryArgName))
    } in
    let syntaxDef = {syntaxDef with productions = snoc syntaxDef.productions initProd} in
    let nonTerminalTypes = mapInsert initProd.nt entryType nonTerminalTypes in
    let firstK: Map Term (Set [TokenRepr]) = cfgFirstK k syntaxDef in

    if not (mapAll (lam fst. not (setIsEmpty fst)) firstK) then
      result.err ("Invalid grammar. The FIRST set is not defined for one or more of its non-terminals.")
    else --continue

    let initState: Set LRStateItem = setInsert {
      nt = initProd.nt,
      terms = initProd.terms,
      stackPointer = 0,
      lookahead = make k (EOFRepr {}),
      prodIdx = subi (length syntaxDef.productions) 1 -- We inserted the initial rule at the back
    } (setEmpty lrStateItemCmp) in
    let initState: Set LRStateItem = lrClosure k syntaxDef firstK initState in
    let table: LRParseTable = {
      k_lookahead = k,
      entrypointIdx = 0,
      entrypointProdIdx = subi (length syntaxDef.productions) 1, -- We inserted the initial rule at the back
      syntaxDef = syntaxDef,
      nonTerminalTypes = nonTerminalTypes,
      tokenConTypes = tokenConTypes,
      states = [initState],
      shifts = mapEmpty subi,
      gotos = mapEmpty subi,
      reductions = mapEmpty subi
    } in

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

    -- Iterate to create all states and transitions
    recursive let iterate = lam table: LRParseTable. lam stateIdxLookup: Map (Set LRStateItem) Int. lam nextStateIdx: Int.
      if geqi nextStateIdx (length table.states) then
        table
      else --continue
      let state = get table.states nextStateIdx in

      let cmpShift = lam lhs. lam rhs.
        let cLookahead = seqCmp tokReprCmp lhs.lookahead rhs.lookahead in
        if neqi cLookahead 0 then cLookahead
        else subi lhs.toIdx rhs.toIdx
      in
      let cmpGoto = lam lhs. lam rhs.
        let cName = nameCmp lhs.nt rhs.nt in
        if neqi cName 0 then cName
        else subi lhs.toIdx rhs.toIdx
      in

      let result = setFold (lam acc: (LRParseTable, Map (Set LRStateItem) Int, Set {lookahead: [TokenRepr], toIdx: Int}, Set {nt: Name, toIdx: Int}). lam item: LRStateItem.
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
            let possibleLookaheads = cfgComposeFirst k firstK (concat postStackTerms (map (lam t2. Terminal t2) item.lookahead)) in
            let stateShifts = setFold (lam acc. lam lh. setInsert {lookahead = lh, toIdx = jIdx} acc) stateShifts possibleLookaheads in
            (table, stateIdxLookup, stateShifts, stateGotos)
          case NonTerminal n then
            -- This is a Goto action
            let stateGotos = setInsert {nt = n, toIdx = jIdx} stateGotos in
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
      let stateReductions = setFold (lam redAcc: [{lookahead: [TokenRepr], prodIdx: Int}]. lam item: LRStateItem.
        if eqi item.stackPointer (length item.terms) then
          snoc redAcc {lookahead = item.lookahead, prodIdx = item.prodIdx}
        else
          redAcc
      ) [] state in
      {tableAcc with reductions = mapInsert stateIdx stateReductions tableAcc.reductions}
    ) table table.states in

    -- Check for conflicts
    let conflicts = foldli (lam acc. lam stateIdx. lam.
      match (mapLookup stateIdx table.shifts, mapLookup stateIdx table.reductions) with (Some shifts, Some reductions) then
        foldli (lam acc. lam reduceIdx. lam r1: {lookahead: [TokenRepr], prodIdx: Int}.
          -- reduce-reduce check
          let acc = foldl (lam acc. lam r2: {lookahead: [TokenRepr], prodIdx: Int}.
            if and (eqSeq tokReprEq r1.lookahead r2.lookahead) (neqi r1.prodIdx r2.prodIdx) then
              snoc acc (join [
                "reduce-reduce conflict in state ", int2string stateIdx, " on lookahead ",
                "[", strJoin ", " (map tokReprToStr r1.lookahead), "] (reduce by rule ",
                int2string r1.prodIdx, " and ", int2string r2.prodIdx, ")"
              ])
            else
              acc
          ) acc (subsequence reductions (addi reduceIdx 1) (length reductions)) in
          -- shift-reduce check
          foldl (lam acc. lam sh: {lookahead: [TokenRepr], toIdx: Int}.
            if eqSeq tokReprEq r1.lookahead sh.lookahead then
              snoc acc (join [
                "shift-reduce conflict in state ", int2string stateIdx, " on lookahead ",
                "[", strJoin ", " (map tokReprToStr r1.lookahead), "] (reduce by rule ",
                int2string r1.prodIdx, " and shift into state ", int2string sh.toIdx, ")"
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
      result.ok table
    else
      result.err (strJoin "\n" (cons "Found following conflicts:" (map (concat " - ") conflicts)))


  -- Creates a multi-line representation of the LR parse table, with each line
  -- indented by the specified amount of whitespaces.
  sem lrtable2string : Int -> LRParseTable -> String
  sem lrtable2string indent =
  | lrtable ->
    let lines = [] in

    let lines = snoc lines (concat (make indent ' ') "Productions:") in
    let ruleIndent = addi (addi indent 2) (length (int2string (length lrtable.syntaxDef.productions))) in
    let lines = foldli (lam lines. lam prodIdx. lam prod: Production.
      let rulenum = int2string prodIdx in
      snoc lines (join [
        make (subi ruleIndent (length rulenum)) ' ', rulenum, ": ",
        nameGetStr prod.nt, " -> ",
        strJoin " " (map cfgTerm2string prod.terms)
      ])
    ) lines lrtable.syntaxDef.productions in

    let lines = snoc lines (concat (make indent ' ') "States:") in
    let lines = foldli (lam lines. lam stateIdx. lam state: Set LRStateItem.
      let lines = snoc lines (join [make (addi indent 2) ' ', "State ", int2string stateIdx, ":"]) in
      let stateStrs = setFold (lam acc: [(String, String)]. lam item: LRStateItem.
        let prefix = [make (addi indent 4) ' ', nameGetStr item.nt, " ->"] in
        let prefix = foldli (lam pfxacc. lam termIdx: Int. lam term: Term.
          if eqi item.stackPointer termIdx then
            concat pfxacc [" [STACK]", " ", cfgTerm2string term]
          else
            concat pfxacc [" ", cfgTerm2string term]
        ) prefix item.terms in
        let prefix = if eqi item.stackPointer (length item.terms) then snoc prefix " [STACK]" else prefix in
        let suffix = join [
          " | (production ", int2string item.prodIdx, ")",
          " | (lookahead [", strJoin ", " (map tokReprToStr item.lookahead), "])"
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
    let lines = mapFoldWithKey (lam lines. lam stateIdx: Int. lam stateShifts: [{lookahead: [TokenRepr], toIdx: Int}].
      foldl (lam lines. lam shift: {lookahead: [TokenRepr], toIdx: Int}.
        snoc lines (join [make (addi indent 2) ' ', int2string stateIdx, " --[", strJoin "," (map tokReprToStr shift.lookahead), "]--> ", int2string shift.toIdx])
      ) lines stateShifts
    ) lines lrtable.shifts in

    let lines = snoc lines (concat (make indent ' ') "Gotos:") in
    let lines = mapFoldWithKey (lam lines. lam stateIdx: Int. lam stateGotos: [{nt: Name, toIdx: Int}].
      foldl (lam lines. lam goto: {nt: Name, toIdx: Int}.
        snoc lines (join [make (addi indent 2) ' ', int2string stateIdx, " --(", nameGetStr goto.nt, ")--> ", int2string goto.toIdx])
      ) lines stateGotos
    ) lines lrtable.gotos in

    let lines = snoc lines (concat (make indent ' ') "Reductions:") in
    let lines = mapFoldWithKey (lam lines. lam stateIdx: Int. lam stateReductions: [{lookahead: [TokenRepr], prodIdx: Int}].
      foldl (lam lines. lam red: {lookahead: [TokenRepr], prodIdx: Int}.
        snoc lines (join [
          make (addi indent 2) ' ',
          "in state ", int2string stateIdx,
          ", reduce by production ", int2string red.prodIdx,
          " on lookahead [", strJoin ", " (map tokReprToStr red.lookahead), "]"
        ])
      ) lines stateReductions
    ) lines lrtable.reductions in

    strJoin "\n" lines


  -- Generates an expression for a LR(k) parser that begins parsing as soon as
  -- it is evaluated. It is by default not wrapped in any lambdas and will be
  -- immediately evaluated unless the caller wraps the returned expression in a
  -- lambda. As such, the type of the generated expressions will not be an
  -- arrow type and will instead directly be:
  --   Result (Info, String) (Info, String) <entrypointType>
  --
  -- Example usage:
  --
  --    let table = lrCreateParseTable ... in
  --    -- Generate and bind important names to be used inside the parser
  --    -- expression. In this case we want to bind the lambda argument
  --    match (nameSym "nextToken", nameSym "stream") with (nNextToken, nStream) in
  --    let bindings = {lrDefaultGeneratorBindings () with
  --      v_stream = nvar_ nStream,
  --      v_nextToken = nvar_ nNextToken
  --    } in
  --    let parserExpr = nulams_ [nStream, nNextToken] (
  --      lrGenerateParser bindings table
  --    ) in
  --    ...
  --
  -- See the LRGeneratorBindings type definitons for more bindings that you
  -- potentially have to provide.
  --
  -- The generated LR(k) parser expression will follow the following stucture:
  --
  --    let actionState = <initial action state from parse table> in
  --    let gotoLookup_<NT0> = [...] in
  --    let gotoLookup_<NT1> = [...] in
  --    ...
  --    let initialStacks = {
  --      typeStack0 = toList [],
  --      typeStack1 = toList [],
  --      ...
  --    } in
  --    let initialStateTrace = [<entrypoint state index>] in
  --    -- extract the first k tokens of lookahead
  --    let lookahead_check: Result w e (Stream, [Token]) =
  --      ...
  --    in
  --    switch lookahead_check
  --      case ResultOk {value = (lexerState, lookahead)} then
  --        recursive let parseLoop =
  --          lam stacks.
  --          lam lexerState: Stream.
  --          lam stateTrace: [Int].
  --          lam lookahead: [Token].
  --          match stateTrace with [currentState] ++ _
  --            switch currentState
  --            case 0 then
  --              switch lookahead
  --              -- first all the shift cases
  --              case [TokenX x, ...] & ([_] ++ lookahead) then
  --                let stacks = {stacks with typeStack<X> = cons x stacks.typeStack<X>} in
  --                let stateTrace = cons <shift index> stateTrace in
  --                switch nextToken lexerState
  --                case ResultOk {value = {token = token, stream = stream}} then
  --                  parseLoop stacks stream stateTrace (snoc lookahead token)
  --                case ResultErr {errors = errors} then
  --                  result.err errors
  --                end
  --              -- then the reduce cases
  --              case [TokenA _, ...] then
  --                let stackY = stack.typeStack<Y> in
  --                let stackN = stack.typeStack<N> in
  --                ...
  --                match (head stackY, tail stackY) with (tokenY1, stackY) in
  --                ...
  --                let newProduce = <semantic action> actionState tokenY1 ... in
  --                <if reducing on entrypoint rule>
  --                  result.ok newProduce
  --                <otherwise (majority of cases)>
  --                  let stackN = cons newProduce stackN in
  --                  let stacks = {stacks with typeStack<Y> = stackY, typeStack<N> = stackN, ...} in
  --                  let stateTrace = subsequence stateTrace <n popped tokens> (length stateTrace) in
  --                  let nextState = get (head stateTrace) gotoLookup_<reduced NT> in
  --                  let stateTrace = cons nextState stateTrace in
  --                  parseLoop stacks lexerState stateTrace lookahead
  --              ...
  --              case _ then
  --                result.err "unexpected tokens"
  --            case _ then
  --              result.err "internal invalid state error"
  --          else
  --            result.err "internal state trace error"
  --        in
  --        parseLoop initialStacks
  --                  lexerState
  --                  initialStateTrace
  --                  lookahead
  --      case ResultErr {errors = errors} then
  --        result.err errors
  --    end
  type LRGeneratorBindings = {
    -- t_ := type names
    t_Result : Name,
    t_Info : Name,
    t_Token : Name,
    t_Stream : Name,
    -- c_ := constructor names
    c_NoInfo : Name,
    c_ResultOk : Name,
    c_ResultErr : Name,
    -- v_ := values and functions (see expected type signature in comments)
    v_result_ok : Expr,  -- all e,w,c. c -> Result e w c
    v_result_err : Expr, -- all e,w,c. e -> Result e w c
    v_nextToken : Expr,  -- Stream -> Result (Info, String) (Info, String) {token: Token, stream: Stream, ...}
    v_stream : Expr,     -- Stream
    v_mergeInfo : Expr,  -- Info -> Info -> Info
    v_tokInfo : Expr,    -- Token -> Info
    v_strJoin : Expr,    -- String -> [String] -> String
    v_tokToStr : Expr,   -- Token -> String
    v_join : Expr,       -- all a. [[a]] -> [a]
    v_int2string : Expr  -- Int -> String
  }
  sem lrDefaultGeneratorBindings : () -> LRGeneratorBindings
  sem lrDefaultGeneratorBindings = | _ -> {
    t_Result = nameNoSym "Result",
    t_Info = nameNoSym "Info",
    t_Token = nameNoSym "Token",
    t_Stream = nameNoSym "Stream",
    c_NoInfo = nameNoSym "NoInfo",
    c_ResultOk = nameNoSym "ResultOk",
    c_ResultErr = nameNoSym "ResultErr",
    v_result_ok = recordproj_ "ok" (var_ "result"),
    v_result_err = recordproj_ "err" (var_ "result"),
    v_nextToken = var_ "nextToken",
    v_stream = var_ "stream",
    v_mergeInfo = var_ "mergeInfo",
    v_tokInfo = var_ "tokInfo",
    v_strJoin = var_ "strJoin",
    v_tokToStr = var_ "tokToStr",
    v_join = var_ "join",
    v_int2string = var_ "int2string"
  }
  sem lrGenerateParser: LRGeneratorBindings -> LRParseTable -> Expr
  sem lrGenerateParser binds =
  | table ->
    /---- Assumed to exist "public" identifiers ----/
    let #var"global: result.err" = lam v. appf1_ binds.v_result_err v in
    let #var"global: result.ok" = lam v. appf1_ binds.v_result_ok v in
    let resExprErr = lam i: Expr. lam e: Expr.  #var"global: result.err" (utuple_ [i, e]) in
    let resErr = lam i. lam s. resExprErr (str_ s) i in
    let resExprErrNoInfo = lam e: Expr. resExprErr (nconapp_ binds.c_NoInfo unit_) e in
    let resErrNoInfo = lam s: String. resExprErrNoInfo (str_ s) in

    /---- Set up the types ----/
    let errorType = tytuple_ [ntycon_ binds.t_Info, tystr_] in
    let warningType = errorType in
    let tokenType = ntycon_ binds.t_Token in
    let lexerStreamType = ntycon_ binds.t_Stream in

    let entrypointType = mapLookupOrElse (lam. tyunknown_) table.syntaxDef.entrypoint table.nonTerminalTypes in
    let resultType = tyapps_ (ntycon_ binds.t_Result) [warningType, errorType, entrypointType] in

    /---- Set up names for initialized values ----/
    let varActionState = nameSym "actionState" in
    let varInitialStacks = nameSym "initialStacks" in
    let varInitialStateTrace = nameSym "initialStateTrace" in

    /---- Set up the stacks ----/
    -- Map types to stack labels
    let cmpType = lam l. lam r. cmpTypeH (l, r) in
    let stackTypeLabel: Map Type String = mapEmpty cmpType in
    -- Check non-terminal types
    let stackTypeLabel = mapFoldWithKey (lam stlAcc: Map Type String. lam. lam ty: Type.
      match mapLookup ty stlAcc with None () then
        let label = join ["typeStack", int2string (mapLength stlAcc)] in
        mapInsert ty label stlAcc
      else
        stlAcc
    ) stackTypeLabel table.nonTerminalTypes in
    -- Check token types
    let stackTypeLabel = mapFoldWithKey (lam stlAcc: Map Type String. lam. lam c: {conIdent: Name, conArg: Type}.
      match mapLookup c.conArg stlAcc with None () then
        let label = join ["typeStack", int2string (mapLength stlAcc)] in
        mapInsert c.conArg label stlAcc
      else
        stlAcc
    ) stackTypeLabel table.tokenConTypes in

    let stackRecordExpr = 
      let tytms = (mapFoldWithKey (lam acc: ([(String, Type)], [(String, Expr)]). lam ty: Type. lam label: String.
        match acc with (tys, tms) in
        let tys = cons (label, (tyseq_ ty)) tys in
        -- TODO(johnwikman, 2023-08-31): The previous usage of "toList" below
        -- has been replaced by the usage of createList_, but it makes use of a
        -- function that selects from a list with no type. Usage of an
        -- intrinsic emptyList and emptyRope or something would be better
        -- suited here, as I know the type of the list but cannot instantiate
        -- any elements from that type.
        --let tms = cons (label, withType (tyseq_ ty) (appf1_ (var_ "toList") (seq_ []))) tms in
        let tms = cons (label, withType (tyseq_ ty) (createList_ (int_ 0) (ulam_ "i" (get_ (seq_ []) (var_ "i"))))) tms in
        (tys, tms)
      ) ([], []) stackTypeLabel) in
      match tytms with (tys, tms) in
      record_ (tyrecord_ tys) tms
    in

    /---- Set up the GOTO lists ----/
    let missingGOTO = 200000 in -- using a large number here since MCore cannot parse negative numbers yet

    let gotoLookup: Map Name (Map Int Int) = mapFoldWithKey (lam acc. lam nt. lam.
      mapInsert nt (mapEmpty subi) acc
    ) (mapEmpty nameCmp) table.nonTerminalTypes in
    let gotoLookup = mapFoldWithKey (lam acc. lam fromIdx. lam stateGotos: [{nt: Name, toIdx: Int}].
      foldl (lam acc. lam stateGoto: {nt: Name, toIdx: Int}.
        mapInsert stateGoto.nt
                  (mapInsert fromIdx stateGoto.toIdx
                             (mapLookupOrElse (lam. error "PANIC. Internal parser generator logic error")
                                              stateGoto.nt acc))
                  acc
      ) acc stateGotos
    ) gotoLookup table.gotos in

    let gotoLookupVarExpressions: Map Name Expr = mapFoldWithKey (lam acc. lam nt: Name. lam gotos: Map Int Int.
      let nameGotos = createRope (length table.states) (lam i. int_ (mapLookupOrElse (lam. missingGOTO) i gotos)) in
      mapInsert nt (seq_ nameGotos) acc
    ) (mapEmpty nameCmp) gotoLookup in
    let gotoLookupVarNames: Map Name Name = mapFoldWithKey (lam acc: Map Name Name. lam nt: Name. lam.
      let lookupName = nameSym (join ["gotoLookup", int2string (mapLength acc), "_", nameGetStr nt]) in
      mapInsert nt lookupName acc
    ) (mapEmpty nameCmp) gotoLookupVarExpressions in

    /---- Set up the tail-recursive parsing function ----/
    let parseFunctionIdent = nameSym "parseLoop" in
    let parseFunctionBody =
      nreclets_ [(parseFunctionIdent, tyunknown_,
        let lamStacks = nameSym "stacks" in
        let lamLexerState = nameSym "lexerState" in
        let lamStateTrace = nameSym "stateTrace" in
        let lamLookahead = nameSym "lookahead" in
        nlams_ [(lamStacks, tyunknown_),
                (lamLexerState, lexerStreamType),
                (lamStateTrace, tyseq_ tyint_),
                (lamLookahead, tyseq_ tokenType)] (
          -- Recursive function body here:

          -- match stateTrace with [currentState] ++ _
          let varCurrentState = nameSym "currentState" in
          match_ (nvar_ lamStateTrace)
                 (pseqedgew_ [npvar_ varCurrentState] []) (
            -- then
            -- switch currentState
            let stateMatches = mapi (lam i: Int. lam.
              -- case <i> then
              matchex_ (nvar_ varCurrentState) (pint_ i) (
                let stateShifts: [{lookahead: [TokenRepr], toIdx: Int}] = mapLookupOrElse (lam. []) i table.shifts in
                let stateReductions: [{lookahead: [TokenRepr], prodIdx: Int}] = mapLookupOrElse (lam. []) i table.reductions in

                let shiftMatches = map (lam shift: {lookahead: [TokenRepr], toIdx: Int}.
                  let lhCons: [{conIdent: Name, conArg: Type}] = map (lam repr. mapLookupOrElse (lam. error "malformed parse table! (1)") repr table.tokenConTypes) shift.lookahead in
                  -- We only need value for the first lookahead token when shifting
                  let v = nameSym "shiftValue" in
                  let h = head lhCons in
                  let hCon = npcon_ h.conIdent (npvar_ v) in
                  let restCons = map (lam lh. npcon_ lh.conIdent pvarw_) (tail lhCons) in
                  let matchCons = cons hCon restCons in
                  -- Name for the "tail", to avoid naming conflict with tail
                  let varRest = nameSym "rest" in
                  matchex_ (nvar_ lamLookahead) (pand_ (pseqtot_ matchCons) (pseqedgen_ [pvarw_] varRest [])) (
                    -- case [TokenX x, TokenY y, ...] & ([_] ++ rest) then
                    --   <if shift>
                    --   let stacks = {stacks with stackX = cons x stacks.stackX} in
                    --   let stateTrace = cons <shiftIdx> stateStrace in
                    --   let nextTokenResult = nextToken lexerState in
                    --   match nextTokenResult with ResultOk {value = lexres} then
                    --     parseLoop stacks lexres.stream stateTrace (snoc lookahead lexres.token)
                    --   else match nextTokenResult with ResultErr {errors = errors} then
                    --     result.err errors
                    --   else never
                    let stackLabel = mapLookupOrElse (lam. error "internal error (2)") h.conArg stackTypeLabel in
                    bindall_ [
                      ulet_ "shiftStack" (recordproj_ stackLabel (nvar_ lamStacks)),
                      ulet_ "newTypeStack" (cons_ (nvar_ v) (var_ "shiftStack")),
                      ulet_ "newStacks" (recordupdate_ (nvar_ lamStacks) stackLabel (var_ "newTypeStack")),
                      ulet_ "nextTokenResult" (appf1_ (binds.v_nextToken) (nvar_ lamLexerState)),
                      matchall_ [
                        matchex_ (var_ "nextTokenResult") (npcon_ (binds.c_ResultOk) (prec_ [("value", pvar_ "lexres")])) (
                          bindall_ [
                            ulet_ "newLookahead" (snoc_ (nvar_ varRest) (recordproj_ "token" (var_ "lexres"))),
                            ulet_ "newLexerState" (recordproj_ "stream" (var_ "lexres")),
                            ulet_ "newStateTrace" (cons_ (int_ shift.toIdx) (nvar_ lamStateTrace)),
                            appf4_ (nvar_ parseFunctionIdent)
                                   (var_ "newStacks")
                                   (var_ "newLexerState")
                                   (var_ "newStateTrace")
                                   (var_ "newLookahead")
                          ]
                        ),
                        matchex_ (var_ "nextTokenResult") (npcon_ (binds.c_ResultErr) (prec_ [("errors", pvar_ "errors"), ("warnings", pvar_ "warnings")])) (
                          nconapp_ (binds.c_ResultErr) (urecord_ [("errors", var_ "errors"), ("warnings", var_ "warnings")])
                        )
                      ]
                    ]
                  )
                ) stateShifts in

                let reductionMatches = map (lam reduction: {lookahead: [TokenRepr], prodIdx: Int}.
                  let lhCons: [{conIdent: Name, conArg: Type}] = map (lam repr. mapLookupOrElse (lam. error "malformed parse table! (2)") repr table.tokenConTypes) reduction.lookahead in
                  let rule = get table.syntaxDef.productions reduction.prodIdx in
                  let termTypes = map (lam term: Term.
                    switch term
                    case Terminal repr then
                      let contype = mapLookupOrElse (lam. error "malformed parse table! (3)") repr table.tokenConTypes in
                      contype.conArg
                    case NonTerminal name then
                      mapLookupOrElse (lam. error "malformed parse table! (4)") name table.nonTerminalTypes
                    end
                  ) rule.terms in
                  -- We don't need any value information here, so all variables can be wildcards
                  let matchCons = map (lam lh. npcon_ lh.conIdent pvarw_) lhCons in
                  matchex_ (nvar_ lamLookahead) (pseqtot_ matchCons) (
                    -- case [TokenX _, TokenY _, ...] then
                    --   <if reduce>
                    --   let stackA = stacks.stackA in -- extract the relevant stacks for this reduce
                    --   let stackB = stacks.stackB in
                    --   let stackC = stacks.stackC in
                    --   let tokenA2 = head stackA in
                    --   let stackA = tail stackA in
                    --   let tokenB1 = head stackB in
                    --   let stackB = tail stackB in
                    --   let tokenA1 = head stackA in
                    --   let stackA = tail stackA in
                    --   let newProduce = semanticAction actionState tokenA1 tokenB1 tokenA2 in
                    --   <if reduce by entrypoint rule>
                    --     result.ok newProduce
                    --   <otherwise (pretty much always)>
                    --     let stackC = cons newProduce stackC in
                    --     let stacks = {stacks with stackA = stackA, stackB = stackB, stackC = stackC} in
                    --     let stateTrace = subsequence stateTrace 3 (length stateTrace) in
                    --     let currentState = head stateTrace in
                    --     let nextState = get currentState gotoLookup_<nt_idx>_<nt> in
                    --     let stateTrace = cons nextState stateTrace in
                    --     parseLoop stacks lexerState stateTrace lookahead
                    let stackLabels = map (lam ty. mapLookupOrElse (lam. error "internal error (3)") ty stackTypeLabel) termTypes in
                    let stackVars = map (lam lbl. (var_ (concat "var" lbl), lbl)) (distinct eqString stackLabels) in

                    let actionRetType =
                      recursive let work = lam ty. match ty with TyArrow t then work t.to else ty in
                      work (tyTm rule.action)
                    in
                    let returnLabel = mapLookupOrElse (lam. error "internal error (4)") actionRetType stackTypeLabel in
                    bindall_ [

                      -- extract all stacks to variables
                      bindall_ (map (lam lbl: String.
                        ulet_ (concat "var" lbl) (recordproj_ lbl (nvar_ lamStacks))
                      ) (distinct eqString (cons returnLabel stackLabels))),

                      -- extract all values from the stacks and pop that value from the stack
                      -- and create the new production
                      bindall_ (snoc
                        -- Stack semantics, so we pop in reverse order
                        (reverse (mapi (lam i. lam lbl.
                        bindall_ [
                          ulet_ (join ["tokenValue", int2string i]) (head_ (var_ (concat "var" lbl))),
                          ulet_ (concat "var" lbl) (tail_ (var_ (concat "var" lbl)))
                        ]
                        ) stackLabels))
                        (ulet_ "newProduce" (appSeq_ rule.action (cons (nvar_ varActionState) (mapi (lam i. lam. var_ (join ["tokenValue", int2string i])) stackLabels))))
                      ),

                      -- If we reduce on the entrypoint rule, then we return. Otherwise push to the stack and run the GOTO action
                      if eqi reduction.prodIdx table.entrypointProdIdx then (
                        #var"global: result.ok" (var_ "newProduce")
                      ) else (bindall_ [
                        ulet_ (concat "var" returnLabel) (cons_ (var_ "newProduce") (var_ (concat "var" returnLabel))),
                        -- Update the stack state
                        ulet_ "newStacks" (foldl (lam rec. lam lbl.
                          recordupdate_ rec lbl (var_ (concat "var" lbl))
                        ) (nvar_ lamStacks) (distinct eqString (cons returnLabel stackLabels))),
                        ulet_ "newStateTrace" (subsequence_ (nvar_ lamStateTrace) (int_ (length stackLabels)) (length_ (nvar_ lamStateTrace))),
                        ulet_ "currentState" (head_ (var_ "newStateTrace")),

                        let varLookupName = mapLookupOrElse (lam. error "malformed parse table! (5)") rule.nt gotoLookupVarNames in
                        ulet_ "nextState" (get_ (nvar_ varLookupName) (var_ "currentState")),
                        ulet_ "newStateTrace" (cons_ (var_ "nextState") (var_ "newStateTrace")),

                        appf4_ (nvar_ parseFunctionIdent)
                               (var_ "newStacks")
                               (nvar_ lamLexerState)
                               (var_ "newStateTrace")
                               (nvar_ lamLookahead)
                      ])
                    ]
                  )
                ) stateReductions in

                -- Error messages in the case of invalid lookahead
                let allLookaheads: [[TokenRepr]] =
                  concat (map (lam x. x.lookahead) stateShifts)
                         (map (lam x. x.lookahead) stateReductions)
                in
                let allLookaheadStrings: [String] = map (lam lh: [TokenRepr].
                  let t: [String] = map tokReprToStr lh in
                  if eqi 1 (length t) then
                    head t
                  else
                    join [head t, " followed by ", strJoin ", " (tail t)]
                ) allLookaheads in
                let lookaheadFailCase =
                  resExprErr (appf2_ (binds.v_mergeInfo)
                                     (appf1_ (binds.v_tokInfo) (head_ (nvar_ lamLookahead)))
                                     (appf1_ (binds.v_tokInfo) (head_ (reverse_ (nvar_ lamLookahead)))))
                             (appf1_ (binds.v_join) (seq_ [
                    str_ (join [
                      "Unexpected ",
                      if eqi 1 table.k_lookahead then "token" else "tokens"
                    ]),
                    str_ " ",
                    appf2_ (binds.v_strJoin) (str_ ", ")
                           (map_ (binds.v_tokToStr) (nvar_ lamLookahead)),
                    str_ ". Expected ",
                    str_ (
                      if eqi 1 (length allLookaheads) then
                        head allLookaheadStrings
                      else
                        strJoin "\n - " (cons "one of" allLookaheadStrings)
                    )
                  ]))
                in

                matchall_ (join [shiftMatches, reductionMatches, [lookaheadFailCase]])
              )
            ) table.states in

            let stateShiftFailCase = resExprErrNoInfo (appf1_ (binds.v_join) (seq_ [
              str_ "Internal error: Unrecognized state: ",
              appf1_ (binds.v_int2string) (nvar_ varCurrentState)
            ])) in

            /- Uncomment this to print state and lookahead
            -- TODO(johnwikman, 2023-01-22): This should probably be some kind of option instead
            bind_ (
              ulet_ "TEMP" (
                appf1_ (var_ "printLn") (appf1_ (var_ "join") (seq_ [
                  str_ "currentState: ",
                  appf1_ (var_ "int2string") (nvar_ varCurrentState),
                  str_ "\nlookahead: [",
                  appf2_ (var_ "strJoin") (str_ ", ") (map_ (var_ "tokToStr") (nvar_ lamLookahead)),
                  str_ "]"
                ]))
              )
            ) -- -/
            (matchall_ (snoc stateMatches stateShiftFailCase)) -- the "real" code

          ) (
            -- else
            resErrNoInfo "Internal error: Empty state-trace before parsing is finished."
          )
        )
      )]
    in

    /---- Set up the expression ----/
    let expr = bindall_ [
      -- Set up the goto lookups and the initial action state
      bindall_ (snoc (map (lam nt: Name.
          let expr = mapLookupOrElse (lam. error "lrk PANIC") nt gotoLookupVarExpressions in
          let binding = mapLookupOrElse (lam. error "lrk PANIC") nt gotoLookupVarNames in
          nulet_ binding expr
        ) (mapKeys gotoLookupVarNames))
        (nulet_ varActionState table.syntaxDef.initActionState)
      ),

      -- Initialize the stacks as lists
      nlet_ varInitialStacks (tyTm stackRecordExpr) stackRecordExpr,

      -- Initialize the state trace
      nulet_ varInitialStateTrace (seq_ [int_ table.entrypointIdx]),

      /- Initialize the lookahead as
      let lookahead_check: Result w e (LexerStateType, [Tokens]) =
        recursive let work = lam lexerState. lam acc. lam i.
          if eqi i 0 then acc else
          let r = nextToken lexerState in
          match r with ResultOk {value = rexres} then
            work lexres.stream (snoc acc lexres.token) (subi i 1)
          else match r with ResultErr {errors = errors} in
            result.err errors
        in
        work lexerState [] k
      in
      -/
      ulet_ "lookahead_check" (
        bindall_ [
          ureclet_ "work" (lams_ [("lhLexerState", tyunknown_),
                                  ("lhAcc", tyseq_ tokenType),
                                  ("i", tyint_)] (
            if_ (eqi_ (var_ "i") (int_ 0)) (
              #var"global: result.ok" (utuple_ [var_ "lhLexerState", var_ "lhAcc"])
            ) (bindall_ [
              ulet_ "r" (appf1_ binds.v_nextToken (var_ "lhLexerState")),
              matchall_ [
                matchex_ (var_ "r") (npcon_ binds.c_ResultOk (prec_ [("value", pvar_ "lexres")])) (
                  bindall_ [
                    ulet_ "newLhAcc" (snoc_ (var_ "lhAcc") (recordproj_ "token" (var_ "lexres"))),
                    ulet_ "newLhLexerState" (recordproj_ "stream" (var_ "lexres")),
                    appf3_ (var_ "work")
                           (var_ "newLhLexerState")
                           (var_ "newLhAcc")
                           (subi_ (var_ "i") (int_ 1))
                  ]
                ),
                matchex_ (var_ "r") (npcon_ binds.c_ResultErr (prec_ [("errors", pvar_ "errors"), ("warnings", pvar_ "warnings")])) (
                  nconapp_ binds.c_ResultErr (urecord_ [("errors", var_ "errors"), ("warnings", var_ "warnings")])
                )
              ]
            ])
          )),
          appf3_ (var_ "work")
                 (binds.v_stream)
                 (seq_ [])
                 (int_ table.k_lookahead)
        ]
      ),

      /- Extract the lookahead and run the parser:
      match lookahead_check with ResultOk {value = (lexerState, lookahead)} then
        <parser body>
        runparser
      else match lookahead_check with ResultErr {errors = errors} in
        result.err errors
      -/
      matchall_ [
        matchex_ (var_ "lookahead_check") (npcon_ binds.c_ResultOk (prec_ [("value", (ptuple_ [pvar_ "lhLexerState", pvar_ "lhLookahead"]))])) (
          bindall_ [
            parseFunctionBody,
            appf4_ (nvar_ parseFunctionIdent) (nvar_ varInitialStacks)
                                              (var_ "lhLexerState")
                                              (nvar_ varInitialStateTrace)
                                              (var_ "lhLookahead")
          ]
        ),
        matchex_ (var_ "lookahead_check") (npcon_ binds.c_ResultErr (prec_ [("errors", pvar_ "errors"), ("warnings", pvar_ "warnings")])) (
          nconapp_ binds.c_ResultErr (urecord_ [("errors", var_ "errors"), ("warnings", var_ "warnings")])
        )
      ]
    ] in
    withType resultType expr
end



lang LRParserTest = LRParser
  -- Lexer fragments
  + LIdentTokenParser
  + UIntTokenParser
  + BracketTokenParser
  + CommaTokenParser
  + SemiTokenParser

  -- Compilation fragments for testing the generated parser
  + MCoreCompileLang
  + BootParser
  + MExprPrettyPrint
  + MExprLowerNestedPatterns
  + MExprTypeCheck
  + MExprSym
end


mexpr
use LRParserTest in

let t_EOF = Terminal (EOFRepr {}) in
let t_LIdent = Terminal (LIdentRepr {}) in
let t_Int = Terminal (IntRepr {}) in
let t_LParen = Terminal (LParenRepr {}) in
let t_RParen = Terminal (RParenRepr {}) in
let t_Comma = Terminal (CommaRepr {}) in
let t_Semi = Terminal (SemiRepr {}) in

let tokEmptyTy = tyrecord_ [("info", tycon_ "Info")] in
let tokStrvalTy = tyrecord_ [("info", tycon_ "Info"), ("val", tystr_)] in
let tokIntvalTy = tyrecord_ [("info", tycon_ "Info"), ("val", tyint_)] in

let allTokenConTypes = mapFromSeq tokReprCmp [
  (EOFRepr {}, {conIdent = nameNoSym "EOFTok", conArg = tokEmptyTy}),
  (LIdentRepr {}, {conIdent = nameNoSym "LIdentTok", conArg = tokStrvalTy}),
  (IntRepr {}, {conIdent = nameNoSym "IntTok", conArg = tokIntvalTy}),
  (LParenRepr {}, {conIdent = nameNoSym "LParenTok", conArg = tokEmptyTy}),
  (RParenRepr {}, {conIdent = nameNoSym "RParenTok", conArg = tokEmptyTy}),
  (CommaRepr {}, {conIdent = nameNoSym "CommaTok", conArg = tokEmptyTy}),
  (SemiRepr {}, {conIdent = nameNoSym "SemiTok", conArg = tokEmptyTy})
] in

type LRParseTest in
con LRPTSucceed: {input: String, expectedOutput: String} -> LRParseTest in
con LRPTFail: {input: String} -> LRParseTest in

let lrptInput = lam parseTest. switch parseTest
  case LRPTSucceed t then t.input
  case LRPTFail t then t.input
end in

type LRTestCase = {
  tokenConTypes: Map TokenRepr {conIdent: Name, conArg: Type},
  name: String,
  syntaxDef: SyntaxDef,
  isLR1: Bool,
  parseTests: [LRParseTest]
} in


let testcases: [LRTestCase] = [
  -- LR1 example from the book by Appel (using slightly different non-terminal tokens)
  let _S = nameSym "S" in
  let _E = nameSym "E" in
  let _V = nameSym "V" in
  let nt_S = NonTerminal _S in
  let nt_E = NonTerminal _E in
  let nt_V = NonTerminal _V in
  {
    tokenConTypes = allTokenConTypes,
    name = "LR1 Example (from Tiger Book)",
    syntaxDef = {
      entrypoint = _S,
      productions = [
        {nt = _S, terms = [nt_V, t_Semi, nt_E],
         action = withType (tyarrows_ [tyunknown_, tystr_, tokEmptyTy, tystr_, tystr_])
                           (ulams_ ["actionState", "a1_V", "a2_Semi", "a3_S"]
                                   (appf1_ (var_ "join")
                                           (seq_ [var_ "a1_V", str_ " = ", var_ "a3_S"])))},
        {nt = _S, terms = [nt_E],
         action = withType (tyarrows_ [tyunknown_, tystr_, tystr_])
                           (ulams_ ["actionState", "a1_E"]
                                   (var_ "a1_E"))},
        {nt = _E, terms = [nt_V],
         action = withType (tyarrows_ [tyunknown_, tystr_, tystr_])
                           (ulams_ ["actionState", "a1_V"]
                                   (var_ "a1_V"))},
        {nt = _V, terms = [t_LIdent],
         action = withType (tyarrows_ [tyunknown_, tokStrvalTy, tystr_])
                           (ulams_ ["actionState", "a1_LIdent"]
                                   (recordproj_ "val" (var_ "a1_LIdent")))},
        {nt = _V, terms = [t_Comma, nt_E],
         action = withType (tyarrows_ [tyunknown_, tokEmptyTy, tystr_, tystr_])
                           (ulams_ ["actionState", "a1_Comma", "a2_E"]
                                   (cons_ (char_ '*') (var_ "a2_E")))}
      ],
      initActionState = unit_
    },
    isLR1 = true,
    parseTests = [
      LRPTSucceed {
        input = ",x;z",
        expectedOutput = "*x = z"},
      LRPTSucceed {
        input = "abc",
        expectedOutput = "abc"},
      LRPTSucceed {
        input = " , abc",
        expectedOutput = "*abc"},
      LRPTSucceed {
        input = "x ; , ,,   y  \n",
        expectedOutput = "x = ***y"},
      LRPTFail {input = ""},
      LRPTFail {input = " , "},
      LRPTFail {input = " ????????? "}
    ]
  },
  -- LR2 example from https://stackoverflow.com/questions/62075086/what-is-an-lr2-parser-how-does-it-differ-from-an-lr1-parser
  let _S = nameSym "S" in
  let _R = nameSym "R" in
  let _T = nameSym "T" in
  let nt_S = NonTerminal _S in
  let nt_R = NonTerminal _R in
  let nt_T = NonTerminal _T in
  {
    tokenConTypes = allTokenConTypes,
    name = "LR2 Example",
    syntaxDef = {
      entrypoint = _S,
      productions = [
        {nt = _S, terms = [nt_R, nt_S],
         action = withType (tyarrows_ [tyunknown_, tystr_, tystr_, tystr_])
                           (ulams_ ["actionState", "a1_R", "a2_S"]
                                   (appf1_ (var_ "join") (seq_ [
                                      var_ "a1_R",
                                      str_ " | ",
                                      var_ "a2_S"
                                    ])))},
        {nt = _S, terms = [nt_R],
         action = withType (tyarrows_ [tyunknown_, tystr_, tystr_])
                           (ulams_ ["actionState", "a1_R"]
                                   (var_ "a1_R"))},
        {nt = _R, terms = [t_LIdent, t_Semi, nt_T],
         action = withType (tyarrows_ [tyunknown_, tokStrvalTy, tokEmptyTy, tyseq_ tystr_, tystr_])
                           (ulams_ ["actionState", "a1_LIdent", "a2_Semi", "a3_T"]
                                   (appf1_ (var_ "join") (seq_ [
                                      recordproj_ "val" (var_ "a1_LIdent"),
                                      str_ "[",
                                      appf2_ (var_ "strJoin") (str_ ", ") (var_ "a3_T"),
                                      str_ "]"
                                    ])))},
        {nt = _T, terms = [t_LIdent, nt_T],
         action = withType (tyarrows_ [tyunknown_, tokStrvalTy, tyseq_ tystr_, tyseq_ tystr_])
                           (ulams_ ["actionState", "a1_LIdent", "a2_T"]
                                   (cons_ (recordproj_ "val" (var_ "a1_LIdent")) (var_ "a2_T")))},
        {nt = _T, terms = [t_Int],
         action = withType (tyarrows_ [tyunknown_, tokIntvalTy, tyseq_ tystr_])
                           (ulams_ ["actionState", "a1_Int"]
                                   (seq_ [appf1_ (var_ "int2string")
                                                 (recordproj_ "val" (var_ "a1_Int"))]))},
        {nt = _T, terms = [],
         action = withType (tyarrows_ [tyunknown_, tyseq_ tystr_])
                           (ulams_ ["actionState"]
                                   (seq_ []))}
      ],
      initActionState = unit_
    },
    isLR1 = false,
    parseTests = [
      LRPTSucceed {
        input = "foo;",
        expectedOutput = "foo[]"},
      LRPTSucceed {
        input = "foo; a 5 bar; babar",
        expectedOutput = "foo[a, 5] | bar[babar]"},
      LRPTSucceed {
        input = "foo; a 5 bar; babar    ;",
        expectedOutput = "foo[a, 5] | bar[] | babar[]"},
      LRPTFail {input = ""},
      LRPTFail {input = "5;"}
    ]
  },
  -- non-LL language (more left parentheses than right parentheses)
  let _LeftOnly = nameSym "LeftOnly" in
  let _LeftRight = nameSym "LeftRight" in
  let nt_LeftOnly = NonTerminal _LeftOnly in
  let nt_LeftRight = NonTerminal _LeftRight in
  {
    tokenConTypes = allTokenConTypes,
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
    isLR1 = true,
    parseTests = [
      LRPTSucceed {
        input = "()",
        expectedOutput = "|(e)"},
      LRPTSucceed {
        input = "( ( (  ) )",
        expectedOutput = "(|((e))"},
      LRPTSucceed {
        input = "(((((((((((()",
        expectedOutput = "(((((((((((|(e)"},
      LRPTSucceed {
        input = "",
        expectedOutput = "|e"},
      LRPTSucceed {
        input = "(((((((((((",
        expectedOutput = "(((((((((((|e"},
      LRPTFail {input = "(((()))))))))))))))))"},
      LRPTFail {input = "(((()]"}
    ]
  }
] in


let suppressPrints = true in
let tprint = lam s. if suppressPrints then () else print s in
let tprintLn = lam s. if suppressPrints then () else printLn s in

-- Run tests
foldl (lam. lam tc: LRTestCase.
  tprintLn (join ["Running testcase ", tc.name, " "]);

  let isLR1_table = match lrCreateParseTable 1 tc.tokenConTypes tc.syntaxDef with ResultOk _ then true else false in
  utest isLR1_table with tc.isLR1 in

  let k = if tc.isLR1 then 1 else 2 in

  switch lrCreateParseTable k tc.tokenConTypes tc.syntaxDef
  case ResultOk {value = lrtable} then
    tprintLn (lrtable2string 2 lrtable);
    tprintLn "";
    let parser = lrGenerateParser (lrDefaultGeneratorBindings ()) lrtable in
    let program: String = strJoin "\n" [
      "include \"error.mc\"",
      "include \"map.mc\"",
      "include \"result.mc\"",
      "include \"seq.mc\"",
      "include \"string.mc\"",
      "include \"mexpr/info.mc\"",
      "include \"parser/lexer.mc\"",
      "mexpr",
      "use Lexer in",
      "let wrappedNextToken = lam s. result.ok (nextToken s) in",
      expr2str (bindall_ [
        -- Wrap the generated expression in lambdas
        let n_stream = nameSym "stream" in
        let n_nextToken = nameSym "nextToken" in
        let bindings = {lrDefaultGeneratorBindings () with
          v_stream = nvar_ n_stream,
          v_nextToken = nvar_ n_nextToken
        } in
        ulet_ "parse" (nlams_ [(n_stream, tycon_ "Stream"), (n_nextToken, tyunknown_)] (
          lrGenerateParser bindings lrtable
        )),

        let_ "lexerState" (tycon_ "Stream")
                          (urecord_ [("pos", appf1_ (var_ "initPos") (str_ "file")),
                                     ("str", get_ (var_ "argv") (int_ 1))]),
        ulet_ "parse_result" (appf2_ (var_ "parse")
                                     (var_ "lexerState")
                                     (var_ "wrappedNextToken")),
        matchall_ [
          matchex_ (var_ "parse_result") (pcon_ "ResultOk" (prec_ [("value", (pvar_ "result"))])) (
            appf1_ (var_ "print") (var_ "result")
          ),
          matchex_ (var_ "parse_result") (pcon_ "ResultErr" (prec_ [("errors", (pvar_ "errors"))])) (
            appf2_ (var_ "errorSingle") (seq_ [])
                   (appf2_ (var_ "strJoin") (str_ "\n")
                           (map_ (ulam_ "v" (tupleproj_ 1 (var_ "v")))
                                 (appf1_ (var_ "mapValues") (var_ "errors"))))
          )
        ]
      ]),
      ""
    ] in

    -- Put the program in a tempfile and compile that
    -- (Can't wait for bootstapping to be done...)
    let tmpFilePath = sysTempFileMake () in
    writeFile tmpFilePath program;

    let ast = parseMCoreFile {{{{{{ defaultBootParserParseMCoreFileArg
      with keepUtests = false }
      with pruneExternalUtests = true }
      with externalsExclude = [] }
      with pruneExternalUtestsWarning = false }
      with eliminateDeadCode = true }
      with keywords = mexprExtendedKeywords } tmpFilePath
    in

    let ast = symbolize ast in
    let ast = typeCheck ast in
    let ast = lowerAll ast in

    -- Compile the program
    let compileOCaml = lam libs. lam clibs. lam ocamlProg.
      let opt = {optimize = true, libraries = libs, cLibraries = clibs} in
      ocamlCompileWithConfig opt ocamlProg
    in
    let cunit: CompileResult = compileMCore ast (mkEmptyHooks compileOCaml) in

    foldl (lam. lam parseTest: LRParseTest.
      let res = cunit.run "" [join ["\"", lrptInput parseTest, "\""]] in
      switch parseTest
      case LRPTSucceed t then
        utest res.stdout with t.expectedOutput in
        utest res.stderr with "" in
        utest res.returncode with 0 in ()
      case LRPTFail _ then
        utest res.stdout with "" using eqString in
        utest res.stderr with "" using neqString in
        utest res.returncode with 0 using neqi in ()
      end
    ) () tc.parseTests;

    cunit.cleanup ();
    sysDeleteFile tmpFilePath;
    tprintLn "";
    ()
  case ResultErr {errors = errors} then
    tprintLn (strJoin "\n" (mapValues errors));
    utest tc.name with "I should not fail!" in ()
  end

) () testcases
