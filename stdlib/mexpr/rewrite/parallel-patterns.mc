include "mexpr/anf.mc"
include "mexpr/patterns.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/tailrecursion.mc"
include "mexpr/rewrite/utils.mc"

include "set.mc"

type VarPattern
con PatternIndex : Int -> VarPattern
con PatternName : Name -> VarPattern

let cmpVarPattern = lam c1 : VarPattern. lam c2 : VarPattern.
  let p : (VarPattern, VarPattern) = (c1, c2) in
  match p with (PatternIndex i1, PatternIndex i2) then
    subi i1 i2
  else match p with (PatternIndex i1, _) then
    1
  else match p with (_, PatternIndex i2) then
    negi 1
  else match p with (PatternName n1, PatternName n2) then
    nameCmp n1 n2
  else never

type Pattern
con FixedAppPattern : {id : Int, fn : Expr, vars : [VarPattern]} -> Pattern
con UnknownAppPattern : {id : Int, vars : [VarPattern]} -> Pattern
con BranchPattern : {id : Int, cond : VarPattern, thn : [Pattern],
                        els : [Pattern]} -> Pattern
con SeqPattern : {id : Int, vars : [VarPattern]} -> Pattern
con RecursionPattern : {id : Int, binds : [(Name, Int)]} -> Pattern
con ReturnPattern : {id : Int, var : VarPattern} -> Pattern

type ParallelPattern = {
  atomicPatternMap : Map Int Pattern,
  activePatterns : [Pattern],
  dependencies : Map Int (Set Int),
  replacement : (Map VarPattern Expr) -> Expr
}

type PatternMatchState = {
  active : [Int],
  dependencies : Map Int (Set Int),
  patternIndexToBoundVar : Map Int Name,
  atomicPatternMatches : Map Int Expr,
  nameMatches : Map Name Name
}

let emptyPatternMatchState = {
  active = [],
  dependencies = mapEmpty subi,
  patternIndexToBoundVar = mapEmpty subi,
  atomicPatternMatches = mapEmpty subi,
  nameMatches = mapEmpty nameCmp
}

let getPatternIndex : Pattern -> Int = lam p.
  match p with FixedAppPattern t then t.id
  else match p with UnknownAppPattern t then t.id
  else match p with BranchPattern t then t.id
  else match p with SeqPattern t then t.id
  else match p with RecursionPattern t then t.id
  else match p with ReturnPattern t then t.id
  else never

let getShallowPatternDependencies : Pattern -> [VarPattern] = lam p.
  match p with FixedAppPattern t then t.vars
  else match p with UnknownAppPattern t then t.vars
  else match p with BranchPattern t then [t.cond]
  else match p with SeqPattern t then t.vars
  else match p with RecursionPattern t then
    match unzip t.binds with (names, indices) then
      join [map (lam n. PatternName n) names,
            map (lam i. PatternIndex i) indices]
    else never
  else match p with ReturnPattern t then [t.var]
  else never

let getInnerPatterns : Pattern -> Option [Pattern] = lam p.
  match p with FixedAppPattern _ then None ()
  else match p with UnknownAppPattern _ then None ()
  else match p with BranchPattern t then Some (concat t.thn t.els)
  else match p with SeqPattern _ then None ()
  else match p with RecursionPattern _ then None ()
  else match p with ReturnPattern _ then None ()
  else never

let isFinalState : PatternMatchState -> Bool = lam state.
  match state with {active = [], dependencies = deps} then
    mapIsEmpty deps
  else false

-- Constructs a mapping from every pattern index to a set containing the
-- indices of patterns on which the pattern depends on. A pattern is considered
-- to depend on a pattern with index i if it contains a PatternIndex i.
--
-- This function is implemented with the assumption that every pattern has been
-- given a unique index. If multiple patterns with the same index are found, an
-- error will be reported.
let getPatternDependencies : [Pattern] -> Map Int (Set Int) =
  lam atomicPatterns.
  recursive let atomicPatternDependencies
    : Map Int (Set Int) -> Pattern -> Map Int (Set Int) =
    lam dependencies. lam p.
    let id = getPatternIndex p in
    match mapLookup id dependencies with None () then
      let patternDeps : Set Int =
        foldl
          (lam patternDeps : Set Int. lam v : VarPattern.
            match v with PatternIndex i then
              setInsert i patternDeps
            else patternDeps)
          (setEmpty subi)
          (getShallowPatternDependencies p) in
      mapInsert id patternDeps dependencies
    else
      error (join ["Found multiple atomic patterns with id ",
                   int2string id])
  in
  let dependencyMap =
    foldl atomicPatternDependencies (mapEmpty subi) atomicPatterns in
  let activePatterns = mapFoldWithKey
    (lam acc. lam k. lam v.
      if eqi (setSize v) 0 then
        snoc acc k
      else acc)
    []
    dependencyMap in
  let dependencies = mapAccumL
    (lam deps. lam i.
      (mapRemove i deps, i)) dependencyMap activePatterns in
  (activePatterns, dependencies.0)

-- Add the dependencies to the ParallelPattern structure. We add them to the
-- structure to avoid having to recompute them every time an atomic pattern is
-- checked.
let withDependencies :
     {atomicPatterns : [Pattern], replacement : (Map VarPattern Expr) -> Expr}
  -> ParallelPattern = lam pat.
  recursive let work : [(Int, Pattern)] -> Pattern -> [(Int, Pattern)] =
    lam acc. lam pat.
    let idx = getPatternIndex pat in
    let acc = cons (idx, pat) acc in
    match getInnerPatterns pat with Some pats then
      foldl work acc pats
    else acc
  in
  match getPatternDependencies pat.atomicPatterns with (activePatterns, dependencies) then
    let nestedPatterns = foldl work [] pat.atomicPatterns in
    let patMap = mapFromSeq subi nestedPatterns in
    { atomicPatternMap = patMap
    , activePatterns = activePatterns
    , dependencies = dependencies
    , replacement = pat.replacement }
  else never

let mapPattern : () -> ParallelPattern =
  use MExprParallelKeywordMaker in
  lam.
  let s = nameSym "s" in
  let acc = nameSym "acc" in
  let atomicPatterns = [
    FixedAppPattern {id = 0, fn = uconst_ (CNull ()), vars = [PatternName s]},
    BranchPattern {id = 1, cond = PatternIndex 0,
      thn = [ReturnPattern {id = 2, var = PatternName acc}],
      els = [
        FixedAppPattern {id = 3, fn = uconst_ (CTail ()), vars = [PatternName s]},
        FixedAppPattern {id = 4, fn = uconst_ (CHead ()), vars = [PatternName s]},
        UnknownAppPattern {id = 5, vars = [PatternIndex 4]},
        SeqPattern {id = 6, vars = [PatternIndex 5]},
        FixedAppPattern {id = 7, fn = uconst_ (CConcat ()),
                       vars = [PatternName acc, PatternIndex 6]},
        RecursionPattern {id = 8, binds = [(s, 3), (acc, 7)]},
        ReturnPattern {id = 9, var = PatternIndex 8}
      ]},
    ReturnPattern {id = 10, var = PatternIndex 1}
  ] in
  let replacement : (Map VarPattern Expr) -> Expr = lam matches.
    match mapLookup (PatternIndex 4) matches with fExpr then
      match mapLookup (PatternIndex 3) matches with headExpr then
        let x = nameSym "x" in
        let f = nulam_ x (substituteExpression fExpr headExpr (nvar_ x)) in
        match mapLookup (PatternName s) matches with sExpr then
          parallelMap_ f sExpr
        else never
      else never
    else never
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let reducePattern : () -> ParallelPattern =
  use MExprParallelKeywordMaker in
  lam.
  let s = nameSym "s" in
  let acc = nameSym "acc" in
  let atomicPatterns = [
    FixedAppPattern {id = 0, fn = uconst_ (CNull ()), vars = [PatternName s]},
    BranchPattern {id = 1, cond = PatternIndex 0,
      thn = [ReturnPattern {id = 2, var = PatternName acc}],
      els = [
        FixedAppPattern {id = 3, fn = uconst_ (CTail ()), vars = [PatternName s]},
        FixedAppPattern {id = 4, fn = uconst_ (CHead ()), vars = [PatternName s]},
        UnknownAppPattern {id = 5, vars = [PatternName acc, PatternIndex 4]},
        RecursionPattern {id = 6, binds = [(s, 3), (acc, 5)]},
        ReturnPattern {id = 7, var = PatternIndex 6}
      ]},
    ReturnPattern {id = 8, var = PatternIndex 1}
  ] in
  let replacement : Map VarPattern Expr -> Expr = lam matches.
    match mapLookup (PatternIndex 4) matches with fExpr then
      match mapLookup (PatternName acc) matches with accExpr then
        match mapLookup (PatternIndex 3) matches with headExpr then
          let x = nameSym "x" in
          let y = nameSym "y" in
          let f = nulam_ x (nulam_ y (
            substituteExpression
              (substituteExpression fExpr accExpr (nvar_ x))
              fExpr (nvar_ y))) in
          match mapLookup (PatternName s) matches with sExpr then
            parallelReduce_ f accExpr sExpr
          else never
        else never
      else never
    else never
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

-- This function extracts the name of a TmVar and returns an option containing
-- the name, assuming that the given expression is always a variable. If this
-- assumption does not hold, it returns None.
let getVariableIdentifier : Expr -> Option Name =
  use MExprParallelKeywordMaker in
  lam varExpr.
  match varExpr with TmVar {ident = ident} then Some ident
  else None ()

let applyPattern : PatternMatchState -> Name -> Expr -> Int -> PatternMatchState =
  lam state. lam boundVar. lam expr. lam patIndex.
  let active = filter (lam pidx. neqi pidx patIndex) state.active in
  let dependencies =
    mapMap (lam deps : Set Int. setRemove patIndex deps) state.dependencies in
  let part =
    partition
      (lam kv : (Int, Set Int). eqi (setSize kv.1) 0)
      (mapToSeq dependencies) in
  match part with (emptyDependencies, nonEmptyDependencies) then
    let newActivePatternIndices = map (lam kv : (Int, Set Int). kv.0)
                                      emptyDependencies in
    let patternIndexToBoundVar =
      mapInsert patIndex boundVar state.patternIndexToBoundVar in
    let atomicPatternMatches =
      mapInsert patIndex expr state.atomicPatternMatches in
    {{{{state with active = concat active newActivePatternIndices}
              with dependencies = mapFromSeq subi nonEmptyDependencies}
              with patternIndexToBoundVar = patternIndexToBoundVar}
              with atomicPatternMatches = atomicPatternMatches}
  else never

let matchVariablePattern : [(Name, Type, Info)] -> Expr -> PatternMatchState
                        -> VarPattern -> Option PatternMatchState =
  use MExprParallelKeywordMaker in
  lam params. lam expr. lam state. lam pat.
  match expr with TmVar {ident = ident} then
    match pat with PatternIndex index then
      match mapLookup index state.patternIndexToBoundVar with Some matchedId then
        if nameEq ident matchedId then Some state else None ()
      else error (concat "Found reference to unmatched pattern with index "
                         (int2string index))
    else match pat with PatternName name then
      match find (lam param : (Name, Type, Info). nameEq param.0 ident) params
      with Some _ then
        match mapLookup name state.nameMatches with Some boundIdent then
          if nameEq ident boundIdent then Some state else None ()
        else
          let nameMatches = mapInsert name ident state.nameMatches in
          Some {state with nameMatches = nameMatches}
      else None ()
    else never
  else None ()

recursive
  let matchAtomicPattern : Map Int Pattern -> Name -> [(Name, Type, Info)] -> Expr
                        -> PatternMatchState -> Int -> Option PatternMatchState =
    use MExprParallelKeywordMaker in
    lam atomicPatternMap. lam bindingIdent. lam params. lam expr. lam state.
    lam patIdx.
    let checkVarPatterns : [VarPattern] -> [Expr] -> State -> Option State =
      lam patterns. lam exprs. lam state.
      let n = length patterns in
      recursive let work : State -> Int -> Option State = lam state. lam i.
        if lti i n then
          let pat = get patterns i in
          let expr = get exprs i in
          optionBind
            (matchVariablePattern params expr state pat)
            (lam updatedState. work updatedState (addi i 1))
        else Some state
      in
      if eqi (length exprs) n then
        work state 0
      else None ()
    in
    let matchArgsWithParams : [Expr] -> PatternMatchState -> VarPattern
                           -> Option Name -> Option PatternMatchState =
      lam args. lam state. lam bindingVar. lam bindingName.
      let n = length args in
      match optionMapM getVariableIdentifier args with Some argNames then
        recursive let work : PatternMatchState -> Int -> Option PatternMatchState =
          lam state. lam i.
          if lti i n then
            let argName = get argNames i in
            match bindingVar with PatternName id then
              match mapLookup id state.nameMatches with Some paramId then
                if nameEq argName paramId then
                  Some state
                else work state (addi i 1)
              else
                let nameMatches = mapInsert id argName state.nameMatches in
                Some {state with nameMatches = nameMatches}
            else match bindingVar with PatternIndex idx then
              match mapLookup idx state.patternIndexToBoundVar with Some boundVar then
                if nameEq boundVar argName then
                  match bindingName with Some id then
                    match mapLookup id state.nameMatches with Some paramIdent then
                      let paramEqName : (Name, Type, Info) -> Bool = lam param.
                        nameEq param.0 paramIdent
                      in
                      optionMap
                        (lam. state)
                        (find paramEqName params)
                    else error "Invalid internal state"
                  else Some state
                else work state (addi i 1)
              else
                error (concat "Found reference to unmatched pattern with index "
                              (int2string idx))
            else never
          else None ()
        in
        work state 0
      else
        error "Arguments of function call were not in ANF"
    in
    match mapLookup patIdx atomicPatternMap with Some pat then
      match pat with FixedAppPattern t then
        match expr with TmApp _ then
          match collectAppArguments expr with (f, args) then
            if eqExpr t.fn f then
              checkVarPatterns t.vars args state
            else None ()
          else None ()
        else None ()
      else match pat with UnknownAppPattern t then
        match expr with TmApp _ then
          match collectAppArguments expr with (_, args) then
            let matchWithParams : State -> VarPattern -> Option State =
              lam state. lam var.
              matchArgsWithParams args state var (None ())
            in
            optionFoldlM matchWithParams state t.vars
          else never
        else None ()
      else match pat with BranchPattern t then
        match expr with TmMatch t2 then
          match matchVariablePattern params t2.target state t.cond
          with Some updatedState then
            let updatedState : PatternMatchState = updatedState in
            match getPatternDependencies t.thn with (thnActive, thnDeps) then
              let thnState = {{updatedState with active = thnActive}
                                            with dependencies = thnDeps} in
              match matchAtomicPatterns atomicPatternMap bindingIdent
                                        params t2.thn thnState
              with Some finalThnState then
                if isFinalState finalThnState then
                  match getPatternDependencies t.els with (elsActive, elsDeps) then
                    let finalThnState : PatternMatchState = finalThnState in
                    let elsState =
                      {{finalThnState with active = elsActive}
                                      with dependencies = elsDeps} in
                    match matchAtomicPatterns atomicPatternMap bindingIdent
                                              params t2.els elsState
                    with Some finalElsState then
                      if isFinalState finalElsState then
                        let finalElsState : PatternMatchState = finalElsState in
                        Some {{finalElsState with active = updatedState.active}
                                             with dependencies = updatedState.dependencies}
                      else None ()
                    else None ()
                  else never
                else None ()
              else None ()
            else never
          else None ()
        else None ()
      else match pat with SeqPattern t then
        match expr with TmSeq {tms = tms} then
          match checkVarPatterns t.vars tms state with Some updatedState then
            Some updatedState
          else None ()
        else None ()
      else match pat with RecursionPattern t then
        match expr with TmApp _ then
          match collectAppArguments expr with (f, args) then
            match getVariableIdentifier f with Some fId then
              if nameEq bindingIdent fId then
                let bindings : [(Name, VarPattern)] =
                  map
                    (lam binding : (Name, Int). (binding.0, PatternIndex binding.1))
                    t.binds in
                let matchWithParams : State -> (Name, Expr) -> Option State =
                  lam state. lam binding.
                  matchArgsWithParams args state binding.1 (Some binding.0)
                in
                optionFoldlM matchWithParams state bindings
              else None ()
            else error "Expected function application to be in ANF"
          else never
        else None ()
      else match pat with ReturnPattern t then
        None ()
      else never
    else
      error (concat "Could not find pattern with index " (int2string patIdx))

  let matchAtomicPatterns : Map Int Pattern -> Name -> [(Name, Type, Info)]
                         -> Expr -> PatternMatchState -> Option PatternMatchState =
    use MExprParallelKeywordMaker in
    lam atomicPatternMap. lam bindingIdent. lam params. lam expr. lam state.
    match expr with TmLet {ident = ident, body = body, inexpr = inexpr} then
      let updatedState =
        foldl
          (lam state. lam patIdx.
            match matchAtomicPattern atomicPatternMap bindingIdent params body
                                     state patIdx
            with Some updatedState then
              applyPattern updatedState ident body patIdx
            else state)
          state
          state.active in
      matchAtomicPatterns atomicPatternMap bindingIdent params inexpr updatedState
    else match expr with TmVar {ident = ident} then
      if and (eqi (length state.active) 1) (mapIsEmpty state.dependencies) then
        let patIdx = head state.active in
        match mapLookup patIdx atomicPatternMap
        with Some (ReturnPattern {var = pvar}) then
          optionMap
            (lam state : PatternMatchState.
              applyPattern state ident expr patIdx)
            (matchVariablePattern params expr state pvar)
        else None ()
      else None ()
    else match expr with TmRecLets t then
      matchAtomicPatterns atomicPatternMap bindingIdent params t.inexpr state
    else None ()
end

let constructLookup : PatternMatchState -> Map VarPattern Expr = lam state.
  let lookup =
    mapFoldWithKey
      (lam acc. lam patIdx. lam patExpr : Expr.
        let key = PatternIndex patIdx in
        mapInsert key patExpr acc)
      (mapEmpty cmpVarPattern) state.atomicPatternMatches in
  mapFoldWithKey
    (lam acc. lam patFnName. lam paramName.
      let key = PatternName patFnName in
      let value = nvar_ paramName in
      mapInsert key value acc)
    lookup state.nameMatches

let matchPattern : RecLetBinding -> ParallelPattern -> Option (Map VarPattern Expr) =
  use MExprParallelKeywordMaker in
  lam binding. lam pattern.
  let initialState = {
    active = pattern.activePatterns,
    dependencies = pattern.dependencies,
    patternIndexToBoundVar = mapEmpty subi,
    atomicPatternMatches = mapEmpty subi,
    nameMatches = mapEmpty nameCmp
  } in
  match functionParametersAndBody binding.body with (params, body) then
    let result = matchAtomicPatterns pattern.atomicPatternMap binding.ident
                                     params body initialState in
    optionBind
      result
      (lam state.
        if isFinalState state then
          Some (constructLookup state)
        else None ())
  else never

lang MExprParallelPattern = MExprParallelKeywordMaker
  sem parallelPatternRewrite =
  | t ->
    t
    -- 1. Go through all recursive bindings in the given expression and store
    --    information about whether they are to be rewritten and if so, to
    --    what. Could use a map of type Map Name ParallelPattern for this.
    -- 2. Go through expression and eliminate all recursive bindings whose
    --    names are found in the map and replace all function calls to that
    --    function by the parallel pattern (using the appropriate parameters,
    --    which has to be recorded somehow). For partial applications, the call
    --    must be wrapped in lambdas to ensure correct parameters are used.
    
end

lang TestLang =
  MExprANF + MExprRewrite + MExprParallelKeywordMaker + MExprTailRecursion +
  MExprPrettyPrint

mexpr

use TestLang in

type PatternMatchResult = Option (Map VarPattern Expr) in

let preprocess : Expr -> Expr = lam e.
  normalizeTerm (tailRecursive (rewriteTerm e))
in

let matchBindingsWithPattern : Expr -> ParallelPattern -> [PatternMatchResult] =
  lam bindings. lam pattern.
  match bindings with TmRecLets {bindings = bindings} then
    map (lam binding. matchPattern binding pattern) bindings
  else never
in

let map = nameSym "map" in
let f = nameSym "f" in
let s = nameSym "s" in
let h = nameSym "h" in
let t = nameSym "t" in
let expr = preprocess (nreclets_ [
  (map, tyunknown_, nulam_ f (nulam_ s (
    match_ (nvar_ s)
      (pseqtot_ [])
      (seq_ [])
      (match_ (nvar_ s)
        (pseqedgen_ [npvar_ h] t [])
        (cons_ (app_ (nvar_ f) (head_ (nvar_ s)))
               (appf2_ (nvar_ map) (nvar_ f) (tail_ (nvar_ s))))
        never_))))
]) in
let mapPatternMatchResult = matchBindingsWithPattern expr (mapPattern ()) in
let fst = optionGetOrElse (lam. never) (get mapPatternMatchResult 0) in
utest mapLookup (PatternIndex 0) fst with Some (null_ (nvar_ s)) using optionEq eqExpr in
utest mapLookup (PatternIndex 3) fst with Some (tail_ (nvar_ s)) using optionEq eqExpr in
utest mapLookup (PatternIndex 4) fst with Some (head_ (nvar_ s)) using optionEq eqExpr in
let recursiveCall = appf3_ (nvar_ map) (var_ "acc") (var_ "f") (var_ "t") in
utest mapLookup (PatternIndex 8) fst with Some recursiveCall using optionEq eqExpr in
utest mapSize fst with 13 in
let snd = get mapPatternMatchResult 1 in
utest optionIsNone snd with true in

let fold = nameSym "fold" in
let acc = nameSym "acc" in
let expr = preprocess (nreclets_ [
  (fold, tyunknown_, nulam_ f (nulam_ acc (nulam_ s (
    match_ (nvar_ s)
      (pseqedgen_ [npvar_ h] t [])
      (appf3_ (nvar_ fold)
        (nvar_ t)
        (appf2_ (nvar_ f) (nvar_ acc) (nvar_ h))
        (nvar_ f))
      (match_ (nvar_ s)
        (pseqtot_ [])
        (nvar_ acc)
        never_)))))
]) in
let reducePatternMatchResult = matchBindingsWithPattern expr (reducePattern ()) in
let fst = optionGetOrElse (lam. never) (get reducePatternMatchResult 0) in
utest mapLookup (PatternIndex 0) fst with Some (null_ (nvar_ s)) using optionEq eqExpr in
utest mapLookup (PatternIndex 2) fst with Some (nvar_ acc) using optionEq eqExpr in
let reduceFuncApp = appf2_ (nvar_ f) (nvar_ acc) (nvar_ h) in
utest mapLookup (PatternIndex 5) fst with Some reduceFuncApp using optionEq eqExpr in
utest mapLookup (PatternIndex 7) fst with Some (var_ "t") using optionEq eqExpr in
utest mapSize fst with 11 in

()
