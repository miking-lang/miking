include "mexpr/anf.mc"
include "mexpr/rewrite/parallel-patterns.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/tailrecursion.mc"
include "mexpr/rewrite/utils.mc"

include "set.mc"

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
  lam expr. lam state. lam pat.
  match expr with TmVar {ident = ident} then
    match pat with PatternIndex index then
      match mapLookup index state.patternIndexToBoundVar with Some matchedId then
        if nameEq ident matchedId then Some state else None ()
      else error (concat "Found reference to unmatched pattern with index "
                         (int2string index))
    else match pat with PatternName name then
      match mapLookup name state.nameMatches with Some boundIdent then
        if nameEq ident boundIdent then Some state else None ()
      else
        let nameMatches = mapInsert name ident state.nameMatches in
        Some {state with nameMatches = nameMatches}
    else None ()
  else match expr with TmConst {val = CInt {val = n1}} then
    match pat with PatternLiteralInt n2 then
      if eqi n1 n2 then Some state else None ()
    else None ()
  else None ()

recursive
  let matchAtomicPattern : Map Int AtomicPattern -> Name -> [(Name, Type, Info)] -> Expr
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
            (matchVariablePattern expr state pat)
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
            else match bindingVar with PatternLiteralInt n then
              error "Not implemented yet"
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
          match matchVariablePattern t2.target state t.cond
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
                let matchWithParams : State -> (Name, Expr) -> Option State =
                  lam state. lam binding.
                  matchArgsWithParams args state binding.1 (Some binding.0)
                in
                optionFoldlM matchWithParams state t.binds
              else None ()
            else None ()
          else never
        else None ()
      else match pat with ReturnPattern t then
        None ()
      else never
    else
      error (concat "Could not find pattern with index " (int2string patIdx))

  let matchAtomicPatterns : Map Int AtomicPattern -> Name -> [(Name, Type, Info)]
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
            (matchVariablePattern expr state pvar)
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
        match mapLookup patIdx state.patternIndexToBoundVar with Some id then
          mapInsert key (id, patExpr) acc
        else error "Could not find identifier matched with pattern")
      (mapEmpty cmpVarPattern) state.atomicPatternMatches in
  mapFoldWithKey
    (lam acc. lam patFnName. lam paramName.
      let key = PatternName patFnName in
      mapInsert key (paramName, nvar_ paramName) acc)
    lookup state.nameMatches

let matchPattern : RecLetBinding -> Pattern -> Option (Map VarPattern Expr) =
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

lang TestLang =
  MExprANF + MExprRewrite + MExprParallelKeywordMaker + MExprTailRecursion +
  MExprPrettyPrint

mexpr

use TestLang in

type PatternMatchResult = Option (Map VarPattern (Name, Expr)) in

let preprocess : Expr -> Expr = lam e.
  normalizeTerm (tailRecursive (rewriteTerm e))
in

let matchBindingsWithPattern : Expr -> Pattern -> [PatternMatchResult] =
  lam bindings. lam pattern.
  match bindings with TmRecLets {bindings = bindings} then
    map (lam binding. matchPattern binding pattern) bindings
  else never
in

let lookupSnd : VarPattern -> PatternMatchResult -> Option Expr =
  lam pat. lam result.
  optionMap
    (lam p : (Name, Expr). p.1)
    (mapLookup pat result)
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
let mapPat = mapPattern () in
let mapPatternMatchResult = matchBindingsWithPattern expr mapPat in
let fst = optionGetOrElse (lam. never) (get mapPatternMatchResult 0) in

utest lookupSnd (PatternIndex 0) fst with Some (null_ (nvar_ s)) using optionEq eqExpr in
utest lookupSnd (PatternIndex 3) fst with Some (tail_ (nvar_ s)) using optionEq eqExpr in
utest lookupSnd (PatternIndex 4) fst with Some (head_ (nvar_ s)) using optionEq eqExpr in
let recursiveCall = appf3_ (nvar_ map) (var_ "acc") (var_ "f") (var_ "t") in
utest lookupSnd (PatternIndex 8) fst with Some recursiveCall using optionEq eqExpr in
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
        (nvar_ f)
        (appf2_ (nvar_ f) (nvar_ acc) (nvar_ h))
        (nvar_ t))
      (match_ (nvar_ s)
        (pseqtot_ [])
        (nvar_ acc)
        never_)))))
]) in
let reducePat = reducePattern () in
let reducePatternMatchResult = matchBindingsWithPattern expr reducePat in
let fst = optionGetOrElse (lam. never) (get reducePatternMatchResult 0) in
utest lookupSnd (PatternIndex 0) fst with Some (null_ (nvar_ s)) using optionEq eqExpr in
utest lookupSnd (PatternIndex 2) fst with Some (nvar_ acc) using optionEq eqExpr in
let reduceFuncApp = appf2_ (nvar_ f) (nvar_ acc) (nvar_ h) in
utest lookupSnd (PatternIndex 5) fst with Some reduceFuncApp using optionEq eqExpr in
utest lookupSnd (PatternIndex 7) fst with Some (var_ "t") using optionEq eqExpr in
utest mapSize fst with 11 in

()
