include "set.mc"
include "mexpr/anf.mc"
include "pmexpr/parallel-patterns.mc"
include "pmexpr/rules.mc"
include "pmexpr/tailrecursion.mc"
include "pmexpr/utils.mc"

type Argument = use Ast in (Name, Type, Info)

type PatternMatchState = use Ast in {
  -- A sequence of indices of the active patterns. These are patterns whose
  -- dependencies have been matched with expressions, but which have not been
  -- matched themselves.
  active : [Int],

  -- Maps the index of an unmatched pattern to a set of indices, representing
  -- the active patterns it depends on.
  patternDependencies : Map Int (Set Int),

  -- Maps the index of a pattern to the name of the variable the expression it
  -- matched with was bound to.
  patternIndexToBoundVar : Map Int Name,

  -- Maps the index of a pattern to the expression it matched with.
  atomicPatternMatches : Map Int Expr,

  -- Maps the name of a parameter to the argument it has matched with.
  nameMatches : Map Name Argument,

  -- Maps the name of a variable to the set of variable patterns on which it
  -- depends.
  variableDependencies: Map Name (Set VarPattern),

  -- The parallel pattern being matched on.
  pattern: Pattern
}

let emptyPatternMatchState = lam p : Pattern. {
  active = [],
  patternDependencies = mapEmpty subi,
  patternIndexToBoundVar = mapEmpty subi,
  atomicPatternMatches = mapEmpty subi,
  nameMatches = mapEmpty nameCmp,
  variableDependencies = mapEmpty nameCmp,
  pattern = p
}

let isFinalState : PatternMatchState -> Bool = lam state.
  match state with {active = [], patternDependencies = deps} then
    mapIsEmpty deps
  else false

-- This function extracts the name of a TmVar and returns an option containing
-- the name, assuming that the given expression is always a variable. If this
-- assumption does not hold, it returns None.
let getVariableIdentifier : use Ast in Expr -> Option Name =
  use PMExprAst in
  lam varExpr.
  match varExpr with TmVar {ident = ident} then Some ident
  else None ()

let findVariableDependencies : use Ast in PatternMatchState -> Expr -> Set VarPattern =
  use PMExprAst in
  lam state. lam expr.
  recursive let work : Set VarPattern -> Expr -> Set VarPattern = lam acc. lam expr.
    match expr with TmVar {ident = ident} then
      match mapLookup ident state.variableDependencies with Some deps then
        setUnion acc deps
      else
        setInsert (PatternName ident) acc
    else sfold_Expr_Expr work acc expr
  in work (setEmpty cmpVarPattern) expr

let updateVariableDependencies : use Ast in PatternMatchState -> Name -> Expr
                              -> Option Int -> PatternMatchState =
  lam state. lam ident. lam body. lam optPatIdx.
  let bodyDependencies =
    let deps = findVariableDependencies state body in
    match optPatIdx with Some idx then
      setInsert (PatternIndex idx) deps
    else deps
  in
  {state with variableDependencies =
    mapInsert ident bodyDependencies state.variableDependencies}

let applyPattern : use Ast in PatternMatchState -> Name -> Expr -> Int -> PatternMatchState =
  use PMExprAst in
  lam state. lam boundVar. lam expr. lam patIndex.
  match mapLookup patIndex state.pattern.atomicPatternMap with Some pat then
    let active =
      let activeWithoutCurrPat =
        filter (lam pidx. neqi pidx patIndex) state.active in
      match pat with UnknownOpPattern _ then
        -- Keep the UnknownOpPattern among active patterns until a pattern
        -- depending on it is matched.
        snoc activeWithoutCurrPat patIndex
      else
        -- Remove an active UnknownOpPattern if the matched pattern depends on
        -- it.
        let activeMatchedUnknownOpPatterns =
          findMap
          (lam varPat : VarPattern.
            match varPat with PatternIndex idx then
              optionBind
                (mapLookup idx state.pattern.atomicPatternMap)
                (lam pat : AtomicPattern.
                  match pat with UnknownOpPattern _ then
                    Some idx
                  else None ())
            else None ())
          (getShallowVarPatternDependencies pat) in
        match activeMatchedUnknownOpPatterns with Some idx then
          filter (lam pidx. neqi pidx idx) activeWithoutCurrPat
        else activeWithoutCurrPat
    in
    let dependencies = mapMap (lam deps : Set Int. setRemove patIndex deps)
                              state.patternDependencies in
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
      {{{{state with active = concat newActivePatternIndices active}
                with patternDependencies = mapFromSeq subi nonEmptyDependencies}
                with patternIndexToBoundVar = patternIndexToBoundVar}
                with atomicPatternMatches = atomicPatternMatches}
    else never
  else
    error (concat "Found reference to undefined pattern with index "
                  (int2string patIndex))

let matchVariablePattern : use Ast in Expr -> PatternMatchState -> VarPattern
                        -> Option PatternMatchState =
  use PMExprAst in
  lam expr. lam state. lam varPat.
  match expr with TmVar {ident = ident, ty = ty, info = info} then
    match varPat with PatternIndex index then
      match mapLookup index state.patternIndexToBoundVar with Some matchedId then
        if nameEq ident matchedId then Some state else None ()
      else
        error (concat "Found reference to unmatched pattern with index "
                      (int2string index))
    else match varPat with PatternName name then
      match mapLookup name state.nameMatches with Some (boundIdent, _, _) then
        if nameEq ident boundIdent then Some state else None ()
      else
        let arg = (ident, ty, info) in
        let nameMatches = mapInsert name arg state.nameMatches in
        Some {state with nameMatches = nameMatches}
    else None ()
  else match expr with TmConst {val = CInt {val = n1}} then
    match varPat with PatternLiteralInt n2 then
      if eqi n1 n2 then Some state else None ()
    else None ()
  else None ()

recursive
  let matchAtomicPattern : use Ast in Name -> [(Name, Type, Info)] -> Expr
                        -> PatternMatchState -> Int -> Option PatternMatchState =
    use PMExprAst in
    lam bindingIdent. lam params. lam expr. lam state. lam patIdx.
    let checkVarPatterns : [VarPattern] -> [Expr] -> PatternMatchState -> Option PatternMatchState =
      lam patterns. lam exprs. lam state.
      let n = length patterns in
      recursive let work : PatternMatchState -> Int -> Option PatternMatchState =
        lam state. lam i.
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
    let matchArgsWithParams : use Ast in [Expr] -> PatternMatchState -> VarPattern
                           -> Option Name -> Option PatternMatchState =
      lam args. lam state. lam bindingVar. lam bindingName.
      let n = length args in
      recursive let work : PatternMatchState -> Int -> Option PatternMatchState =
        lam state. lam i.
        if lti i n then
          let arg = get args i in
          match bindingVar with PatternName id then
            match arg with TmVar {ident = argName, ty = ty, info = info} then
              match mapLookup id state.nameMatches with Some (paramName, _, _) then
                if nameEq argName paramName then
                  Some state
                else work state (addi i 1)
              else
                let arg = (argName, ty, info) in
                let nameMatches = mapInsert id arg state.nameMatches in
                Some {state with nameMatches = nameMatches}
            else None ()
          else match bindingVar with PatternIndex idx then
            match getVariableIdentifier arg with Some argName then
              match mapLookup idx state.patternIndexToBoundVar
              with Some boundVar then
                match bindingName with Some id then
                  match mapLookup id state.nameMatches with Some (paramIdent, _, _) then
                    let paramEqName : (Name, Type, Info) -> Bool = lam param.
                      nameEq param.0 paramIdent
                    in
                    optionMap
                      (lam. state)
                      (find paramEqName params)
                  else error "Invalid internal state"
                else Some state
              else None ()
            else
              match mapLookup idx state.atomicPatternMatches with Some expr then
                if eqExpr arg expr then
                  Some state
                else None ()
              else error "Invalid internal state"
          else match bindingVar with PatternLiteralInt n1 then
            match arg with TmConst {val = CInt {val = n2}} then
              if eqi n1 n2 then Some state else None ()
            else None ()
          else never
        else None ()
      in
      work state 0
    in
    match mapLookup patIdx state.pattern.atomicPatternMap with Some pat then
      match pat with AppPattern t then
        match expr with TmApp _ then
          match collectAppArguments expr with (f, args) then
            if eqExpr t.fn f then
              checkVarPatterns t.vars args state
            else None ()
          else None ()
        else None ()
      else match pat with UnknownOpPattern t then
        let deps = findVariableDependencies state expr in
        let dependenciesContainsVarPat = lam varPat : VarPattern.
          match varPat with PatternIndex _ then
            setMem varPat deps
          else match varPat with PatternName paramId then
            match mapLookup paramId state.nameMatches with Some (argId, _, _) then
              setMem (PatternName argId) deps
            else false
          else false
        in
        if forAll dependenciesContainsVarPat t.vars then
          Some state
        else None ()
      else match pat with BranchPattern t then
        match expr with TmMatch t2 then
          match matchVariablePattern t2.target state t.cond
          with Some updatedState then
            let updatedState : PatternMatchState = updatedState in
            match getPatternDependencies t.thn with (thnActive, thnDeps) then
              let thnState = {{updatedState with active = thnActive}
                                            with patternDependencies = thnDeps} in
              match matchAtomicPatterns bindingIdent params t2.thn thnState
              with Some finalThnState then
                if isFinalState finalThnState then
                  match getPatternDependencies t.els with (elsActive, elsDeps) then
                    let finalThnState : PatternMatchState = finalThnState in
                    let elsState =
                      {{finalThnState with active = elsActive}
                                      with patternDependencies = elsDeps} in
                    match matchAtomicPatterns bindingIdent params t2.els elsState
                    with Some finalElsState then
                      if isFinalState finalElsState then
                        let finalElsState : PatternMatchState = finalElsState in
                        let deps = updatedState.patternDependencies in
                        let finalState =
                          {{finalElsState with active = updatedState.active}
                                          with patternDependencies = deps} in
                        Some finalState
                      else None ()
                    else None ()
                  else never
                else None ()
              else None ()
            else never
          else None ()
        else None ()
      else match pat with RecursionPattern t then
        match expr with TmApp _ then
          match collectAppArguments expr with (f, args) then
            match getVariableIdentifier f with Some fId then
              if nameEq bindingIdent fId then
                let matchWithParams : PatternMatchState -> (Name, VarPattern)
                                   -> Option PatternMatchState =
                  lam state. lam binding.
                  matchArgsWithParams args state binding.1 (Some binding.0)
                in
                optionFoldlM matchWithParams state t.binds
              else None ()
            else None ()
          else never
        else None ()
      else match pat with ReturnPattern _ then
        None ()
      else never
    else
      error (concat "Could not find pattern with index " (int2string patIdx))

  let matchAtomicPatterns : use Ast in Name -> [(Name, Type, Info)] -> Expr
                         -> PatternMatchState -> Option PatternMatchState =
    use PMExprAst in
    lam bindingIdent. lam params. lam expr. lam state.
    match expr with TmLet {ident = ident, body = body, inexpr = inexpr} then
      let updatedState =
        optionGetOrElse
          (lam. updateVariableDependencies state ident body (None ()))
          (findMap
            (lam patIdx.
              match matchAtomicPattern bindingIdent params body state patIdx
              with Some updatedState then
                let state = updateVariableDependencies updatedState ident body
                                                       (Some patIdx) in
                Some (applyPattern state ident body patIdx)
              else None ())
            state.active) in
      matchAtomicPatterns bindingIdent params inexpr updatedState
    else match expr with TmVar {ident = ident} then
      if and (eqi (length state.active) 1) (mapIsEmpty state.patternDependencies) then
        let patIdx = head state.active in
        match mapLookup patIdx state.pattern.atomicPatternMap
        with Some (ReturnPattern {var = pvar}) then
          optionMap
            (lam state : PatternMatchState.
              applyPattern state ident expr patIdx)
            (matchVariablePattern expr state pvar)
        else None ()
      else None ()
    else match expr with TmRecLets t then
      matchAtomicPatterns bindingIdent params t.inexpr state
    else None ()
end

let constructLookup : use Ast in PatternMatchState -> Map VarPattern (Name, Expr) =
  use MExprAst in
  lam state.
  let lookup =
    mapFoldWithKey
      (lam acc. lam patIdx. lam patExpr : Expr.
        let key = PatternIndex patIdx in
        match mapLookup patIdx state.patternIndexToBoundVar with Some id then
          mapInsert key (id, patExpr) acc
        else error "Could not find identifier matched with pattern")
      (mapEmpty cmpVarPattern) state.atomicPatternMatches in
  mapFoldWithKey
    (lam acc. lam patFnName. lam arg : Argument.
      let key = PatternName patFnName in
      match arg with (id, ty, info) in
      let param = TmVar {ident = id, ty = ty, info = info, frozen = false} in
      mapInsert key (id, param) acc)
    lookup state.nameMatches

let matchPattern =
  use PMExprAst in
  lam binding : RecLetBinding. lam pattern : Pattern.
  let initState =
    {{emptyPatternMatchState pattern
        with active = pattern.activePatterns}
        with patternDependencies = pattern.dependencies} in
  match functionParametersAndBody binding.body with (params, body) then
    let result = matchAtomicPatterns binding.ident params body initState in
    optionBind
      result
      (lam state.
        if isFinalState state then
          Some (constructLookup state)
        else None ())
  else never

lang TestLang =
  MExprANF + PMExprRewrite + PMExprAst + PMExprTailRecursion + MExprPrettyPrint
end

mexpr

use TestLang in

type PatternMatchResult = Option (Map VarPattern (Name, Expr)) in

let preprocess : Expr -> Expr = lam e.
  normalizeTerm (tailRecursive (rewriteTerm e))
in

let matchBindingsWithPattern : Expr -> Pattern -> [PatternMatchResult] =
  lam recLets. lam pattern.
  match recLets with TmRecLets {bindings = bindings} then
    map (lam binding. matchPattern binding pattern) bindings
  else never
in

let lookupSnd : VarPattern -> Map VarPattern (Name, Expr) -> Option Expr =
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
let expr = typeCheck (preprocess (nreclets_ [
  (map, tyunknown_, nlam_ f (tyarrow_ tyint_ tyint_) (nulam_ s (
    match_ (nvar_ s)
      (pseqtot_ [])
      (seq_ [])
      (match_ (nvar_ s)
        (pseqedgen_ [npvar_ h] t [])
        (cons_ (app_ (nvar_ f) (head_ (nvar_ s)))
               (appf2_ (nvar_ map) (nvar_ f) (tail_ (nvar_ s))))
        never_))))])) in
let mapPat = getMapPattern () in
let mapPatternMatchResult = matchBindingsWithPattern expr mapPat in
let fst = optionGetOrElse (lam. never) (get mapPatternMatchResult 0) in
utest lookupSnd (PatternIndex 0) fst with Some (null_ (nvar_ s)) using optionEq eqExpr in
utest lookupSnd (PatternIndex 3) fst with Some (tail_ (nvar_ s)) using optionEq eqExpr in
utest lookupSnd (PatternIndex 4) fst with Some (head_ (nvar_ s)) using optionEq eqExpr in
let recursiveCall = appf3_ (nvar_ map) (var_ "acc") (var_ "f") (var_ "t") in
utest lookupSnd (PatternIndex 7) fst with Some recursiveCall using optionEq eqExpr in
utest mapSize fst with 12 in

let map2id = nameSym "map2" in
let acc = nameSym "acc" in
let s2 = nameSym "s" in
let h2 = nameSym "h" in
let t2 = nameSym "t" in
let expr = preprocess (nreclets_ [
  (map2id, tyunknown_, nulam_ acc (nulam_ s (nulam_ s2 (
    match_ (nvar_ s)
      (pseqtot_ [])
      (nvar_ acc)
      (match_ (nvar_ s2)
        (pseqtot_ [])
        (nvar_ acc)
        (match_ (nvar_ s)
          (pseqedgen_ [npvar_ h] t [])
          (match_ (nvar_ s2)
            (pseqedgen_ [npvar_ h2] t2 [])
            (appf3_ (nvar_ map2id)
              (snoc_ (nvar_ acc) (muli_ (head_ (nvar_ s)) (head_ (nvar_ s2))))
              (tail_ (nvar_ s))
              (tail_ (nvar_ s2)))
            never_)
          never_))
  ))))
]) in
let map2Pat = getMap2Pattern () in
let map2PatternMatchResult = matchBindingsWithPattern expr map2Pat in
let fst = optionGetOrElse (lam. never) (get map2PatternMatchResult 0) in
utest lookupSnd (PatternIndex 6) fst with Some (tail_ (nvar_ s)) using optionEq eqExpr in
utest lookupSnd (PatternIndex 11) fst with Some (concat_ (nvar_ acc) (var_ "t"))
using optionEq eqExpr in
utest mapSize fst with 19 in

let fold = nameSym "fold" in
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
let reducePat = getReducePattern () in
let reducePatternMatchResult = matchBindingsWithPattern expr reducePat in
let fst = optionGetOrElse (lam. never) (get reducePatternMatchResult 0) in
utest lookupSnd (PatternIndex 0) fst with Some (null_ (nvar_ s)) using optionEq eqExpr in
utest lookupSnd (PatternIndex 2) fst with Some (nvar_ acc) using optionEq eqExpr in
let reduceFuncApp = appf2_ (nvar_ f) (nvar_ acc) (nvar_ h) in
utest lookupSnd (PatternIndex 5) fst with Some reduceFuncApp using optionEq eqExpr in
utest lookupSnd (PatternIndex 7) fst with Some (var_ "t") using optionEq eqExpr in
utest mapSize fst with 11 in

()
