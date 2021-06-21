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
  atomicPatterns : [Pattern],
  activePatterns : [Int],
  dependencies : Map Int (Set Int),
  replacement : (Map VarPattern Expr) -> Expr
}

type PatternMatchState = {
  active : [Pattern],
  dependencies : Map Int (Set Int),
  patternVarIndices : Map Int Name,
  atomicPatternMatches : Map Int Expr,
  nameMatches : Map Name Name
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

-- Constructs a mapping from every pattern index to a set containing the
-- indices of patterns on which the pattern depends on. A pattern is considered
-- to depend on a pattern with index i if it contains a PatternIndex i.
--
-- This function is implemented with the assumption that every pattern has been
-- given a unique index. If multiple patterns with the same index are found, an
-- error will be reported.
let getPatternDependencies : [Pattern] -> Map Int (Set Int) =
  lam atomicPatterns.
  recursive let atomicPatternDependencies : Map Int (Set Int) -> Pattern
                                         -> ([Pattern], Map Int (Set Int)) =
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
      let dependencies = mapInsert id patternDeps dependencies in
      match getInnerPatterns p with Some pats then
        let innerDeps = foldl atomicPatternDependencies (mapEmpty subi) pats in
        mapUnion dependencies (mapMap (lam v. setInsert id v) innerDeps)
      else dependencies
    else
      error (join ["Found multiple atomic patterns with id ",
                   int2string id])
  in
  let dependencyMap =
    foldl atomicPatternDependencies (mapEmpty subi) atomicPatterns in
  let activePatterns = mapFoldWithKey
    (lam acc. lam k. lam v.
      if eqi (setSize v) 0 then
        snoc acc (get atomicPatterns k)
      else acc)
    []
    dependencyMap in
  let dependencies = mapAccumL
    (lam deps. lam p.
      let i = getPatternIndex p in
      (mapRemove i deps, p)) dependencyMap activePatterns in
  (activePatterns, dependencies.0)


-- Add the dependencies to the ParallelPattern structure. We add them to the
-- structure to avoid having to recompute them every time an atomic pattern is
-- checked.
let withDependencies :
  {atomicPatterns : [Pattern],
   replacement : (Map VarPattern Expr) -> Expr} -> ParallelPattern = lam pat.
  match getPatternDependencies pat.atomicPatterns with (activePatterns, dependencies) then
    { atomicPatterns = pat.atomicPatterns
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
        FixedAppPattern {id = 7, fn = Some (uconst_ (CConcat ())),
                       vars = [PatternName acc, PatternIndex 6]},
        RecursionPattern {id = 8, binds = [(s, 3), (acc, 7)]},
        ReturnPattern {id = 9, var = PatternIndex 8}
      ]},
    ReturnPattern {id = 10, var = PatternIndex 1}
  ] in
  let replacement : Map VarPattern Expr -> Expr = lam matches.
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

let matchVariablePattern : [(Name, Type, Info)] -> Expr -> PatternMatchState
                        -> VarPattern -> Some PatternMatchState =
  use MExprParallelKeywordMaker in
  lam params. lam expr. lam state. lam pat.
  match expr with TmVar {ident = ident} then
    match pat with PatternIndex index then
      match mapLookup index state.patternVarIndices with Some matchedId then
        if nameEq ident matchedId then Some state else None ()
      else error (concat "Found reference to unmatched pattern with index "
                         (int2string index))
    else match pat with PatternName name then
      match mapLookup name state.nameMatches with Some boundIdent then
        if nameEq ident boundIdent then Some state else None ()
      else
        let nameMatches = mapInsert name ident state.nameMatches in
        Some {state with nameMatches = nameMatches}
    else never
  else None ()

let matchAtomicPattern : Name -> [(Name, Type, Info)] -> Expr
                      -> PatternMatchState -> Pattern -> PatternMatchState =
  use MExprParallelKeywordMaker in
  lam bindingIdent. lam params. lam expr. lam state. lam pat.
  let checkVarPatterns : [VarPattern] -> [Expr] -> State -> Option State =
    lam patterns. lam exprs. lam state.
    let n = length patterns in
    recursive let work : State -> Int -> Option State  = lam state. lam i.
      if lti i n then
        let pat = get patterns i in
        let expr = get exprs i in
        optionMap
          (lam updatedState. work updatedState (addi i 1))
          (matchVariablePattern params expr state pat)
      else Some state
    in
    if eqi (length exprs) n then
      work state 0
    else None ()
  in
  let matchArgsWithParams : [(Name, Type, Info)] -> [Expr] -> State
                         -> VarPattern -> Option Name -> Option State =
    lam args. lam state. lam bindingVar. lam bindingName.
    let n = length args in
    recursive let work : State -> Int -> Option State = lam state. lam i.
      if lti i n then
        let arg = get args i in
        match bindingVar with PatternName id then
          match arg with TmVar {ident = ident} then
            match mapLookup id state.nameMatches with Some paramId then
              if nameEq ident paramId then
                Some state
              else work state (addi i 1)
            else
              let nameMatches = mapInsert id ident state.nameMatches in
              Some {state with nameMatches = nameMatches}
          else work state (addi i 1)
        else match bindingVar with PatternIndex idx then
          match mapLookup idx state.atomicPatternMatches with Some bindingExpr then
            if eqExpr arg bindingExpr then
              match bindingName with Some id then
                let param : (Name, Type, Info) = get params i in
                match mapLookup id state.nameMatches with Some paramIdent then
                  if nameEq param.0 paramIdent then
                    Some state
                  else work state (addi i 1)
                else
                  let nameMatches = mapInsert id param.0 state.nameMatches in
                  Some {state with nameMatches = nameMatches}
              else Some state
            else work state (addi i 1)
          else
            error (concat "Found reference to unmatched pattern with index "
                          (int2string idx))
        else never
      else None ()
    in
    if eqi (length args) n then
      work state 0
    else None ()
  in
  match pat with FixedAppPattern t then
    match expr with TmApp _ then
      match collectAppArguments expr with (f, args) then
        if eqExpr t.fn f then
          match checkVarPatterns t.vars args state with Some updatedState then
            -- Pattern matched
            updatedState
          else state
        else state
      else state
    else state
  else match pat with UnknownAppPattern t then
    match expr with TmApp _ then
      match collectAppArguments expr with (_, args) then
        let matchWithParams : State -> VarPattern -> Option State =
          lam state. lam var.
          matchArgsWithParams args state var (None ())
        in
        match optionFoldlM (matchArgsWithParams params args) state t.vars
        with Some updatedState then
          -- Pattern matched
          updatedState
        else state
      else never
    else state
  else match pat with BranchPattern t then
    match expr with TmMatch t2 then
      match matchVariablePattern params t2.target state t.cond
      with Some updatedState then
        -- TODO: create a "nested" pattern state for the if- and else-branches
        -- and use these to do pattern checking for the thn and els pattern
        -- sequences.
        updatedState
      else state
    else state
  else match pat with SeqPattern t then
    match expr with TmSeq {tms = tms} then
      match checkVarPatterns t.vars tms state with Some updatedState then
        -- Pattern matched, now we have to:
        -- 1. remove from active pattern sequence
        -- 2. update dependencies accordingly
        updatedState
      else state
    else state
  else match pat with RecursionPattern t then
    match expr with TmApp _ then
      match collectAppArguments expr with (f, args) then
        if nameEq bindingIdent f then
          let bindings : [(Name, VarPattern)] =
            map
              (lam binding : (Name, Int). (binding.0, PatternIndex binding.1))
              t.binds in
          let matchWithParams : State -> (Name, Expr) -> Option State =
            lam state. lam binding.
            matchArgsWithParams params args state binding.1 (Some binding.0)
          in
          match optionFoldlM matchWithParams state bindings
          with Some updatedState then
            -- Pattern matched
            updatedState
          else state
        else state
      else never
    else state
  else match pat with ReturnPattern t then
    state
  else never

let matchPattern : RecLetBinding -> ParallelPattern -> Option (Map VarPattern Expr) =
  use MExprParallelKeywordMaker in
  lam binding. lam pattern.
  recursive let checkAtomicPatterns
    : PatternMatchState -> Expr -> [(Name, Type, Info)] -> Option PatternMatchState =
    lam state. lam body. lam params.
    match body with TmLet {ident = ident, body = expr, inexpr = inexpr} then
      let updatedState =
        foldl
          (lam state. lam pat. matchAtomicPattern binding.ident params expr state pat)
          state
          state.active in
      checkAtomicPatterns updatedState inexpr params
    else match body with TmVar {ident = ident} then
      match state.active with [ReturnPattern {var = pvar}] then
        matchVariablePattern params body state pvar
      else None ()
    else match body with TmRecLets t then
      checkAtomicPatterns state t.inexpr params
    else None ()
  in
  let initialState = {
    active = pattern.activePatterns,
    dependencies = pattern.dependencies,
    patternVarIndices = mapEmpty subi,
    atomicPatternMatches = mapEmpty subi,
    nameMatches = mapEmpty nameCmp
  } in
  dprintLn initialState.active;
  (mapMapWithKey (lam k. lam v. dprint k; print " "; dprintLn (setToSeq v)) initialState.dependencies);
  (match functionParametersAndBody binding.body with (params, body) then
    let finalState = checkAtomicPatterns initialState body params in
    dprintLn finalState;
    ()
  else never);
  -- * Go through let-expressions of the body of the binding, check for matches
  --   with the atomic patterns.
  let x = 0 in

  -- * When a match is found, update set of "active" atomic patterns to be
  --   checked. Also insert the matching expression into the 'matches' map.
  let y = 0 in

  -- * If all atomic patterns are matched, pass the 'matches' map to the
  --   replacement function of the pattern. This part will always work given
  --   that the definition replacement function is valid with respect to the
  --   atomic patterns.
  let allAtomicPatternsMatched = false in
  if allAtomicPatternsMatched then
    Some ()
  else None ()

let x = matchPattern {ident = nameNoSym "x", body = unit_} (mapPattern ())

let _optionGetExn : Option (Info -> Expr) -> Info -> Expr = lam o. lam info.
  match o with Some v then
    v info
  else error "Could not find variable of parallel pattern"

let mapPattern = use MExprParallelKeywordMaker in
  lam.
  let map = nameSym "map" in
  let f = nameSym "f" in
  let s = nameSym "s" in
  let acc = nameSym "acc" in
  { ident = map
  , expr = if_ (null_ (nvar_ s))
    (nvar_ acc)
    (appf3_ (nvar_ map)
      (nvar_ f)
      (tail_ (nvar_ s))
      (concat_ (nvar_ acc) (seq_ [app_ (nvar_ f) (head_ (nvar_ s))])))
  , replacement = lam info. lam args.
      let f = _optionGetExn (mapLookup f args) info in
      let as = _optionGetExn (mapLookup s args) info in
      TmParallelMap {f = f, as = as, ty = TyUnknown {info = info},
                     info = info}}
let reducePattern = use MExprParallelKeywordMaker in
  lam.
  let reduce = nameSym "reduce" in
  let s = nameSym "s" in
  let acc = nameSym "acc" in
  let f = nameSym "f" in
  { ident = reduce
  , expr = if_ (null_ (nvar_ s))
      (nvar_ acc)
      (appf3_ (nvar_ reduce)
        (tail_ (nvar_ s))
        (appf2_ (nvar_ f) (nvar_ acc) (head_ (nvar_ s)))
        (nvar_ f))
  , replacement = lam info. lam args.
      let f = _optionGetExn (mapLookup f args) info in
      let ne = _optionGetExn (mapLookup acc args) info in
      let as = _optionGetExn (mapLookup s args) info in
      TmParallelReduce {f = f, ne = ne, as = as, ty = TyUnknown {info = info},
                        info = info}}

let variableFromTriple = use MExprAst in
  lam triple : (Name, Type, Info).
  TmVar {ident = triple.0, ty = triple.1, info = triple.2}

let patterns = ref []
let genPatterns = lam. [mapPattern (), reducePattern ()]
let getPatterns = lam.
  let pats = deref patterns in
  if null pats then
    let pats = genPatterns () in
    modref patterns pats; pats
  else pats

-- Attempts to match the body of the given binding with the given arguments
-- with a parallel pattern. If they match the pattern replacement is updated to
-- use the corresponding variables of the given body and returned. If they do
-- not match None () is returned.
let matchPattern : RecLetBinding -> Expr -> [(Name, Type, Info)]
                -> ParallelPattern -> Option Expr =
  use MExprParallelKeywordMaker in
  lam binding. lam bindingBody. lam bindingArgs. lam pattern.
  let empty = {varEnv = biEmpty, conEnv = biEmpty} in
  match eqExprH empty empty pattern.expr bindingBody with Some freeVarEnv then
    let freeVarEnv : EqEnv = freeVarEnv in
    let paramNameMap = mapFromSeq nameCmp freeVarEnv.varEnv in
    let paramVarMap =
      mapMap
        (lam v. (lam info. TmVar {ident = v, ty = TyUnknown {info = info},
                                  info = info}))
        paramNameMap in
    let replacement = pattern.replacement binding.info paramVarMap in
    match mapLookup pattern.ident paramNameMap with Some id then
      if nameEq id binding.ident then
        Some (substituteVariables replacement paramVarMap)
      else None ()
    else None()
  else None ()

let tryRewriteBinding = use MExprAst in
  lam binding : RecLetBinding.
  match functionParametersAndBody binding.body with (args, body) then
    let n = length (getPatterns ()) in
    recursive let tryMatchPattern = lam i.
      if lti i n then
        let pattern = get (getPatterns ()) i in
        match matchPattern binding body args pattern with Some replacement then
          Some ({binding with body = replaceFunctionBody binding.body replacement})
        else
          tryMatchPattern (addi i 1)
      else None ()
    in
    match tryMatchPattern 0 with Some rewrittenBinding then
      rewrittenBinding
    else binding
  else never

lang MExprParallelPatterns = MExprAst
  sem insertParallelPatterns =
  | TmRecLets t ->
    TmRecLets {t with bindings = map tryRewriteBinding t.bindings}
  | expr -> smap_Expr_Expr insertParallelPatterns expr
end

lang TestLang =
  MExprParallelPatterns + MExprRewrite + MExprParallelKeywordMaker +
  MExprTailRecursion

mexpr

use TestLang in

let fold = nameSym "fold" in
let f = nameSym "f" in
let s = nameSym "s" in
let acc = nameSym "acc" in
let h = nameSym "h" in
let t = nameSym "t" in
let t1 = nreclets_ [
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
] in
let t2 = nreclets_ [
  (fold, tyunknown_, nulam_ f (nulam_ acc (nulam_ s (
    parallelReduce_ (nvar_ f) (nvar_ acc) (nvar_ s)))))
] in

utest insertParallelPatterns (rewriteTerm t1) with t2 using eqExpr in
utest insertParallelPatterns t2 with t2 using eqExpr in

let map = nameSym "map" in
let mapTr = nameSym "map_tr" in
let t1 = nreclets_ [
  (map, tyunknown_, nulam_ f (nulam_ s (
    match_ (nvar_ s)
      (pseqtot_ [])
      (seq_ [])
      (match_ (nvar_ s)
        (pseqedgen_ [npvar_ h] t [])
        (cons_ (head_ (nvar_ s)) (appf2_ (nvar_ map) (nvar_ f) (tail_ (nvar_ s))))
        never_))))
] in
let t2 = nreclets_ [
  (mapTr, tyunknown_, nulam_ f (nulam_ s (nulam_ acc (
    parallelMap_ (nvar_ f) (nvar_ s))))),
  (map, tyunknown_, nulam_ f (nulam_ s (
    appf3_ (nvar_ mapTr) (nvar_ f) (nvar_ s) (seq_ []))))
] in
utest insertParallelPatterns (tailRecursive (rewriteTerm t1)) with t2 using eqExpr in
utest insertParallelPatterns t2 with t2 using eqExpr in

()
