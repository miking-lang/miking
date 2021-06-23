include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"

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

type AtomicPattern
con FixedAppPattern : {id : Int, fn : Expr, vars : [VarPattern]} -> AtomicPattern
con UnknownAppPattern : {id : Int, vars : [VarPattern]} -> AtomicPattern
con BranchPattern : {id : Int, cond : VarPattern, thn : [AtomicPattern],
                        els : [AtomicPattern]} -> AtomicPattern
con SeqPattern : {id : Int, vars : [VarPattern]} -> AtomicPattern
con RecursionPattern : {id : Int, binds : [(Name, Int)]} -> AtomicPattern
con ReturnPattern : {id : Int, var : VarPattern} -> AtomicPattern

type Pattern = {
  atomicPatternMap : Map Int AtomicPattern,
  activePatterns : [AtomicPattern],
  dependencies : Map Int (Set Int),
  replacement : (Map VarPattern (Name, Expr)) -> Expr
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

let getPatternIndex : AtomicPattern -> Int = lam p.
  match p with FixedAppPattern t then t.id
  else match p with UnknownAppPattern t then t.id
  else match p with BranchPattern t then t.id
  else match p with SeqPattern t then t.id
  else match p with RecursionPattern t then t.id
  else match p with ReturnPattern t then t.id
  else never

let getShallowPatternDependencies : AtomicPattern -> [VarPattern] = lam p.
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

let getInnerPatterns : AtomicPattern -> Option [AtomicPattern] = lam p.
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
let getPatternDependencies : [AtomicPattern] -> Map Int (Set Int) =
  lam atomicPatterns.
  recursive let atomicPatternDependencies = lam dependencies. lam p.
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
     {atomicPatterns : [AtomicPattern],
      replacement : (Map VarPattern (Name, Expr)) -> Expr} -> Pattern = lam pat.
  recursive let work = lam acc. lam pat.
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

-- Definition of the 'parallelMap' pattern
let mapPatRef : Option Pattern = ref (None ())
let mapPattern : () -> Pattern =
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
  let replacement : (Map VarPattern (Name, Expr)) -> Expr = lam matches.
    match mapLookup (PatternIndex 5) matches with Some (_, fExpr) then
      match mapLookup (PatternIndex 4) matches with Some (headName, headExpr) then
        let x = nameSym "x" in
        let subMap = mapFromSeq nameCmp [
          (headName, lam info.
            TmVar {ident = x, ty = tyWithInfo info (ty headExpr), 
                   info = info})
        ] in
        let f = nulam_ x (substituteVariables fExpr subMap) in
        match mapLookup (PatternName s) matches with Some (_, sExpr) then
          parallelMap_ f sExpr
        else never
      else never
    else never
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let getMapPattern = lam.
  match deref mapPatRef with Some pat then
    pat
  else
    let pat = mapPattern () in
    modref mapPatRef (Some pat);
    pat

-- Definition of the 'parallelReduce' pattern
let reducePatRef : Option Pattern = ref (None ())
let reducePattern : () -> Pattern =
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
  let replacement : Map VarPattern (Name, Expr) -> Expr = lam matches.
    match mapLookup (PatternIndex 5) matches with Some (_, fExpr) then
      match mapLookup (PatternName acc) matches with Some (accName, accExpr) then
        match mapLookup (PatternIndex 4) matches with Some (headName, headExpr) then
          let x = nameSym "x" in
          let y = nameSym "y" in
          let subMap = mapFromSeq nameCmp [
            (accName, lam info.
              TmVar {ident = x, ty = tyWithInfo info (ty accExpr),
                     info = info}),
            (headName, lam info.
              TmVar {ident = y, ty = tyWithInfo info (ty headExpr),
                     info = info})
          ] in
          let f = nulam_ x (nulam_ y (substituteVariables fExpr subMap)) in
          match mapLookup (PatternName s) matches with Some(_, sExpr) then
            parallelReduce_ f accExpr sExpr
          else never
        else never
      else never
    else never
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let getReducePattern = lam.
  match deref reducePatRef with Some pat then
    pat
  else
    let pat = reducePattern () in
    modref reducePatRef (Some pat);
    pat
