include "mexpr/ast.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"

type VarPattern
con PatternIndex : Int -> VarPattern
con PatternName : Name -> VarPattern
con PatternLiteralInt : Int -> VarPattern

let varPatternIndex : VarPattern -> Int = lam p.
  match p with PatternIndex _ then 0
  else match p with PatternName _ then 1
  else match p with PatternLiteralInt _ then 2
  else never

let cmpVarPattern : VarPattern -> VarPattern -> Int = lam p1. lam p2.
  let diff = subi (varPatternIndex p1) (varPatternIndex p2) in
  if eqi diff 0 then
    let p = (p1, p2) in
    match p with (PatternIndex i1, PatternIndex i2) then
      subi i1 i2
    else match p with (PatternName n1, PatternName n2) then
      nameCmp n1 n2
    else match p with (PatternLiteralInt i1, PatternLiteralInt i2) then
      subi i1 i2
    else never
  else diff

let varPatString : VarPattern -> String = lam pat.
  match pat with PatternIndex i then
    concat "PatternIndex " (int2string i)
  else match pat with PatternName n then
    let symStr =
      match nameGetSym n with Some sym then
        int2string (sym2hash sym)
      else "?"
    in
    join ["PatternName (", nameGetStr n, ", " symStr, ")"]
  else match pat with PatternLiteralInt n then
    concat "PatternLiteralInt " (int2string n)
  else never

type AtomicPattern
con AppPattern : {id : Int, fn : Expr, vars : [VarPattern]} -> AtomicPattern
con UnknownOpPattern : {id : Int, vars : [VarPattern]} -> AtomicPattern
con BranchPattern : {id : Int, cond : VarPattern, thn : [AtomicPattern],
                        els : [AtomicPattern]} -> AtomicPattern
con RecursionPattern : {id : Int, binds : [(Name, VarPattern)]} -> AtomicPattern
con ReturnPattern : {id : Int, var : VarPattern} -> AtomicPattern

type Pattern = {
  atomicPatternMap : Map Int AtomicPattern,
  activePatterns : [AtomicPattern],
  dependencies : Map Int (Set Int),
  replacement : Map VarPattern (Name, Expr) -> Expr
}

let getPatternIndex : AtomicPattern -> Int = lam p.
  match p with AppPattern t then t.id
  else match p with UnknownOpPattern t then t.id
  else match p with BranchPattern t then t.id
  else match p with RecursionPattern t then t.id
  else match p with ReturnPattern t then t.id
  else never

let getShallowVarPatternDependencies : AtomicPattern -> [VarPattern] = lam p.
  match p with AppPattern t then t.vars
  else match p with UnknownOpPattern t then t.vars
  else match p with BranchPattern t then [t.cond]
  else match p with RecursionPattern t then
    match unzip t.binds with (names, vars) then
      join [map (lam n. PatternName n) names, vars]
    else never
  else match p with ReturnPattern t then [t.var]
  else never

let getInnerPatterns : AtomicPattern -> Option [AtomicPattern] = lam p.
  match p with AppPattern _ then None ()
  else match p with UnknownOpPattern _ then None ()
  else match p with BranchPattern t then Some (concat t.thn t.els)
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
          (getShallowVarPatternDependencies p) in
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

let getMatch : String -> VarPattern -> Map VarPattern (Name, Expr)
            -> (Name, Expr) =
  lam parallelPattern. lam varPat. lam matches.
  match mapLookup varPat matches with Some (id, expr) then
    (id, expr)
  else
    error (join [
      "Pattern replacement function for ", parallelPattern,
      " referenced unmatched variable pattern ", varPatString varPat])

let getMatchName 
  : String -> VarPattern -> Map VarPattern (Name, Expr) -> Name =
  lam parallelPattern. lam varPat. lam matches.
  match getMatch parallelPattern varPat matches with (id, _) then
    id
  else never

let getMatchExpr
  : String -> VarPattern -> Map VarPattern (Name, Expr) -> Expr =
  lam parallelPattern. lam varPat. lam matches.
  match getMatch parallelPattern varPat matches with (_, expr) then
    expr
  else never

-- Definition of the 'parallelMap' pattern
let mapPatRef : Option Pattern = ref (None ())
let mapPattern : () -> Pattern =
  use MExprParallelKeywordMaker in
  lam.
  let s = nameSym "s" in
  let acc = nameSym "acc" in
  let atomicPatterns = [
    AppPattern {id = 0, fn = uconst_ (CNull ()), vars = [PatternName s]},
    BranchPattern {id = 1, cond = PatternIndex 0,
      thn = [ReturnPattern {id = 2, var = PatternName acc}],
      els = [
        AppPattern {id = 3, fn = uconst_ (CTail ()), vars = [PatternName s]},
        AppPattern {id = 4, fn = uconst_ (CHead ()), vars = [PatternName s]},
        UnknownOpPattern {id = 5, vars = [PatternIndex 4]},
        AppPattern {id = 6, fn = uconst_ (CConcat ()),
                       vars = [PatternName acc, PatternIndex 5]},
        RecursionPattern {id = 7, binds = [(s, PatternIndex 3), (acc, PatternIndex 6)]},
        ReturnPattern {id = 8, var = PatternIndex 7}
      ]},
    ReturnPattern {id = 9, var = PatternIndex 1}
  ] in
  let replacement : (Map VarPattern (Name, Expr)) -> Expr = lam matches.
    let patternName = "parallelMap" in
    let fExpr = getMatchExpr patternName (PatternIndex 5) matches in
    let headPair : (Name, Expr) = getMatch patternName (PatternIndex 4) matches in
    let sExpr = getMatchExpr patternName (PatternName s) matches in

    let x = nameSym "x" in
    let subMap = mapFromSeq nameCmp [
      (headPair.0, lam info.
        TmVar {ident = x, ty = tyWithInfo info (ty headPair.1), info = info})
    ] in
    let f = nulam_ x (substituteVariables fExpr subMap) in
    parallelMap_ f sExpr
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
    AppPattern {id = 0, fn = uconst_ (CNull ()), vars = [PatternName s]},
    BranchPattern {id = 1, cond = PatternIndex 0,
      thn = [ReturnPattern {id = 2, var = PatternName acc}],
      els = [
        AppPattern {id = 3, fn = uconst_ (CTail ()), vars = [PatternName s]},
        AppPattern {id = 4, fn = uconst_ (CHead ()), vars = [PatternName s]},
        UnknownOpPattern {id = 5, vars = [PatternName acc, PatternIndex 4]},
        RecursionPattern {id = 6, binds = [(s, PatternIndex 3), (acc, PatternIndex 5)]},
        ReturnPattern {id = 7, var = PatternIndex 6}
      ]},
    ReturnPattern {id = 8, var = PatternIndex 1}
  ] in
  let replacement : Map VarPattern (Name, Expr) -> Expr = lam matches.
    let patternName = "parallelReduce" in
    let fExpr = getMatchExpr patternName (PatternIndex 5) matches in
    let accPair : (Name, Expr) = getMatch patternName (PatternName acc) matches in
    let headPair : (Name, Expr) = getMatch patternName (PatternIndex 4) matches in
    let sExpr = getMatchExpr patternName (PatternName s) matches in

    let x = nameSym "x" in
    let y = nameSym "y" in
    let subMap = mapFromSeq nameCmp [
      (accPair.0, lam info.
        TmVar {ident = x, ty = tyWithInfo info (ty accPair.1), info = info}),
      (headPair.0, lam info.
        TmVar {ident = y, ty = tyWithInfo info (ty headPair.1), info = info})
    ] in
    let f = nulam_ x (nulam_ y (substituteVariables fExpr subMap)) in
    parallelReduce_ f accPair.1 sExpr
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let getReducePattern = lam.
  match deref reducePatRef with Some pat then
    pat
  else
    let pat = reducePattern () in
    modref reducePatRef (Some pat);
    pat

-- Definition of the 'for' pattern
let eliminateUnusedLetExpressions : Expr -> Expr =
  use MExprParallelKeywordMaker in
  lam e.
  recursive let collectVariables = lam acc. lam expr.
    match expr with TmVar {ident = ident} then
      setInsert ident acc
    else sfold_Expr_Expr collectVariables acc expr
  in
  recursive let work = lam acc. lam expr.
    match expr with TmVar {ident = ident} then
      (setInsert ident acc, expr)
    else match expr with TmLet t then
      match work acc t.inexpr with (acc, inexpr) then
        if setMem t.ident acc then
          let acc = collectVariables acc t.body in
          (acc, TmLet {t with inexpr = inexpr})
        else
          (acc, inexpr)
      else never
    else smapAccumL_Expr_Expr work acc expr
  in
  match work (setEmpty nameCmp) e with (_, e) then
    e
  else never

let forPatRef = ref (None ())
let forPattern = use MExprAst in
  lam.
  let i = nameSym "i" in
  let n = nameSym "n" in
  let acc = nameSym "acc" in
  let atomicPatterns = [
    AppPattern {id = 0, fn = uconst_ (CLti ()),
                     vars = [PatternName i, PatternName n]},
    BranchPattern {id = 1, cond = PatternIndex 0,
      thn = [
        UnknownOpPattern {id = 2, vars = [PatternName acc, PatternName i]},
        AppPattern {id = 3, fn = uconst_ (CAddi ()),
                         vars = [PatternName i, PatternLiteralInt 1]},
        RecursionPattern {id = 4, binds = [(acc, PatternIndex 2),
                                           (i, PatternIndex 3),
                                           (n, PatternName n)]},
        ReturnPattern {id = 5, var = PatternIndex 4}
      ],
      els = [ReturnPattern {id = 6, var = PatternName acc}]},
    ReturnPattern {id = 7, var = PatternIndex 1}
  ] in
  let replacement : Map VarPattern (Name, Expr) -> Expr = lam matches.
    let patternName = "sequentialFor" in
    let accResultName = getMatchName patternName (PatternIndex 2) matches in
    let nParamExpr = getMatchExpr patternName (PatternName n) matches in
    let branchExpr = getMatchExpr patternName (PatternIndex 1) matches in
    let accPair : (Name, Expr) = getMatch patternName (PatternName acc) matches in
    let iterPair : (Name, Expr) = getMatch patternName (PatternName i) matches in

    match branchExpr with TmMatch {thn = thn} then
      -- Replace i with fresh variable to avoid it being replaced by a passed
      -- argument.
      let accFresh = nameSym (nameGetStr accPair.0) in
      let iFresh = nameSym (nameGetStr iterPair.0) in
      let subMap = mapFromSeq nameCmp [
        (iterPair.0, lam info.
          TmVar {ident = iFresh, ty = tyWithInfo info (ty iterPair.1),
                 info = info})
      ] in
      let thn = substituteVariables thn subMap in

      -- Eliminate let-expressions that are not needed in the new form of the
      -- for-loop. This includes at least the recursive call (the for-loop is
      -- not recursive) and the increment of the iteration value because it is
      -- implicitly handled by the for-loop.
      let thn = bind_ thn (nvar_ accResultName) in
      let thn = eliminateUnusedLetExpressions thn in

      sequentialFor_
        (nulam_ iFresh thn)
        accPair.1 nParamExpr
    else
      error (join [
        "Rewriting into sequential for pattern failed: BranchPattern matched ",
        "with non-branch expression"])
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let getForPattern = lam.
  match deref forPatRef with Some pat then
    pat
  else
    let pat = forPattern () in
    modref forPatRef (Some pat);
    pat
