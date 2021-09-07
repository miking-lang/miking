include "mexpr/ast.mc"
include "mexpr/rewrite/function-properties.mc"
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

-- Definition of the map pattern
-- This pattern can be matched both by 'parallelMap' uses, but also by
-- 'flatMap' uses. They are distinguished by looking at the final result, which
-- is a singleton sequence in the 'parallelMap' case.
let mapPatRef : Ref (Option Pattern) = ref (None ())
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
        RecursionPattern {id = 7, binds = [(s, PatternIndex 3),
                                           (acc, PatternIndex 6)]},
        ReturnPattern {id = 8, var = PatternIndex 7}
      ]},
    ReturnPattern {id = 9, var = PatternIndex 1}
  ] in
  let replacement : (Map VarPattern (Name, Expr)) -> Expr = lam matches.
    let patternName = "parallelMap" in
    let branchExpr = getMatchExpr patternName (PatternIndex 1) matches in
    let fPair : (Name, Expr) = getMatch patternName (PatternIndex 5) matches in
    let headPair : (Name, Expr) = getMatch patternName (PatternIndex 4) matches in
    let sExpr = getMatchExpr patternName (PatternName s) matches in

    match branchExpr with TmMatch {els = els} then
      let x = nameSym "x" in
      let subMap = mapFromSeq nameCmp [
        (headPair.0, lam info.
          TmVar {ident = x, ty = tyWithInfo info (ty headPair.1), info = info})
      ] in
      let els = substituteVariables els subMap in
      match fPair.1 with TmSeq {tms = [fResultVar]} then
        let els = eliminateUnusedLetExpressions (bind_ els fResultVar) in
        parallelMap_ (nulam_ x els) sExpr
      else
        let els = eliminateUnusedLetExpressions (bind_ els (nvar_ fPair.0)) in
        parallelFlatMap_ (nulam_ x els) sExpr
    else
      error (join [
        "Rewriting into parallelMap pattern failed: BranchPattern matched ",
        "with non-branch expression"])
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let getMapPattern = lam.
  match deref mapPatRef with Some pat then
    pat
  else
    let pat = mapPattern () in
    modref mapPatRef (Some pat);
    pat

-- Definition of the 'parallelMap2' pattern
let map2PatRef : Ref (Option Pattern) = ref (None ())
let map2Pattern : () -> Pattern =
  use MExprParallelKeywordMaker in
  lam.
  let s1 = nameSym "s1" in
  let s2 = nameSym "s2" in
  let acc = nameSym "acc" in
  let atomicPatterns = [
    AppPattern {id = 0, fn = uconst_ (CNull ()), vars = [PatternName s1]},
    BranchPattern {id = 1, cond = PatternIndex 0,
      thn = [ReturnPattern {id = 2, var = PatternName acc}],
      els = [
        AppPattern {id = 3, fn = uconst_ (CNull ()), vars = [PatternName s2]},
        BranchPattern {id = 4, cond = PatternIndex 3,
          thn = [ReturnPattern {id = 5, var = PatternName acc}],
          els = [
            AppPattern {id = 6, fn = uconst_ (CTail ()), vars = [PatternName s1]},
            AppPattern {id = 7, fn = uconst_ (CTail ()), vars = [PatternName s2]},
            AppPattern {id = 8, fn = uconst_ (CHead ()), vars = [PatternName s1]},
            AppPattern {id = 9, fn = uconst_ (CHead ()), vars = [PatternName s2]},
            UnknownOpPattern {id = 10, vars = [PatternIndex 8, PatternIndex 9]},
            AppPattern {id = 11, fn = uconst_ (CConcat ()),
                        vars = [PatternName acc, PatternIndex 10]},
            RecursionPattern {id = 12, binds = [(s1, PatternIndex 6),
                                                (s2, PatternIndex 7),
                                                (acc, PatternIndex 11)]},
            ReturnPattern {id = 13, var = PatternIndex 12}
          ]},
        ReturnPattern {id = 14, var = PatternIndex 4}]},
    ReturnPattern {id = 15, var = PatternIndex 1}
  ] in
  let replacement : (Map VarPattern (Name, Expr)) -> Expr = lam matches.
    let patternName = "parallelMap2" in
    let branchExpr = getMatchExpr patternName (PatternIndex 4) matches in
    let fExpr = getMatchExpr patternName (PatternIndex 10) matches in
    let headFst : (Name, Expr) = getMatch patternName (PatternIndex 8) matches in
    let headSnd : (Name, Expr) = getMatch patternName (PatternIndex 9) matches in
    let sFstExpr = getMatchExpr patternName (PatternName s1) matches in
    let sSndExpr = getMatchExpr patternName (PatternName s2) matches in

    match branchExpr with TmMatch {els = els} then
      match fExpr with TmSeq {tms = [fResultVar]} then
        let x = nameSym "x" in
        let y = nameSym "y" in
        let subMap = mapFromSeq nameCmp [
          (headFst.0, lam info.
            TmVar {ident = x, ty = tyWithInfo info (ty headFst.1), info = info}),
          (headSnd.0, lam info.
            TmVar {ident = y, ty = tyWithInfo info (ty headSnd.1), info = info})
        ] in
        let els = substituteVariables els subMap in
        let els = eliminateUnusedLetExpressions (bind_ els fResultVar) in
        parallelMap2_ (nulam_ x (nulam_ y els)) sFstExpr sSndExpr
      else
        error (join [
          "Rewriting into parallelMap2 pattern failed: The functional ",
          "expression did not result in a singleton sequence"])
    else
      error (join [
        "Rewriting into parallelMap2 pattern failed: Inner BranchPattern ",
        "matched with non-branch expression"])
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let getMap2Pattern = lam.
  match deref map2PatRef with Some pat then
    pat
  else
    let pat = map2Pattern () in
    modref map2PatRef (Some pat);
    pat

-- Definition of the 'parallelReduce'/'foldLeft' pattern
let reducePatRef : Ref (Option Pattern) = ref (None ())
let reducePattern : () -> Pattern =
  use PMExprFunctionProperties in
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
    let seqReduce = lam f. lam acc. lam s.
      TmApp {
        lhs = TmApp {
          lhs = TmApp {
            lhs = TmConst {val = CFoldl (), ty = tyunknown_, info = NoInfo ()},
            rhs = f,
            ty = tyunknown_,
            info = NoInfo ()
          },
          rhs = acc,
          ty = tyunknown_,
          info = NoInfo ()
        },
        rhs = s,
        ty = tyunknown_,
        info = NoInfo ()} in
    let patternName = "parallelReduce" in
    let branchExpr = getMatchExpr patternName (PatternIndex 1) matches in
    let fResultPair : (Name, Expr) = getMatch patternName (PatternIndex 5) matches in
    let accPair : (Name, Expr) = getMatch patternName (PatternName acc) matches in
    let headPair : (Name, Expr) = getMatch patternName (PatternIndex 4) matches in
    let sExpr = getMatchExpr patternName (PatternName s) matches in

    match branchExpr with TmMatch {els = els} then
      let x = nameSym "x" in
      let y = nameSym "y" in
      let subMap = mapFromSeq nameCmp [
        (accPair.0, lam info.
          TmVar {ident = x, ty = tyWithInfo info (ty accPair.1), info = info}),
        (headPair.0, lam info.
          TmVar {ident = y, ty = tyWithInfo info (ty headPair.1), info = info})
      ] in
      let els = substituteVariables els subMap in
      let els = eliminateUnusedLetExpressions (bind_ els (nvar_ fResultPair.0)) in
      let f = nulam_ x (nulam_ y els) in
      seqReduce f accPair.1 sExpr
    else
      error (join [
        "Rewriting into parallelReduce pattern failed: BranchPattern matched ",
        "with non-branch expression"])
  in
  withDependencies {atomicPatterns = atomicPatterns, replacement = replacement}

let getReducePattern = lam.
  match deref reducePatRef with Some pat then
    pat
  else
    let pat = reducePattern () in
    modref reducePatRef (Some pat);
    pat
