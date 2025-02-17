include "mexpr/ast.mc"
include "pmexpr/ast.mc"
include "pmexpr/function-properties.mc"
include "pmexpr/utils.mc"

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
    join ["PatternName (", nameGetStr n, ", ", symStr, ")"]
  else match pat with PatternLiteralInt n then
    concat "PatternLiteralInt " (int2string n)
  else never

type AtomicPattern
con AppPattern : use Ast in {id : Int, fn : Expr, vars : [VarPattern]} -> AtomicPattern
con UnknownOpPattern : {id : Int, vars : [VarPattern]} -> AtomicPattern
con BranchPattern : {id : Int, cond : VarPattern, thn : [AtomicPattern],
                        els : [AtomicPattern]} -> AtomicPattern
con RecursionPattern : {id : Int, binds : [(Name, VarPattern)]} -> AtomicPattern
con ReturnPattern : {id : Int, var : VarPattern} -> AtomicPattern

type Pattern = use Ast in {
  atomicPatternMap : Map Int AtomicPattern,
  activePatterns : [Int],
  dependencies : Map Int (Set Int),
  replacement : Info -> Map VarPattern (Name, Expr) -> Expr
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
let getPatternDependencies : [AtomicPattern] -> ([Int], Map Int (Set Int)) =
  lam atomicPatterns.
  recursive let atomicPatternDependencies =
    lam dependencies : Map Int (Set Int). lam p : AtomicPattern.
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
let withDependencies : use Ast in
     {atomicPatterns : [AtomicPattern],
      replacement : Info -> Map VarPattern (Name, Expr) -> Expr} -> Pattern = lam pat.
  recursive let work = lam acc. lam pat.
    let idx = getPatternIndex pat in
    let acc = cons (idx, pat) acc in
    match getInnerPatterns pat with Some pats then
      foldl work acc pats
    else acc
  in
  match getPatternDependencies pat.atomicPatterns with (activePatterns, dependencies) in
  let nestedPatterns = foldl work [] pat.atomicPatterns in
  let patMap = mapFromSeq subi nestedPatterns in
  { atomicPatternMap = patMap
  , activePatterns = activePatterns
  , dependencies = dependencies
  , replacement = pat.replacement }

let getMatch : use Ast in String -> VarPattern -> Map VarPattern (Name, Expr)
            -> (Name, Expr) =
  lam parallelPattern. lam varPat. lam matches.
  match mapLookup varPat matches with Some (id, expr) then
    (id, expr)
  else
    error (join [
      "Pattern replacement function for ", parallelPattern,
      " referenced unmatched variable pattern ", varPatString varPat])

let eliminateUnusedLetExpressions : use Ast in Expr -> Expr =
  use PMExprAst in
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
      match work acc t.inexpr with (acc, inexpr) in
      if setMem t.ident acc then
        let acc = collectVariables acc t.body in
        (acc, TmLet {t with inexpr = inexpr})
      else (acc, inexpr)
    else smapAccumL_Expr_Expr work acc expr
  in
  match work (setEmpty nameCmp) e with (_, e) in
  e

-- Definition of the map pattern
let mapPatRef : Ref (Option Pattern) = ref (None ())
let mapPattern : () -> Pattern =
  use PMExprVariableSub in
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
  let replacement : Info -> (Map VarPattern (Name, Expr)) -> Expr =
    lam info. lam matches.
    let patternName = "parallelMap" in
    match getMatch patternName (PatternIndex 1) matches with (_, branchExpr) in
    match getMatch patternName (PatternIndex 5) matches with (fId, fExpr) in
    match getMatch patternName (PatternIndex 4) matches with (headId, headExpr) in
    match getMatch patternName (PatternName s) matches with (_, sExpr) in
    match branchExpr with TmMatch {els = els} then
      match fExpr with TmSeq {tms = [fResultVar]} then
        let x = nameSym "x" in
        let subMap = mapFromSeq nameCmp [
          (headId, lam info.
            TmVar {ident = x, ty = tyWithInfo info (tyTm headExpr),
                   info = info, frozen = false})
        ] in
        let els = substituteVariables subMap els in
        let els = eliminateUnusedLetExpressions (bind_ els fResultVar) in
        let fType = TyArrow {
          from = tyTm headExpr, to = tyTm els, info = infoTm els} in
        let innerAppType = TyArrow {
          from = TySeq {ty = tyTm headExpr, info = info},
          to = TySeq {ty = tyTm els, info = info},
          info = info} in
        let mapTy = TyArrow {
          from = fType,
          to = innerAppType,
          info = info} in
        TmApp {
          lhs = TmApp {
            lhs = TmConst {val = CMap (), ty = mapTy, info = info},
            rhs = TmLam {
              ident = x, tyAnnot = tyTm headExpr, tyParam = tyTm headExpr, body = els,
              ty = fType, info = infoTm els},
            ty = innerAppType, info = info},
          rhs = sExpr,
          ty = TySeq {ty = tyTm els, info = info}, info = info}
      else
        error (join [
          "Rewriting into parallelMap pattern failed: The functional expression ",
          "did not result in a singleton sequence"])
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
  use PMExprVariableSub in
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
  let replacement : Info -> (Map VarPattern (Name, Expr)) -> Expr =
    lam info. lam matches.
    let patternName = "parallelMap2" in
    match getMatch patternName (PatternIndex 4) matches with (_, branchExpr) in
    match getMatch patternName (PatternIndex 10) matches with (_, fExpr) in
    match getMatch patternName (PatternIndex 8) matches with (headFstId, headFstExpr) in
    match getMatch patternName (PatternIndex 9) matches with (headSndId, headSndExpr) in
    match getMatch patternName (PatternName s1) matches with (_, sFstExpr) in
    match getMatch patternName (PatternName s2) matches with (_, sSndExpr) in
    match branchExpr with TmMatch {els = els} then
      match fExpr with TmSeq {tms = [fResultVar]} then
        let x = nameSym "x" in
        let y = nameSym "y" in
        let subMap = mapFromSeq nameCmp [
          (headFstId, lam info.
            TmVar {ident = x, ty = tyWithInfo info (tyTm headFstExpr),
                   info = info, frozen = false}),
          (headSndId, lam info.
            TmVar {ident = y, ty = tyWithInfo info (tyTm headSndExpr),
                   info = info, frozen = false})
        ] in
        let els = substituteVariables subMap els in
        let els = eliminateUnusedLetExpressions (bind_ els fResultVar) in
        TmMap2 {
          f = TmLam {
            ident = x, tyAnnot = tyTm headFstExpr, tyParam = tyTm headFstExpr,
            body = TmLam {
              ident = y, tyAnnot = tyTm headSndExpr, tyParam = tyTm headSndExpr, body = els,
              ty = TyArrow {from = tyTm headSndExpr, to = tyTm els, info = info},
              info = infoTm els},
            ty = TyArrow {
              from = tyTm headFstExpr,
              to = TyArrow {from = tyTm headSndExpr, to = tyTm els, info = info},
              info = info},
            info = info},
          as = sFstExpr,
          bs = sSndExpr,
          ty = TySeq {ty = tyTm els, info = info},
          info = info}
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

-- Definition of the fold pattern
let reducePatRef : Ref (Option Pattern) = ref (None ())
let reducePattern : () -> Pattern =
  use PMExprVariableSub in
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
  let replacement : Info -> Map VarPattern (Name, Expr) -> Expr =
    lam info. lam matches.
    let getReduceFunctionTypes = lam f.
      let errMsg = join [
        "Rewriting info fold pattern failed: invalid type of function argument\n",
        "Expected type of shape A -> (B -> C), got ",
        use MExprPrettyPrint in type2str (tyTm f)] in
      match tyTm f with TyArrow {from = tya, to = TyArrow {from = tyb, to = tyc}} then
        if eqType tya tyc then
          (tya, tyb)
        else errorSingle [info] errMsg
      else errorSingle [info] errMsg
    in
    let seqReduce = lam f. lam acc. lam s.
      match getReduceFunctionTypes f with (accType, seqElemType) in
      let seqAppType = TyArrow {
        from = TySeq {ty = seqElemType, info = info},
        to = accType, info = infoTy accType} in
      let foldlAppType = TyArrow {from = accType, to = seqAppType, info = info} in
      let foldlType = TyArrow {from = tyTm f, to = foldlAppType, info = info} in
      TmApp {
        lhs = TmApp {
          lhs = TmApp {
            lhs = TmConst {val = CFoldl (), ty = foldlType, info = info},
            rhs = f,
            ty = foldlAppType,
            info = info},
          rhs = acc,
          ty = seqAppType,
          info = info},
        rhs = s,
        ty = accType,
        info = info} in
    let patternName = "fold" in
    match getMatch patternName (PatternIndex 1) matches with (_, branchExpr) in
    match getMatch patternName (PatternIndex 4) matches with (headId, headExpr) in
    match getMatch patternName (PatternIndex 5) matches with (fResultId, fResultExpr) in
    match getMatch patternName (PatternName acc) matches with (accId, accExpr) in
    match getMatch patternName (PatternName s) matches with (_, sExpr) in
    match branchExpr with TmMatch {els = els} then
      let x = nameSym "x" in
      let y = nameSym "y" in
      let subMap = mapFromSeq nameCmp [
        (accId, lam info.
          TmVar {ident = x, ty = tyWithInfo info (tyTm accExpr), info = info,
                 frozen = false}),
        (headId, lam info.
          TmVar {ident = y, ty = tyWithInfo info (tyTm headExpr), info = info,
                 frozen = false})
      ] in
      let els = substituteVariables subMap els in
      let fResultVar = TmVar {ident = fResultId, ty = tyTm fResultExpr,
                              info = infoTm fResultExpr, frozen = false} in
      let els = eliminateUnusedLetExpressions (bind_ els fResultVar) in
      let elemTy = tyTm headExpr in
      let accTy = tyTm accExpr in
      let f = TmLam {
        ident = x, tyAnnot = accTy, tyParam = accTy,
        body = TmLam {
          ident = y, tyAnnot = elemTy, tyParam = elemTy, body = els,
          ty = TyArrow {from = elemTy, to = accTy,
                        info = infoTm els},
          info = info},
        ty = TyArrow {
          from = accTy,
          to = TyArrow {from = elemTy, to = accTy, info = info},
          info = info},
        info = info} in
      seqReduce f accExpr sExpr
    else
      error (join [
        "Rewriting into fold pattern failed: BranchPattern matched ",
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
