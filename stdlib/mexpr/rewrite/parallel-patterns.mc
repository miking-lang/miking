include "mexpr/patterns.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/tailrecursion.mc"
include "mexpr/rewrite/utils.mc"

type ParallelPattern = {
  ident : Name,
  expr : Expr,
  replacement : [Expr] -> Expr
}

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
      (concat_ (nvar_ acc) (seq_ [head_ (nvar_ s)])))
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
