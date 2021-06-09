include "mexpr/patterns.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/utils.mc"

type ParallelPattern = {
  ident : Name,
  expr : Expr,
  replacement : [Expr] -> Expr
}

let reduceName = nameSym "reduce"
let s = nameSym "s"
let acc = nameSym "acc"
let f = nameSym "f"
let reducePattern = lam.
  if_ (null_ (nvar_ s))
    (nvar_ acc)
    (appf3_ (nvar_ reduceName)
      (tail_ (nvar_ s))
      (appf2_ (nvar_ f) (nvar_ acc) (head_ (nvar_ s)))
      (nvar_ f))
let patterns = use MExprParallelKeywordMaker in
  [{ident = reduceName, expr = reducePattern (),
    replacement = lam info. lam args.
      let a = map (lam arg : (Name, Type, Info).
        TmVar {ident = arg.0, ty = arg.1, info = arg.2}) args in
      TmParallelReduce {
        f = get a 2,
        ne = get a 1,
        as = get a 0,
        ty = TyUnknown {info = info},
        info = info}}]

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
    let paramNameMap =
      mapFromSeq nameCmp
        (map
          (lam p : (Name, Name).
            (p.0, lam info. TmVar {ident = p.1, ty = TyUnknown {info = info},
                                   info = info}))
          freeVarEnv.varEnv) in
    let replacement = pattern.replacement binding.info bindingArgs in
    Some (substituteVariables replacement paramNameMap)
  else None ()

let tryRewriteBinding = use MExprAst in
  lam binding : RecLetBinding.
  match functionParametersAndBody binding.body with (args, body) then
    let n = length patterns in
    recursive let tryMatchPattern = lam i.
      if lti i n then
        let pattern = get patterns i in
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
  sem findParallelPatterns =
  | TmRecLets t ->
    TmRecLets {t with bindings = map tryRewriteBinding t.bindings}
  | expr -> smap_Expr_Expr findParallelPatterns expr
end

lang TestLang = MExprParallelPatterns + MExprRewrite + MExprParallelKeywordMaker

mexpr

use TestLang in

let fold = nameSym "fold" in
let f = nameSym "f" in
let s = nameSym "s" in
let acc = nameSym "acc" in
let h = nameSym "h" in
let t = nameSym "t" in
let t1 = nreclets_ [
  (fold, tyunknown_, nulam_ s (nulam_ acc (nulam_ f (
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
  (fold, tyunknown_, nulam_ s (nulam_ acc (nulam_ f (
    parallelReduce_ (nvar_ f) (nvar_ acc) (nvar_ s)))))
] in

utest findParallelPatterns (rewriteTerm t1) with t2 using eqExpr in
utest findParallelPatterns t2 with t2 using eqExpr in

()
