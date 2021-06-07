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
let reducePattern =
  if_ (null_ (nvar_ s))
    (nvar_ acc)
    (appf2_ (nvar_ f) (head_ (nvar_ s))
      (appf3_ (nvar_ reduceName) (nvar_ f) (nvar_ acc) (tail_ (nvar_ s))))
let patterns =
  use MExprAst in
  [{ident = reduceName, expr = reducePattern,
    replacement = lam info. lam args.
      let a = map (lam arg : (Name, Type, Info).
        TmVar {ident = arg.0, ty = arg.1, info = arg.2}) args in
      withInfo info (parallelReduce_ (get a 0) (get a 1) (get a 2))}]

let matchPattern : Name -> Expr -> [(Name, Type, Info)] -> ParallelPattern
                -> Option Expr =
  use MExprParallelKeywordMaker in
  lam binding. lam bindingBody. lam bindingArgs. lam pattern.
  let pat = substituteIdentifier pattern.expr pattern.ident binding.ident in
  let empty = {varEnv = biEmpty, conEnv = biEmpty} in
  match eqExprH empty empty pat bindingBody with Some freeVarEnv then
    let paramNameMap =
      map
        (lam p : (Name, Name).
          (p.0, lam info. TmVar {ident = p.1, info = info}))
        freeVarEnv.varEnv in
    let replacement = pattern.replacement binding.info bindingArgs in
    Some (substituteVariables pattern.replacement paramNameMap)
  else None ()

let tryRewriteBinding = use MExprAst in
  lam binding : RecLetBinding.
  let body = functionBodyWithoutLambdas binding.body in
  let n = length patterns in
  recursive let tryPatterns = lam i.
    if leqi i n then
      let pattern = get patterns i in
      let args = functionArguments binding.body in
      match matchPattern binding body args pattern with Some replacement then
        Some ({binding with body = replacement})
      else
        tryPatterns (addi i 1)
    else None ()
  in
  match tryPatterns 0 with Some rewrittenBinding then
    rewrittenBinding
  else binding

lang MExprParallelPatterns = MExprAst
  sem findParallelPatterns =
  | TmRecLets t ->
    map tryRewriteBinding t.bindings
  | expr -> smap_Expr_Expr findParallelPatterns expr
end

lang TestLang = MExprParallelPatterns + MExprRewrite + MExprEq

mexpr

use TestLang in

let fold = nameSym "fold" in
let f = nameSym "f" in
let s = nameSym "s" in
let h = nameSym "h" in
let t = nameSym "t" in
let t1 = nreclets_ [
  (fold, tyunknown_, nulam_ f (nulam_ acc (nulam_ s (
    match_ (nvar_ s)
      (pseqedgen_ [npvar_ h] t [])
      (appf3_ (nvar_ fold) (nvar_ f) (nvar_ t)
        (appf2_ (nvar_ f) (nvar_ acc) (nvar_ h)))
      (match_ (nvar_ s)
        (pseqtot_ [])
        (seq_ [])
        never_)))))
] in
let t2 = nreclets_ [
  (fold, tyunknown_, nulam_ f (nulam_ acc (nulam_ s (
    parallelReduce_ (nvar_ f) (nvar_ acc) (nvar_ s)))))
] in
utest findParallelPatterns (rewriteTerm t1) with t2 using eqExpr in

()
