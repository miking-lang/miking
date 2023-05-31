include "pmexpr/pattern-match.mc"
include "pmexpr/parallel-patterns.mc"
include "pmexpr/promote.mc"

lang PMExprParallelPattern = PMExprAst + PMExprPromote + PMExprVariableSub
  sem tryPatterns (patterns : [Pattern]) =
  | t ->
    let binding : RecLetBinding = t in
    let n = length patterns in
    recursive let tryPattern = lam i.
      if lti i n then
        let pattern : Pattern = get patterns i in
        match matchPattern binding pattern with Some map then
          Some (pattern.replacement binding.info map)
        else
          tryPattern (addi i 1)
      else None ()
    in
    tryPattern 0

  sem parallelPatternRewrite (patterns : [Pattern]) =
  | t ->
    let replacements = mapEmpty nameCmp in
    match parallelPatternRewriteH patterns replacements t with (_, t) in
    promote t

  sem parallelPatternRewriteH (patterns : [Pattern])
                              (replacements : Map Name ([(Name, Type, Info)], Expr)) =
  | TmRecLets t ->
    -- Collect the parameters
    let replacements =
      foldl
        (lam replacements. lam binding : RecLetBinding.
          match functionParametersAndBody binding.body with (params, _) then
            match tryPatterns patterns binding with Some replacement then
              mapInsert binding.ident (params, replacement) replacements
            else replacements
          else replacements)
        replacements
        t.bindings in

    -- Remove bindings that have been replaced by parallel patterns
    let retainedBindings =
      filter
        (lam binding : RecLetBinding.
          optionIsNone (mapLookup binding.ident replacements))
        t.bindings in

    if null retainedBindings then
      parallelPatternRewriteH patterns replacements t.inexpr
    else
      -- Replace applications on replaced bindings within the bodies of the
      -- bindings that remain.
      let bindings =
        map
          (lam binding : RecLetBinding.
            match parallelPatternRewriteH patterns replacements binding.body
            with (_, body) in
            {binding with body = body})
          retainedBindings in

      -- Apply on the inexpr of the recursive let-expression (apply on the
      -- remaining part of the tree).
      match parallelPatternRewriteH patterns replacements t.inexpr
      with (replacements, inexpr) in
      (replacements, TmRecLets {{t with bindings = bindings}
                                   with inexpr = inexpr})
  | (TmApp {info = info}) & t ->
    let performSubstitution : Expr -> [(Name, Type, Info)] -> [Expr] -> Expr =
      lam e. lam params. lam args.
      let substMap = mapFromSeq nameCmp
        (map
          (lam paramArg : ((Name, Type, Info), Expr).
            match paramArg with ((id, ty, info), expr) in
            (id, lam info. withInfo info (withType ty expr)))
          (zip params args)) in
      substituteVariables substMap e
    in
    match collectAppArguments t with (f, args) in
    let appBody =
      match f with TmVar {ident = ident} then
        match mapLookup ident replacements with Some (params, expr) then
          let nargs = length args in
          let nparams = length params in
          if lti nargs nparams then
            let diff = subi nparams nargs in
            let extraNames = create diff (lam. nameSym "x") in
            let exprWrappedInLambdas =
              foldl
                (lam e. lam name.
                  -- TODO(larshum, 2021-12-06): Do not use TyUnknown, but
                  -- propagate the appropriate types based on the parameter
                  -- types, which are known.
                  TmLam {
                    ident = name,
                    tyAnnot = TyUnknown {info = info},
                    tyParam = TyUnknown {info = info},
                    body = e,
                    ty = tyTm e,
                    info = info})
                expr
                extraNames in
            let extraVars =
              map
                (lam id : Name.
                  TmVar {ident = id, ty = TyUnknown {info = info},
                         info = info, frozen = false})
                extraNames in
            let args = concat args (reverse extraVars) in
            Some (performSubstitution exprWrappedInLambdas params args)
          else if eqi nargs nparams then
            Some (performSubstitution expr params args)
          else errorSingle [info] (concat "Too many arguments passed to "
                                          (nameGetStr ident))
        else None ()
      else None ()
    in
    (replacements, optionGetOrElse (lam. t) appBody)
  | t -> smapAccumL_Expr_Expr (parallelPatternRewriteH patterns) replacements t
end

lang TestLang =
  MExprANF + PMExprRewrite + PMExprAst + PMExprTailRecursion + MExprPrettyPrint +
  PMExprParallelPattern

  sem isAtomic =
  | TmMap2 _ -> false
  | TmParallelReduce _ -> false
  
  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmMap2 t ->
    match printParen indent env t.f with (env, f) in
    match pprintCode indent env t.as with (env, as) in
    match pprintCode indent env t.bs with (env, bs) in
    (env, join ["parallelMap2 (", f, ") (", as, ") (", bs, ")"])
  | TmParallelReduce t ->
    match printParen indent env t.f with (env, f) in
    match pprintCode indent env t.ne with (env, ne) in
    match pprintCode indent env t.as with (env, as) in
    (env, join ["parallelReduce (", f, ") (", ne, ") (", as, ")"])
end

mexpr

use TestLang in

let patterns = [getMapPattern (), getReducePattern ()] in

let preprocess : Expr -> Expr = lam e.
  normalizeTerm (tailRecursive (rewriteTerm e))
in

let recletBindingCount : Expr -> Int = lam e.
  match e with TmRecLets t then
    length t.bindings
  else 0
in

let containsParallelKeyword : Expr -> Bool = lam e.
  recursive let work = lam acc. lam e.
    if or acc (isKeyword e) then true
    else match e with TmApp {lhs = TmApp {lhs = TmConst {val = CMap ()}}} then true
    else sfold_Expr_Expr work acc e
  in
  work false e
in

let map = nameSym "map" in
let f = nameSym "f" in
let s = nameSym "s" in
let h = nameSym "h" in
let t = nameSym "t" in
let addOne = nameSym "addOne" in
let x = nameSym "x" in
let expr = preprocess (nreclets_ [
  (map, tyunknown_, nulam_ f (nulam_ s (
    match_ (nvar_ s)
      (pseqtot_ [])
      (seq_ [])
      (match_ (nvar_ s)
        (pseqedgen_ [npvar_ h] t [])
        (cons_ (app_ (nvar_ f) (head_ (nvar_ s)))
               (appf2_ (nvar_ map) (nvar_ f) (tail_ (nvar_ s))))
        never_)))),
  (addOne, tyunknown_, nulam_ s (
    appf2_ (nvar_ map) (nulam_ x (addi_ (nvar_ x) (int_ 1))) (nvar_ s)
  ))
]) in
let expr = parallelPatternRewrite patterns expr in
utest recletBindingCount expr with 1 in
utest containsParallelKeyword expr with true in

let red = nameSym "reduce" in
let acc = nameSym "acc" in
let x = nameSym "x" in
let y = nameSym "y" in
let expr = preprocess (bindall_ [
  nureclets_ [
    (red, nulam_ acc (nulam_ s (
      match_ (nvar_ s)
        (pseqedgen_ [npvar_ h] t [])
        (appf2_ (nvar_ red)
          (addi_ (nvar_ acc) (nvar_ h))
          (nvar_ t))
        (match_ (nvar_ s)
          (pseqtot_ [])
          (nvar_ acc)
          never_))))],
  ulet_ "sum" (appf2_ (nvar_ red) (int_ 0) (seq_ [int_ 1, int_ 2, int_ 3]))
]) in
let expr = parallelPatternRewrite patterns expr in
utest recletBindingCount expr with 0 in
utest containsParallelKeyword expr with true in

let fold = nameSym "fold" in
let expr = preprocess (bindall_ [
  nreclets_ [
    (fold, tyunknown_, nulam_ acc (nulam_ f (nulam_ s (
      match_ (nvar_ s)
        (pseqedgen_ [npvar_ h] t [])
        (appf3_ (nvar_ fold)
          (appf2_ (nvar_ f) (nvar_ acc) (nvar_ h))
          (nvar_ f)
          (nvar_ t))
        (match_ (nvar_ s)
          (pseqtot_ [])
          (nvar_ acc)
          never_)))))],
  ulet_ "sum" (
    appf3_ (nvar_ fold)
      (int_ 0)
      (uconst_ (CAddi ()))
      (seq_ [int_ 1, int_ 2, int_ 3]))
]) in
let expr = parallelPatternRewrite patterns expr in
utest recletBindingCount expr with 0 in
utest containsParallelKeyword expr with true in

()
