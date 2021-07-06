include "mexpr/rewrite/pattern-match.mc"
include "mexpr/rewrite/parallel-patterns.mc"

lang MExprParallelPattern = MExprParallelKeywordMaker
  sem tryPatterns (patterns : [Pattern]) =
  | t ->
    let binding : RecLetBinding = t in
    let n = length patterns in
    recursive let tryPattern = lam i.
      if lti i n then
        let pattern : Pattern = get patterns i in
        match matchPattern binding pattern with Some map then
          Some (pattern.replacement map)
        else
          tryPattern (addi i 1)
      else None ()
    in
    tryPattern 0

  sem parallelPatternRewrite (patterns : [Pattern]) =
  | t ->
    let replacements = mapEmpty nameCmp in
    match parallelPatternRewriteH patterns replacements t with (_, t) then
      t
    else never

  sem parallelPatternRewriteH (patterns : [Pattern])
                              (replacements : Map Name ([Name], Expr)) =
  | TmRecLets t ->
    -- Collect the parameters
    let replacements =
      foldl
        (lam replacements. lam binding : RecLetBinding.
          match functionParametersAndBody binding.body with (params, _) then
            match tryPatterns patterns binding with Some replacement then
              let paramNames =
                map (lam param : (Name, Type, Info). param.0) params in
              mapInsert binding.ident (paramNames, replacement) replacements
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
            with (_, body) then
              {binding with body = body}
            else never)
          retainedBindings in

      -- Apply on the inexpr of the recursive let-expression (apply on the
      -- remaining part of the tree).
      match parallelPatternRewriteH patterns replacements t.inexpr
      with (replacements, inexpr) then
        (replacements, TmRecLets {{t with bindings = bindings}
                                     with inexpr = inexpr})
    else never
  | (TmApp {info = info}) & t ->
    let performSubstitution : Expr -> [Name] -> [Expr] -> Expr =
      lam e. lam paramNames. lam args.
      let substMap = mapFromSeq nameCmp
        (map
          (lam paramNameArg : (Name, Expr).
            (paramNameArg.0, lam info. withInfo info paramNameArg.1))
          (zip paramNames args)) in
      substituteVariables e substMap
    in
    match collectAppArguments t with (f, args) then
      let appBody =
        match f with TmVar {ident = ident} then
          match mapLookup ident replacements with Some (paramNames, expr) then
            let nargs = length args in
            let nparams = length paramNames in
            if lti nargs nparams then
              let diff = subi nparams nargs in
              let extraNames = create diff (lam. nameSym "x") in
              let exprWrappedInLambdas =
                foldl
                  (lam e. lam name.
                    TmLam {
                      ident = name,
                      tyIdent = TyUnknown {info = NoInfo ()},
                      body = e,
                      ty = ty e,
                      info = NoInfo ()})
                  expr
                  extraNames in
              let args = concat args (reverse extraNames) in
              Some (performSubstitution exprWrappedInLambdas paramNames args)
            else if eqi nargs nparams then
              Some (performSubstitution expr paramNames args)
            else
              infoErrorExit info (concat "Too many arguments passed to " ident)
          else None ()
        else None ()
      in
      (replacements, optionGetOrElse (lam. t) appBody)
    else never
  | t -> smapAccumL_Expr_Expr (parallelPatternRewriteH patterns) replacements t
end

lang TestLang =
  MExprANF + MExprRewrite + MExprParallelKeywordMaker + MExprTailRecursion +
  MExprPrettyPrint + MExprParallelPattern

  sem isAtomic =
  | TmParallelMap _ -> false
  | TmParallelMap2 _ -> false
  | TmParallelReduce _ -> false
  | TmParallelScan _ -> false
  | TmParallelFilter _ -> false
  | TmParallelPartition _ -> false
  | TmParallelAll _ -> false
  | TmParallelAny _ -> false
  | TmFlatten _ -> false
  | TmSequentialFor _ -> false
  
  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmParallelMap t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelMap (", f, ") (", as, ")"])
      else never
    else never
  | TmParallelMap2 t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        match pprintCode indent env t.bs with (env, bs) then
          (env, join ["parallelMap2 (", f, ") (", as, ") (", bs, ")"])
        else never
      else never
    else never
  | TmParallelReduce t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.ne with (env, ne) then
        match pprintCode indent env t.as with (env, as) then
          (env, join ["parallelReduce (", f, ") (", ne, ") (", as, ")"])
        else never
      else never
    else never
  | TmParallelScan t -> never
  | TmParallelFilter t -> never
  | TmParallelPartition t -> never
  | TmParallelAll t -> never
  | TmParallelAny t -> never
  | TmFlatten t -> never
  | TmSequentialFor t ->
    match printParen indent env t.body with (env, body) then
      match pprintCode indent env t.init with (env, init) then
        match pprintCode indent env t.n with (env, n) then
          (env, join ["for (", init, ") (", n, ")", pprintNewline indent, body])
        else never
      else never
    else never
end

mexpr

use TestLang in

let patterns = [getMapPattern (), getReducePattern (), getForPattern()] in

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

let fold = nameSym "fold" in
let acc = nameSym "acc" in
let x = nameSym "x" in
let y = nameSym "y" in
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

let iterMax = nameSym "iterMax" in
let max = nameSym "max" in
let i = nameSym "i" in
let n = nameSym "n" in
let expr = preprocess (bindall_ [
  nulet_ s (seq_ [int_ 1, int_ 2, int_ 3]),
  nulet_ n (length_ (nvar_ s)),
  nreclets_ [
    (iterMax, tyunknown_, nulam_ acc (nulam_ i (nulam_ n (
      if_ (eqi_ (nvar_ i) (nvar_ n))
        (nvar_ acc)
        (bindall_ [
          nulet_ x (get_ (nvar_ s) (nvar_ i)),
          nulet_ y (if_ (gtf_ (app_ (nvar_ f) (nvar_ acc))
                              (app_ (nvar_ f) (nvar_ x)))
                        (nvar_ acc)
                        (nvar_ x)),
          appf3_ (nvar_ iterMax) (nvar_ y) (addi_ (nvar_ i) (int_ 1)) (nvar_ n)
        ])))))
  ],
  appf3_ (nvar_ iterMax) (head_ (nvar_ s)) (int_ 0) (nvar_ n)
]) in
let expr = parallelPatternRewrite patterns expr in
utest recletBindingCount expr with 0 in
utest containsParallelKeyword expr with true in

()
