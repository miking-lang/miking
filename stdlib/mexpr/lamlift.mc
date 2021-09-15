-- Defines lambda lifting of MExpr AST nodes in quadratic time in the size of
-- the program.

include "digraph.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

type LambdaLiftState = {
  -- Variables in the current scope that can occur as free variables in the
  -- current expression.
  vars : Set Name,

  -- Functions in the current scope that can occur as free variables in the
  -- current expression.
  funs : Set Name,

  -- Contains the solutions of the functions found in funs. The solution of a
  -- function is a set of identifiers corresponding to its free variables.
  sols : Map Name (Set Name)
}

let emptyLambdaLiftState = {
  vars = setEmpty nameCmp,
  funs = setEmpty nameCmp,
  sols = mapEmpty nameCmp
}

-- Adds a name to all anonymous functions by wrapping them in a let-expression.
-- These are all lambda expressions that are not part of the right-hand side of
-- a let-expression or a recursive binding.
lang LambdaLiftNameAnonymous = MExprAst
  sem nameAnonymousLambdasInBody =
  | TmLam t -> TmLam {t with body = nameAnonymousLambdasInBody t.body}
  | t -> nameAnonymousLambdas t

  sem nameAnonymousLambdas =
  | TmLam t ->
    let lambdaName = nameSym "t" in
    TmLet {ident = lambdaName, tyBody = t.ty, body = TmLam t,
           inexpr = TmVar {ident = lambdaName, ty = t.ty, info = t.info},
           ty = t.ty, info = t.info}
  | TmLet t ->
    TmLet {{t with body = nameAnonymousLambdasInBody t.body}
              with inexpr = nameAnonymousLambdas t.inexpr}
  | TmRecLets t ->
    let bindings =
      map
        (lam bind : RecLetBinding.
          {bind with body = nameAnonymousLambdasInBody bind.body})
        t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = nameAnonymousLambdas t.inexpr}
  | t -> smap_Expr_Expr nameAnonymousLambdas t
end

lang LambdaLiftFindFreeVariablesPat = MExprAst
  sem getFreeVariablePatName (state : LambdaLiftState) =
  | PName id -> {state with vars = setInsert id state.vars}
  | PWildcard _ -> state

  sem findFreeVariablesPat (state : LambdaLiftState) =
  | PatNamed t -> getFreeVariablePatName state t.ident
  | PatSeqEdge t ->
    let state = foldl findFreeVariablesPat state t.prefix in
    let state = getFreeVariablePatName state t.middle in
    foldl findFreeVariablesPat state t.postfix
  | p -> sfold_Pat_Pat findFreeVariablesPat state p
end

-- Finds the set of free variables of all functions. For recursive
-- let-expressions, this requires solving a system of set equations (as the
-- free variables within bindings may affect each other).
lang LambdaLiftFindFreeVariables = MExprAst + LambdaLiftFindFreeVariablesPat
  sem findFreeVariablesInBody (state : LambdaLiftState) (fv : Set Name) =
  | TmVar t ->
    if setMem t.ident state.vars then
      setInsert t.ident fv
    else if setMem t.ident state.funs then
      match mapLookup t.ident state.sols with Some funFreeVars then
        mapFoldWithKey
          (lam acc. lam id. lam. setInsert id acc)
          fv
          funFreeVars
      else fv
    else fv
  | TmLam t -> findFreeVariablesInBody state fv t.body
  | TmLet t ->
    let fv = findFreeVariablesInBody state fv t.body in
    findFreeVariablesInBody state fv t.inexpr
  | TmRecLets t -> findFreeVariablesInBody state fv t.inexpr
  | t -> sfold_Expr_Expr (findFreeVariablesInBody state) fv t

  sem findFreeVariablesReclet (state : LambdaLiftState) =
  | TmLet t ->
    let state =
      match t.tyBody with TyArrow _ then
        let fv = findFreeVariablesInBody state (setEmpty nameCmp) t.body in
        {{state with funs = setInsert t.ident state.funs}
                with sols = mapInsert t.ident fv state.sols}
      else state
    in
    findFreeVariablesReclet state t.inexpr
  | TmRecLets t ->
    let findBinding = lam state : LambdaLiftState. lam bind : RecLetBinding.
      let fv = findFreeVariablesInBody state (setEmpty nameCmp) bind.body in
      {{state with funs = setInsert bind.ident state.funs}
              with sols = mapInsert bind.ident fv state.sols}
    in
    let state = foldl findBinding state t.bindings in
    findFreeVariablesReclet state t.inexpr
  | t -> sfold_Expr_Expr findFreeVariablesReclet state t

  sem addGraphVertices (g : Digraph Name Int) =
  | TmLet t ->
    let g =
      match t.tyBody with TyArrow _ then digraphAddVertex t.ident g
      else g
    in
    let g = addGraphVertices g t.body in
    addGraphVertices g t.inexpr
  | TmRecLets t ->
    let g =
      foldl
        (lam g. lam bind : RecLetBinding. digraphAddVertex bind.ident g)
        g t.bindings in
    let g =
      foldl
        (lam g. lam bind : RecLetBinding.
          addGraphVertices g bind.body)
        g t.bindings in
    addGraphVertices g t.inexpr
  | t -> sfold_Expr_Expr addGraphVertices g t

  sem addGraphCallEdges (src : Name) (g : Digraph Name Int) =
  | TmVar t ->
    if digraphHasVertex t.ident g then
      digraphMaybeAddEdge src t.ident 0 g
    else g
  | TmLet t ->
    let letSrc = match t.tyBody with TyArrow _ then t.ident else src in
    let g = addGraphCallEdges letSrc g t.body in
    addGraphCallEdges src g t.inexpr
  | TmRecLets t ->
    let g =
      foldl
        (lam g. lam bind : RecLetBinding.
          addGraphCallEdges bind.ident g bind.body)
        g
        t.bindings in
    addGraphCallEdges src g t.inexpr
  | t -> sfold_Expr_Expr (addGraphCallEdges src) g t

  sem findFreeVariables (state : LambdaLiftState) =
  | TmLam t ->
    let state = {state with vars = setInsert t.ident state.vars} in
    findFreeVariables state t.body
  | TmLet t ->
    let state =
      match t.tyBody with TyArrow _ then
        let fv = findFreeVariablesInBody state (setEmpty nameCmp) t.body in
        {{state with funs = setInsert t.ident state.funs}
                with sols = mapInsert t.ident fv state.sols}
      else
        {state with vars = setInsert t.ident state.vars}
    in
    let state = findFreeVariables state t.body in
    findFreeVariables state t.inexpr
  | TmRecLets t ->
    recursive let propagateFunNames : LambdaLiftState -> Digraph Name Int
                                   -> [[Name]] -> LambdaLiftState =
      lam state. lam g. lam s.
      match s with [h] ++ t then
        let freeVars =
          foldl
            (lam acc. lam id.
              match mapLookup id state.sols with Some fv then
                setUnion acc fv
              else acc)
            (setEmpty nameCmp) h in
        let state =
          foldl
            (lam state : LambdaLiftState. lam id.
              {state with sols = mapInsert id freeVars state.sols})
            state h in
        propagateFunNames state g t
      else state
    in
    let findFreeVariablesBinding : LambdaLiftState -> RecLetBinding
                                -> LambdaLiftState =
      lam state. lam bind.
      findFreeVariables state bind.body
    in
    let state = findFreeVariablesReclet state (TmRecLets t) in
    let g : Digraph Name Int = digraphEmpty nameEq eqi in
    let g = addGraphVertices g (TmRecLets t) in
    let g =
      foldl
        (lam g. lam bind : RecLetBinding.
          addGraphCallEdges bind.ident g bind.body)
        g t.bindings in
    let sccs = digraphTarjan g in
    let state = propagateFunNames state g (reverse sccs) in
    let state = foldl findFreeVariablesBinding state t.bindings in
    findFreeVariables state t.inexpr
  | TmMatch t ->
    let state = findFreeVariables state t.target in
    let state = findFreeVariablesPat state t.pat in
    let state = findFreeVariables state t.thn in
    findFreeVariables state t.els
  | TmExt t ->
    let state = {state with vars = setInsert t.ident state.vars} in
    findFreeVariables state t.inexpr
  | t -> sfold_Expr_Expr findFreeVariables state t
end

lang LambdaLiftInsertFreeVariables = MExprAst
  sem insertFreeVariablesH (solutions : Map Name (Set Name))
                           (subMap : Map Name (Info -> Expr)) =
  | TmVar t ->
    match mapLookup t.ident subMap with Some subExpr then
      (subMap, subExpr t.info)
    else (subMap, TmVar t)
  | TmLet (t & {tyBody = TyArrow _}) ->
    match mapLookup t.ident solutions with Some freeVars then
      let fv = setToSeq freeVars in
      let info = infoTm t.body in
      let body =
        foldr
          (lam freeVarId. lam body.
            TmLam {ident = freeVarId, tyIdent = TyUnknown {info = info},
                   body = body, ty = ty body, info = info})
          t.body
          fv in
      let subExpr = lam info.
        foldr
          (lam freeVarId. lam acc.
            let x = TmVar {ident = freeVarId, ty = TyUnknown {info = info},
                           info = info} in
            TmApp {lhs = acc, rhs = x, ty = TyUnknown {info = info}, info = info})
          (TmVar {ident = t.ident, ty = t.tyBody, info = info})
          fv in
      match insertFreeVariablesH solutions subMap body with (subMap, body) then
        let subMap = mapInsert t.ident subExpr subMap in
        match insertFreeVariablesH solutions subMap t.inexpr
        with (subMap, inexpr) then
          (subMap, TmLet {{t with body = body}
                             with inexpr = inexpr})
        else never
      else never
    else error (join ["Found no free variable solution for ",
                      nameGetStr t.ident])
  | TmRecLets t ->
    let addBindingSubExpression =
      lam subMap : Map Name (Info -> Expr). lam bind : RecLetBinding.
      match mapLookup bind.ident solutions with Some freeVars then
        let subExpr = lam info.
          foldr
            (lam freeVarId. lam acc.
              let x = TmVar {ident = freeVarId, ty = TyUnknown {info = info},
                             info = info} in
              TmApp {lhs = acc, rhs = x, ty = TyUnknown {info = info}, info = info})
            (TmVar {ident = bind.ident, ty = bind.tyBody, info = info})
            (reverse (setToSeq freeVars)) in
        mapInsert bind.ident subExpr subMap
      else error (join ["Lambda lifting error: No solution found for binding ",
                        nameGetStr bind.ident])
    in
    let insertFreeVarsBinding =
      lam subMap : Map Name (Info -> Expr). lam bind : RecLetBinding.
      match mapLookup bind.ident solutions with Some freeVars then
        let body =
          foldr
            (lam freeVarId. lam body.
              let info = infoTm body in
              TmLam {ident = freeVarId, tyIdent = TyUnknown {info = info},
                     body = body, ty = ty body, info = info})
            bind.body
            (setToSeq freeVars) in
        match insertFreeVariablesH solutions subMap body with (subMap, body) then
          (subMap, {bind with body = body})
        else never
      else error (join ["Lambda lifting error: No solution found for binding ",
                        nameGetStr bind.ident])
    in
    let subMap = foldl addBindingSubExpression subMap t.bindings in
    match mapAccumL insertFreeVarsBinding subMap t.bindings
    with (subMap, bindings) then
      match insertFreeVariablesH solutions subMap t.inexpr with (subMap, inexpr) then
        (subMap, TmRecLets {{t with bindings = bindings}
                               with inexpr = inexpr})
      else never
    else never
  | t -> smapAccumL_Expr_Expr (insertFreeVariablesH solutions) subMap t

  sem insertFreeVariables (solutions : Map Name (Set Name)) =
  | t ->
    match insertFreeVariablesH solutions (mapEmpty nameCmp) t with (_, t) then
      t
    else never
end

lang LambdaLiftLiftGlobal = MExprAst
  sem _bindIfNonEmpty (lifted : [Expr]) =
  | t ->
    if null lifted then t
    else bindall_ (snoc lifted t)

  sem liftRecursiveBindingH (bindings : [RecLetBinding]) =
  | TmLet t ->
    match liftRecursiveBindingH bindings t.body with (bindings, body) then
      match t.tyBody with TyArrow _ then
        let bind : RecLetBinding =
          {ident = t.ident, tyBody = t.tyBody, body = t.body, info = t.info} in
        let bindings = snoc bindings bind in
        liftRecursiveBindingH bindings t.inexpr
      else match liftRecursiveBindingH bindings t.inexpr
      with (bindings, inexpr) then
        (bindings, TmLet {{t with body = body}
                             with inexpr = inexpr})
      else never
    else never
  | TmRecLets t ->
    let liftBinding : [RecLetBinding] -> RecLetBinding -> [RecLetBinding] =
      lam bindings. lam bind.
      match liftRecursiveBindingH bindings bind.body with (bindings, body) then
        snoc bindings {bind with body = body}
      else never
    in
    let bindings = foldl liftBinding bindings t.bindings in
    liftRecursiveBindingH bindings t.inexpr
  | t -> smapAccumL_Expr_Expr liftRecursiveBindingH bindings t

  sem liftRecursiveBinding =
  | TmRecLets t /- : Expr -> Expr -/ ->
    let liftBinding : [RecLetBinding] -> RecLetBinding -> [RecLetBinding] =
      lam bindings. lam bind.
      match liftRecursiveBindingH bindings bind.body with (bindings, body) then
        snoc bindings {bind with body = body}
      else never
    in
    let bindings = foldl liftBinding [] t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = unit_}

  sem liftGlobalH (lifted : [Expr]) =
  | TmLet t ->
    match liftGlobalH lifted t.body with (lifted, body) then
      match t.tyBody with TyArrow _ then
        let lifted = snoc lifted (TmLet {{t with body = body}
                                            with inexpr = unit_}) in
        liftGlobalH lifted t.inexpr
      else match liftGlobalH lifted t.inexpr with (lifted, inexpr) then
        (lifted, TmLet {{t with body = body}
                           with inexpr = inexpr})
      else never
    else never
  | TmRecLets t ->
    let lifted = snoc lifted (liftRecursiveBinding (TmRecLets t)) in
    (lifted, t.inexpr)
  | t -> smapAccumL_Expr_Expr liftGlobalH lifted t

  sem liftGlobal =
  | TmLet t ->
    match liftGlobalH [] t.body with (lifted, body) then
      _bindIfNonEmpty
        lifted
        (TmLet {{t with body = body}
                   with inexpr = liftGlobal t.inexpr})
    else never
  | TmRecLets t ->
    let lifted = [liftRecursiveBinding (TmRecLets t)] in
    _bindIfNonEmpty
      lifted
      (liftGlobal t.inexpr)
  | TmType t -> TmType {t with inexpr = liftGlobal t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = liftGlobal t.inexpr}
  | TmUtest t ->
    match liftGlobalH [] t.test with (lifted, test) then
      match liftGlobalH lifted t.expected with (lifted, expected) then
        _bindIfNonEmpty
          lifted
          (TmUtest {{{t with test = test}
                        with expected = expected}
                        with next = liftGlobal t.next})
      else never
    else never
  | TmExt t -> TmExt {t with inexpr = liftGlobal t.inexpr}
  | t ->
    match liftGlobalH [] t with (lifted, t) then
      _bindIfNonEmpty
        lifted
        t
    else never
end

lang MExprLambdaLift =
  LambdaLiftNameAnonymous + LambdaLiftFindFreeVariables +
  LambdaLiftInsertFreeVariables + LambdaLiftLiftGlobal

  sem liftLambdas =
  | t ->
    let t = nameAnonymousLambdas t in
    let state : LambdaLiftState = findFreeVariables emptyLambdaLiftState t in
    let t = insertFreeVariables state.sols t in
    liftGlobal t
end

lang TestLang = MExprLambdaLift + MExprEq + MExprSym + MExprTypeAnnot

mexpr

use TestLang in

let preprocess = lam t. typeAnnot (symbolize t) in

let noLambdas = bind_ (ulet_ "x" (int_ 2)) unit_ in
utest liftLambdas noLambdas with noLambdas using eqExpr in

let innerFunction = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x"
    (bind_
      (ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))))
      (muli_ (app_ (var_ "g") (var_ "x")) (int_ 2)))),
  app_ (var_ "f") (int_ 1)]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (muli_ (app_ (var_ "g") (var_ "x")) (int_ 2))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas innerFunction with expected using eqExpr in

let factorial = preprocess (ureclets_ [
  ("fact", ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (int_ 1)
      (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))))]) in
utest liftLambdas factorial with factorial using eqExpr in

let factorialWithHelper = preprocess (bindall_ [
  ulet_ "fact" (ulam_ "n" (bindall_ [
    ureclets_ [
      ("work", ulam_ "acc" (ulam_ "n" (
        if_ (eqi_ (var_ "n") (int_ 0))
          (var_ "acc")
          (appf2_ (var_ "work")
            (muli_ (var_ "acc") (var_ "n"))
            (subi_ (var_ "n") (int_ 1))))))],
    appf2_ (var_ "work") (int_ 1) (var_ "n")])),
  app_ (var_ "fact") (int_ 4)]) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("work", ulam_ "acc" (ulam_ "n" (
      if_ (eqi_ (var_ "n") (int_ 0))
        (var_ "acc")
        (appf2_ (var_ "work")
          (muli_ (var_ "acc") (var_ "n"))
          (subi_ (var_ "n") (int_ 1))))))],
  ulet_ "fact" (ulam_ "n" (appf2_ (var_ "work") (int_ 1) (var_ "n"))),
  app_ (var_ "fact") (int_ 4)]) in
utest liftLambdas factorialWithHelper with expected using eqExpr in

let liftFreeVars = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))),
    app_ (var_ "g") (int_ 2)])),
  app_ (var_ "f") (int_ 3)]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 2))),
  app_ (var_ "f") (int_ 3)]) in
utest liftLambdas liftFreeVars with expected using eqExpr in

let deepNesting = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (bindall_ [
      ulet_ "h" (ulam_ "z" (
        addi_ (var_ "y") (var_ "z"))),
      app_ (var_ "h") (int_ 2)])),
    app_ (var_ "g") (var_ "x")])),
  app_ (var_ "f") (int_ 1)]) in
let expected = preprocess (bindall_ [
  ulet_ "h" (ulam_ "y" (ulam_ "z" (addi_ (var_ "y") (var_ "z")))),
  ulet_ "g" (ulam_ "y" (appf2_ (var_ "h") (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas deepNesting with expected using eqExpr in

let multipleInnerLets = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))),
    ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (var_ "x"))),
    addi_ (app_ (var_ "g") (int_ 1)) (app_ (var_ "h") (int_ 2))])),
  app_ (var_ "f") (int_ 1)]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "h" (ulam_ "x" (ulam_ "z" (addi_ (var_ "z") (var_ "x")))),
  ulet_ "f" (ulam_ "x" (
    addi_ (appf2_ (var_ "g") (var_ "x") (int_ 1))
          (appf2_ (var_ "h") (var_ "x") (int_ 2)))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas multipleInnerLets with expected using eqExpr in

let letInReclet = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ureclets_ [
      ("g", ulam_ "y" (bindall_ [
        ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (int_ 1))),
        addi_ (app_ (var_ "h") (var_ "y")) (var_ "x")
      ]))],
    app_ (var_ "g") (int_ 1)
  ])),
  app_ (var_ "f") (int_ 4)]) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("h", ulam_ "z" (addi_ (var_ "z") (int_ 1))),
    ("g", ulam_ "x" (ulam_ "y" (
      addi_ (app_ (var_ "h") (var_ "y")) (var_ "x"))))],
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 4)]) in
utest liftLambdas letInReclet with expected using eqExpr in

let deepNestedRecursiveDefs = preprocess (ureclets_ [
  ("f1", ulam_ "x" (bindall_ [
    ulet_ "f2" (bindall_ [
      ureclets_ [("f3", ulam_ "x1" (addi_ (var_ "x1") (int_ 1)))],
      ureclets_ [
        ("f4", ulam_ "y" (bindall_ [
          ulet_ "k" (ulam_ "x2" (app_ (var_ "f5") (var_ "x2"))),
          addi_ (app_ (var_ "k") (var_ "x")) (var_ "y")])),
        ("f5", ulam_ "x3" (app_ (var_ "f4") (subi_ (var_ "x3") (int_ 1))))
      ],
      addi_ (app_ (var_ "f3") (var_ "x"))
            (app_ (var_ "f4") (int_ 2))]),
    var_ "f2"]))]) in
let expected = preprocess (ureclets_ [
  ("f3", ulam_ "x1" (addi_ (var_ "x1") (int_ 1))),
  ("k", ulam_ "x" (ulam_ "x2" (appf2_ (var_ "f5") (var_ "x") (var_ "x2")))),
  ("f4", ulam_ "x" (ulam_ "y" (addi_ (appf2_ (var_ "k") (var_ "x") (var_ "x")) (var_ "y")))),
  ("f5", ulam_ "x" (ulam_ "x3" (appf2_ (var_ "f4") (var_ "x") (subi_ (var_ "x3") (int_ 1))))),
  ("f1", ulam_ "x" (bindall_ [
    ulet_ "f2" (addi_ (app_ (var_ "f3") (var_ "x"))
                      (appf2_ (var_ "f4") (var_ "x") (int_ 2))),
    var_ "f2"]))]) in
utest liftLambdas deepNestedRecursiveDefs with expected using eqExpr in

let fdef = ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))) in
let fapp = bind_ fdef (app_ (var_ "f") (int_ 1)) in

let liftUtest = preprocess (
  utest_
    (int_ 0)
    fapp
    unit_) in
let expected = preprocess (
  bind_
    fdef
    (utest_
      (int_ 0)
      (app_ (var_ "f") (int_ 1))
      unit_)) in
utest liftLambdas liftUtest with expected using eqExpr in

let liftApp = preprocess (bindall_ [
  app_
    (bind_
      (ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))))
      (app_ (var_ "g") (int_ 2)))
    fapp]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  fdef,
  app_
    (app_ (var_ "g") (int_ 2))
    (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftApp with expected using eqExpr in

let liftSeq = preprocess (seq_ [fapp]) in
let expected = preprocess (bindall_ [fdef, seq_ [app_ (var_ "f") (int_ 1)]]) in
utest liftLambdas liftSeq with expected using eqExpr in

let liftRecord = preprocess (urecord_ [("a", fapp), ("b", int_ 2)]) in
let expected = preprocess (bindall_ [
  fdef,
  urecord_ [
    ("a", app_ (var_ "f") (int_ 1)),
    ("b", int_ 2)]]) in
utest liftLambdas liftRecord with expected using eqExpr in

let liftRecordUpdate = preprocess (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)]),
  recordupdate_ (var_ "r") "b" fapp
  ]) in
let expected = preprocess (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)]),
  fdef,
  recordupdate_ (var_ "r") "b" (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftRecordUpdate with expected using eqExpr in

let liftMatchTarget = preprocess (
  match_ fapp (pint_ 0)
    (int_ 1)
    (int_ 2)) in
let expected = preprocess (bindall_ [
  fdef,
  match_ (app_ (var_ "f") (int_ 1)) (pint_ 0)
    (int_ 1)
    (int_ 2)]) in
utest liftLambdas liftMatchTarget with expected using eqExpr in

let liftMatchThn = preprocess (
  match_ (int_ 3) (pint_ 3)
    fapp
    (int_ 0)) in
let expected = preprocess (bindall_ [
  fdef,
  match_ (int_ 3) (pint_ 3)
    (app_ (var_ "f") (int_ 1))
    (int_ 0)]) in
utest liftLambdas liftMatchThn with expected using eqExpr in

let liftMatchEls = preprocess (
  match_ (int_ 3) (pint_ 3)
    (int_ 0)
    fapp) in
let expected = preprocess (bindall_ [
  fdef,
  match_ (int_ 3) (pint_ 3)
    (int_ 0)
    (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftMatchEls with expected using eqExpr in

let conAppLift = preprocess (bindall_ [
  condef_ "Leaf" (tyarrow_ tyint_ (tyvar_ "Tree")),
  conapp_ "Leaf" fapp
]) in
let expected = preprocess (bindall_ [
  condef_ "Leaf" (tyarrow_ tyint_ (tyvar_ "Tree")),
  fdef,
  conapp_ "Leaf" (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas conAppLift with expected using eqExpr in

let anonymousFunctionLift = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (
    app_ (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) (int_ 4))),
  app_ (var_ "f") (int_ 2)]) in
let expected = preprocess (bindall_ [
  ulet_ "t" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "t") (var_ "x") (int_ 4))),
  app_ (var_ "f") (int_ 2)]) in
utest liftLambdas anonymousFunctionLift with expected using eqExpr in

let anonymousMapLift = preprocess (
  map_ (ulam_ "x" (addi_ (var_ "x") (int_ 1))) (seq_ [int_ 0, int_ 7])) in
let expected = preprocess (bindall_ [
  ulet_ "t" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  map_ (var_ "t") (seq_ [int_ 0, int_ 7])]) in
utest liftLambdas anonymousMapLift with expected using eqExpr in

let recursiveSystem = preprocess (bindall_ [
  ulet_ "a" (int_ 1),
  ulet_ "b" (int_ 2),
  ulet_ "c" (int_ 5),
  ureclets_ [
    ("f", ulam_ "x" (addi_ (app_ (var_ "g") (var_ "x")) (var_ "a"))),
    ("g", ulam_ "y" (addi_ (app_ (var_ "h") (var_ "y")) (var_ "b"))),
    ("h", ulam_ "z" (addi_ (app_ (var_ "f") (var_ "z")) (var_ "c")))],
  unit_]) in
let expected = preprocess (bindall_ [
  ulet_ "a" (int_ 1),
  ulet_ "b" (int_ 2),
  ulet_ "c" (int_ 5),
  ureclets_ [
    ("f", ulams_ ["a", "b", "c", "x"] (
      addi_ (appSeq_ (var_ "g") [var_ "a", var_ "b", var_ "c", var_ "x"])
            (var_ "a"))),
    ("g", ulams_ ["a", "b", "c", "y"] (
      addi_ (appSeq_ (var_ "h") [var_ "a", var_ "b", var_ "c", var_ "y"])
            (var_ "b"))),
    ("h", ulams_ ["a", "b", "c", "z"] (
      addi_ (appSeq_ (var_ "f") [var_ "a", var_ "b", var_ "c", var_ "z"])
            (var_ "c")))],
  unit_]) in
utest liftLambdas recursiveSystem with expected using eqExpr in

let boundInMatchPat = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (
    match_ (var_ "x") (pvar_ "y")
      (bind_
        (ulet_ "g" (ulam_ "z" (addi_ (var_ "y") (var_ "z"))))
        (app_ (var_ "g") (var_ "x")))
      (int_ 0)))]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "z" (addi_ (var_ "y") (var_ "z")))),
  ulet_ "f" (ulam_ "x" (
    match_ (var_ "x") (pvar_ "y")
      (appf2_ (var_ "g") (var_ "y") (var_ "x"))
      (int_ 0)))]) in
utest liftLambdas boundInMatchPat with expected using eqExpr in

let nestedFreeVar = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (bindall_ [
      ulet_ "h" (ulam_ "z" (addi_ (var_ "x") (var_ "z"))),
      app_ (var_ "h") (var_ "y")])),
    app_ (var_ "g") (var_ "x")]))]) in
let expected = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (ulam_ "z" (addi_ (var_ "x") (var_ "z")))),
  ulet_ "g" (ulam_ "x" (ulam_ "y" (appf2_ (var_ "h") (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (var_ "x")))
]) in
utest liftLambdas nestedFreeVar with expected using eqExpr in

()
