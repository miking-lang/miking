include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"

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

-- Finds the set of free variables of all functions. For recursive
-- let-expressions, this requires solving a system of set equations (as the
-- free variables within bindings may affect each other).
lang LambdaLiftFreeVariables = MExprAst
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
      else error (join ["Invalid lambda lift state: function set contains ",
                        "key ", nameGetStr t.ident, " but this key was not ",
                        "found in the solutions map"])
    else
      -- NOTE(larshum, 2021-09-12): Variable was bound within the scope of the
      -- current body.
      fv
  | TmLam t -> findFreeVariablesInBody state fv t.body
  | TmLet (t & {body = TmLam _}) ->
    fv
  | TmLet t ->
    let fv = findFreeVariablesInBody state fv t.body in
    findFreeVariablesInBody state fv t.inexpr
  | TmRecLets t -> findFreeVariablesInBody state fv t.inexpr
  | t -> sfold_Expr_Expr (findFreeVariablesInBody state) fv t

  sem findFreeVariables (state : LambdaLiftState) =
  | TmLet t ->
    let state =
      match t.body with TmLam _ then
        let fv = findFreeVariablesInBody state (setEmpty nameCmp) t.body in
        {{state with funs = setInsert t.ident state.funs}
                with sols = mapInsert t.ident fv state.sols}
      else state
    in
    match findFreeVariables state t.body with (state, body) then
      match findFreeVariables state t.inexpr with (state, inexpr) then
        (state, TmLet {{t with body = body} with inexpr = inexpr})
      else never
    else never
  | TmRecLets t ->
    -- TODO(larshum, 2021-09-12): Solve the system of set equations that the
    -- bindings give rise to - approach is to solve for each SCC (of call
    -- graph) through substitution, as functions within same SCC will all have
    -- the same free variables.
    (state, t)
  | t -> smapAccumL_Expr_Expr findFreeVariables state t
end

lang MExprLambdaLift = LambdaLiftNameAnonymous + LambdaLiftFreeVariables
  sem liftLambdas =
  | t ->
    let t = nameAnonymousLambdas t in
    let t = findFreeVariables emptyLambdaLiftState t in
    unit_
end

lang TestLang = MExprLambdaLift + MExprEq + MExprPrettyPrint

mexpr

use TestLang in

let noLambdas = bind_ (ulet_ "x" (int_ 2)) unit_ in
utest liftLambdas noLambdas with noLambdas using eqExpr in

let innerFunction = symbolize (bindall_ [
  ulet_ "f" (ulam_ "x"
    (bind_
      (ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))))
      (muli_ (app_ (var_ "g") (var_ "x")) (int_ 2)))),
  app_ (var_ "f") (int_ 1)]) in
let expected = symbolize (bindall_ [
  ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (
    muli_ (app_ (var_ "g") (var_ "x")) (int_ 2))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas innerFunction with expected using eqExpr in

let factorial = symbolize (ureclets_ [
  ("fact", ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (int_ 1)
      (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))))]) in
utest liftLambdas factorial with factorial using eqExpr in

let factorialWithHelper = symbolize (bindall_ [
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
let expected = symbolize (bindall_ [
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

let liftFreeVars = symbolize (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))),
    app_ (var_ "g") (int_ 2)])),
  app_ (var_ "f") (int_ 3)]) in
let expected = symbolize (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 2))),
  app_ (var_ "f") (int_ 3)]) in
utest liftLambdas liftFreeVars with expected using eqExpr in

let deepNesting = symbolize (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (bindall_ [
      ulet_ "h" (ulam_ "z" (
        addi_ (var_ "y") (var_ "z"))),
      app_ (var_ "h") (int_ 2)])),
    app_ (var_ "g") (var_ "x")])),
  app_ (var_ "f") (int_ 1)]) in
let expected = symbolize (bindall_ [
  ulet_ "h" (ulam_ "y" (ulam_ "z" (addi_ (var_ "y") (var_ "z")))),
  ulet_ "g" (ulam_ "y" (appf2_ (var_ "h") (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas deepNesting with expected using eqExpr in

let multipleInnerLets = symbolize (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))),
    ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (var_ "x"))),
    addi_ (app_ (var_ "g") (int_ 1)) (app_ (var_ "h") (int_ 2))])),
  app_ (var_ "f") (int_ 1)]) in
let expected = symbolize (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "h" (ulam_ "x" (ulam_ "z" (addi_ (var_ "z") (var_ "x")))),
  ulet_ "f" (ulam_ "x" (
    addi_ (appf2_ (var_ "g") (var_ "x") (int_ 1))
          (appf2_ (var_ "h") (var_ "x") (int_ 2)))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas multipleInnerLets with expected using eqExpr in

let letInReclet = symbolize (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ureclets_ [
      ("g", ulam_ "y" (bindall_ [
        ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (int_ 1))),
        addi_ (app_ (var_ "h") (var_ "y")) (var_ "x")
      ]))],
    app_ (var_ "g") (int_ 1)
  ])),
  app_ (var_ "f") (int_ 4)]) in
let expected = symbolize (bindall_ [
  ureclets_ [
    ("h", ulam_ "z" (addi_ (var_ "z") (int_ 1))),
    ("g", ulam_ "x" (ulam_ "y" (
    addi_ (app_ (var_ "h") (var_ "y")) (var_ "x"))))],
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 4)]) in
utest liftLambdas letInReclet with expected using eqExpr in

let deepNestedRecursiveDefs = symbolize (ureclets_ [
  ("f1", ulam_ "x" (bindall_ [
    ulet_ "f2" (bindall_ [
      ureclets_ [("f3", ulam_ "x" (addi_ (var_ "x") (int_ 1)))],
      ureclets_ [
        ("f4", ulam_ "y" (bindall_ [
          ulet_ "k" (ulam_ "x" (app_ (var_ "f5") (var_ "x"))),
          addi_ (app_ (var_ "k") (var_ "x")) (var_ "y")])),
        ("f5", ulam_ "x" (subi_ (var_ "x") (int_ 1)))
      ],
      addi_ (app_ (var_ "f3") (var_ "x"))
            (app_ (var_ "f4") (int_ 2))]),
    var_ "f2"]))]) in
let expected = symbolize (bindall_ [
  ureclets_ [("f3", ulam_ "x" (addi_ (var_ "x") (int_ 1)))],
  ureclets_ [
    ("k", ulam_ "x" (app_ (var_ "f5") (var_ "x"))),
    ("f4", ulam_ "x" (ulam_ "y" (addi_ (app_ (var_ "k") (var_ "x")) (var_ "y")))),
    ("f5", ulam_ "x" (subi_ (var_ "x") (int_ 1)))
  ],
  ureclets_ [
    ("f1", ulam_ "x" (bindall_ [
      ulet_ "f2" (addi_ (app_ (var_ "f3") (var_ "x"))
                        (app_ (var_ "f4") (int_ 2))),
      var_ "f2"]))
  ]
]) in
utest liftLambdas deepNestedRecursiveDefs with expected using eqExpr in

let fdef = ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))) in
let fapp = bind_ fdef (app_ (var_ "f") (int_ 1)) in

let liftUtest = symbolize (
  utest_
    (int_ 0)
    fapp
    unit_) in
let expected = symbolize (
  bind_
    fdef
    (utest_
      (int_ 0)
      (app_ (var_ "f") (int_ 1))
      unit_)) in
utest liftLambdas liftUtest with expected using eqExpr in

let liftApp = symbolize (bindall_ [
  app_
    (bind_
      (ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))))
      (app_ (var_ "g") (int_ 2)))
    fapp]) in
let expected = symbolize (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  fdef,
  app_
    (app_ (var_ "g") (int_ 2))
    (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftApp with expected using eqExpr in

let liftSeq = symbolize (seq_ [fapp]) in
let expected = symbolize (bindall_ [fdef, seq_ [app_ (var_ "f") (int_ 1)]]) in
utest liftLambdas liftSeq with expected using eqExpr in

let liftRecord = symbolize (urecord_ [("a", fapp), ("b", int_ 2)]) in
let expected = symbolize (bindall_ [
  fdef,
  urecord_ [
    ("a", app_ (var_ "f") (int_ 1)),
    ("b", int_ 2)]]) in
utest liftLambdas liftRecord with expected using eqExpr in

let liftRecordUpdate = symbolize (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)]),
  recordupdate_ (var_ "r") "b" fapp
  ]) in
let expected = symbolize (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)]),
  fdef,
  recordupdate_ (var_ "r") "b" (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftRecordUpdate with expected using eqExpr in

let liftMatchTarget = symbolize (
  match_ fapp (pint_ 0)
    (int_ 1)
    (int_ 2)) in
let expected = symbolize (bindall_ [
  fdef,
  match_ (app_ (var_ "f") (int_ 1)) (pint_ 0)
    (int_ 1)
    (int_ 2)]) in
utest liftLambdas liftMatchTarget with expected using eqExpr in

let liftMatchThn = symbolize (
  match_ (int_ 3) (pint_ 3)
    fapp
    (int_ 0)) in
let expected = symbolize (bindall_ [
  fdef,
  match_ (int_ 3) (pint_ 3)
    (app_ (var_ "f") (int_ 1))
    (int_ 0)]) in
utest liftLambdas liftMatchThn with expected using eqExpr in

let liftMatchEls = symbolize (
  match_ (int_ 3) (pint_ 3)
    (int_ 0)
    fapp) in
let expected = symbolize (bindall_ [
  fdef,
  match_ (int_ 3) (pint_ 3)
    (int_ 0)
    (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftMatchEls with expected using eqExpr in

let conAppLift = symbolize (bindall_ [
  condef_ "Leaf" (tyarrow_ tyint_ (tyvar_ "Tree")),
  conapp_ "Leaf" fapp
]) in
let expected = symbolize (bindall_ [
  condef_ "Leaf" (tyarrow_ tyint_ (tyvar_ "Tree")),
  fdef,
  conapp_ "Leaf" (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas conAppLift with expected using eqExpr in

let anonymousFunctionLift = symbolize (bindall_ [
  ulet_ "f" (ulam_ "x" (
    app_ (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) (int_ 4))),
  app_ (var_ "f") (int_ 2)]) in
let expected = symbolize (bindall_ [
  ulet_ "t" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "t") (var_ "x") (int_ 4))),
  app_ (var_ "f") (int_ 2)]) in
utest liftLambdas anonymousFunctionLift with expected using eqExpr in

let anonymousMapLift = symbolize (
  map_ (ulam_ "x" (addi_ (var_ "x") (int_ 1))) (seq_ [int_ 0, int_ 7])) in
let expected = symbolize (bindall_ [
  ulet_ "t" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  map_ (var_ "t") (seq_ [int_ 0, int_ 7])]) in
utest liftLambdas anonymousMapLift with expected using eqExpr in

let recursiveSystem = symbolize (bindall_ [
  ulet_ "a" (int_ 1),
  ulet_ "b" (int_ 2),
  ulet_ "c" (int_ 5),
  ureclets_ [
    ("f", ulam_ "x" (addi_ (app_ (var_ "g") (var_ "x")) (var_ "a"))),
    ("g", ulam_ "y" (addi_ (app_ (var_ "h") (var_ "y")) (var_ "b"))),
    ("h", ulam_ "z" (addi_ (app_ (var_ "f") (var_ "z")) (var_ "c")))],
  unit_]) in
let expected = symbolize (bindall_ [
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

()
