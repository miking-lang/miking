-- Implementation of global common subexpression elimination. Assumes that the
-- AST has been symbolized, annotated with types, and does not contain any
-- side-effects.

include "math.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/type-check.mc"
include "mexpr/pprint.mc"

type PosIndex = Int
type ProgramPos = [PosIndex]

-- Finds the longest common prefix of two program positions.
let programPosLCP : ProgramPos -> ProgramPos -> ProgramPos =
  lam t1. lam t2.
  -- We use binary search to find the longest common prefix for which both
  -- sequences have the same positional indices.
  recursive let binarySearch : Int -> Int -> ProgramPos = lam lo. lam hi.
    if geqi (addi lo 1) hi then subsequence t1 0 hi
    else
      let mid = addi (divi (subi hi lo) 2) lo in
      if eqi (get t1 mid) (get t2 mid) then
        binarySearch mid hi
      else binarySearch lo mid
  in
  let hi = mini (length t1) (length t2) in
  if gti hi 0 then
    if eqi (head t1) (head t2) then
      binarySearch 0 hi
    else []
  else []

type ExprStatus
con Once : ProgramPos -> ExprStatus
con Multiple : ProgramPos -> ExprStatus

type CSESearchEnv = use Ast in {
  index : PosIndex,
  subexprs : Map Expr ExprStatus,
  recursiveIdents : Set Name
}

type CSEApplyEnv = use Ast in {
  index : PosIndex,
  posToSubexpr : Map PosIndex [(Name, Expr)],
  exprIdent : Map Expr Name
}

lang CSE = MExprCmp
  sem insertSubexpressionDeclarations (env : CSEApplyEnv) =
  | t /- : Expr -/ ->
    optionGetOrElse
      (lam. t)
      (optionMap
        (lam exprs : [(Name, Expr)].
          foldl
            (lam acc. lam namedExpr : (Name, Expr).
              match namedExpr with (id, e) then
                TmLet {ident = id, tyAnnot = tyTm e, tyBody = tyTm e,
                       body = e, inexpr = acc, ty = tyTm acc, info = infoTm e}
              else never)
            t
            exprs)
        (mapLookup env.index env.posToSubexpr))

  sem cseCount (pos : ProgramPos) (env : CSESearchEnv) =
  | t ->
    let opt = mapLookup t env.subexprs in
    let env =
      match opt with None () then
        -- Subexpression found for the first time
        {env with subexprs = mapInsert t (Once pos) env.subexprs}
      else match opt with Some (Once prevPos | Multiple prevPos) then
        -- Subexpression found at least once
        let newPos = Multiple (programPosLCP prevPos pos) in
        {env with subexprs = mapInsert t newPos env.subexprs}
      else never
    in
    sfold_Expr_Expr (cseSearch pos) env t

  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | t -> sfold_Expr_Expr (cseSearch pos) env t

  sem cseSearch (pos : ProgramPos) (env : CSESearchEnv) =
  | t -> cseSearchH pos {env with index = addi env.index 1} t

  sem cseReplace (env : CSEApplyEnv) =
  | t ->
    match mapLookup t env.exprIdent with Some ident then
      (env, TmVar {ident = ident, ty = tyTm t, info = infoTm t, frozen = false})
    else smapAccumL_Expr_Expr cseApply env t

  sem cseApplyH (env : CSEApplyEnv) =
  | t -> smapAccumL_Expr_Expr cseApply env t

  sem cseApply (env : CSEApplyEnv) =
  | t -> cseApplyH {env with index = addi env.index 1} t

  sem cse =
  | t ->
    let emptySearchEnv = {
      index = 0,
      subexprs = mapEmpty cmpExpr,
      recursiveIdents = setEmpty nameCmp
    } in
    let initialApplyEnv = {
      index = 0,
      posToSubexpr = mapEmpty subi,
      exprIdent = mapEmpty cmpExpr
    } in
    let searchEnv : CSESearchEnv = cseSearch [] emptySearchEnv t in
    let applyEnv : CSEApplyEnv =
      foldl
        (lam applyEnv : CSEApplyEnv. lam exprEntry : (Expr, ExprStatus).
          -- Ignore expressions that are only used once.
          match exprEntry with (_, Once _) then applyEnv
          else match exprEntry with (expr, Multiple pos) then
            let tempId = nameSym "t" in
            let index = match pos with _ ++ [x] then x else 0 in
            let posToSubexpr = mapInsertWith concat index [(tempId, expr)]
                                             applyEnv.posToSubexpr in
            {{applyEnv with posToSubexpr = posToSubexpr}
                       with exprIdent = mapInsert expr tempId applyEnv.exprIdent}
          else never)
        initialApplyEnv
        (mapBindings searchEnv.subexprs) in
    match cseApply applyEnv t with (env, t) then
      insertSubexpressionDeclarations applyEnv t
    else never
end

lang AppCSE = CSE + AppAst
  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | app & (TmApp t) ->
    match t.ty with TyArrow _ then
      sfold_Expr_Expr (cseSearch pos) env app
    else match t.lhs with TmVar {ident = ident} then
      if mapMem ident env.recursiveIdents then env
      else cseCount pos env app
    else cseCount pos env app

  sem cseApplyH (env : CSEApplyEnv) =
  | app & (TmApp _) -> cseReplace env app
end

lang LamCSE = CSE + LamAst
  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | TmLam t ->
    let pos = snoc pos env.index in
    cseSearch pos env t.body

  sem cseApplyH (env : CSEApplyEnv) =
  | TmLam t ->
    match cseApply env t.body with (acc, body) then
      let body = insertSubexpressionDeclarations env body in
      (acc, TmLam {t with body = body})
    else never
end

lang LetCSE = CSE + LetAst
  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | TmLet t ->
    let env : CSESearchEnv = cseSearch pos env t.body in
    let inexprPos = snoc pos env.index in
    cseSearch inexprPos env t.inexpr

  sem cseApplyH (env : CSEApplyEnv) =
  | TmLet t ->
    match cseApply env t.body with (thnEnv, body) then
      match cseApply thnEnv t.inexpr with (env, inexpr) then
        let inexpr = insertSubexpressionDeclarations thnEnv inexpr in
        (env, TmLet {{t with body = body}
                        with inexpr = inexpr})
      else never
    else never
end

lang RecLetsCSE = CSE + RecLetsAst
  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | TmRecLets t ->
    let recursiveIdents =
      foldl
        (lam acc. lam binding : RecLetBinding. setInsert binding.ident acc)
        env.recursiveIdents
        t.bindings in
    let bindEnv =
      foldl
        (lam acc. lam binding : RecLetBinding.
          cseSearch pos acc binding.body)
        {env with recursiveIdents = recursiveIdents}
        t.bindings in
    cseSearch pos bindEnv t.inexpr

  sem cseApplyH (env : CSEApplyEnv) =
  | TmRecLets t ->
    let applyBinding : CSEApplyEnv -> RecLetBinding
                    -> (CSEApplyEnv, RecLetBinding) =
      lam env. lam binding.
      match cseApply env binding.body with (env, body) then
        (env, {binding with body = body})
      else never
    in
    match mapAccumL applyBinding env t.bindings with (inexprEnv, bindings) then
      match cseApply inexprEnv t.inexpr with (env, inexpr) then
        let inexpr = insertSubexpressionDeclarations inexprEnv inexpr in
        (env, TmRecLets {{t with bindings = bindings} with inexpr = inexpr})
      else never
    else never
end

lang MatchCSE = CSE + MatchAst
  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | TmMatch t ->
    let env : CSESearchEnv = cseSearch pos env t.target in
    let thnPos = snoc pos env.index in
    let env : CSESearchEnv = cseSearch thnPos env t.thn in
    let elsPos = snoc pos env.index in
    cseSearch elsPos env t.els

  sem cseApplyH (env : CSEApplyEnv) =
  | TmMatch t ->
    match cseApply env t.target with (thnEnv, target) then
      match cseApply thnEnv t.thn with (elsEnv, thn) then
        let thn = insertSubexpressionDeclarations thnEnv thn in
        match cseApply elsEnv t.els with (env, els) then
          let els = insertSubexpressionDeclarations elsEnv els in
          (env, TmMatch {{{t with target = target}
                             with thn = thn}
                             with els = els})
        else never
      else never
    else never
end

lang RecordCSE = CSE + RecordAst
  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | record & (TmRecord _) -> cseCount pos env record

  sem cseApplyH (env : CSEApplyEnv) =
  | record & (TmRecord _) -> cseReplace env record
end

lang DataCSE = CSE + DataAst
  sem cseSearchH (pos : ProgramPos) (env : CSESearchEnv) =
  | conApp & (TmConApp _) -> cseCount pos env conApp

  sem cseApplyH (env : CSEApplyEnv) =
  | conApp & (TmConApp _) -> cseReplace env conApp
end

lang MExprCSE =
  AppCSE + LamCSE + LetCSE + RecLetsCSE + MatchCSE + RecordCSE + DataCSE

  -- Runs CSE on the body of a function. That is, if it is an expression
  -- wrapped inside a sequence of lambda terms.
  sem cseFunction (inLambda : Bool) =
  | TmLam t ->
    TmLam {t with body = cseFunction true t.body}
  | t -> if inLambda then cse t else t

  -- Runs CSE globally within the body of each top-level function.
  sem cseGlobal =
  | TmLet t ->
    TmLet {{t with body = cseFunction false t.body}
              with inexpr = cseGlobal t.inexpr}
  | TmRecLets t ->
    let bindings =
      map
        (lam bind : RecLetBinding.
          {bind with body = cseFunction false bind.body})
        t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = cseGlobal t.inexpr}
  | TmType t -> TmType {t with inexpr = cseGlobal t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = cseGlobal t.inexpr}
  | TmUtest t -> TmUtest {t with next = cseGlobal t.next}
  | TmExt t -> TmExt {t with inexpr = cseGlobal t.inexpr}
  | t -> t
end

lang TestLang = MExprCSE + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint end

mexpr

use TestLang in

recursive let withoutTypes = lam e.
  match e with TmType t then
    withoutTypes t.inexpr
  else e
in

let preprocess = lam t.
  withoutTypes (typeCheck (symbolize t))
in
let commonExpr = addi_ (int_ 2) (int_ 2) in

let t = preprocess (bindall_ [
  ulet_ "x" (ulam_ "a" (muli_ commonExpr commonExpr)),
  ureclets_ [
    ("x", ulam_ "a" (muli_ commonExpr commonExpr)),
    ("x", ulam_ "a" commonExpr)],
  ulet_ "x" (muli_ commonExpr commonExpr),
  ulet_ "x" (ulam_ "a" commonExpr),
  unit_
]) in
let expected = preprocess (bindall_ [
  ulet_ "x" (ulam_ "a" (
    bind_ (ulet_ "t" commonExpr) (muli_ (var_ "t") (var_ "t")))),
  ureclets_ [
    ("x", ulam_ "a" (bind_ (ulet_ "t" commonExpr) (muli_ (var_ "t") (var_ "t")))),
    ("x", ulam_ "a" commonExpr)],
  ulet_ "x" (muli_ commonExpr commonExpr),
  ulet_ "x" (ulam_ "a" commonExpr),
  unit_
]) in
utest cseGlobal t with expected using eqExpr in

let t = preprocess (muli_ commonExpr commonExpr) in
let expected = preprocess (bindall_ [
  ulet_ "t" commonExpr,
  muli_ (var_ "t") (var_ "t")]) in
utest cse t with expected using eqExpr in

let t = preprocess (ulet_ "x" (muli_ commonExpr commonExpr)) in
let expected = preprocess (bindall_ [
  ulet_ "t" commonExpr,
  ulet_ "x" (muli_ (var_ "t") (var_ "t"))]) in
utest cse t with expected using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "x" (muli_ commonExpr commonExpr),
  ulet_ "y" (addi_ commonExpr commonExpr),
  addi_ (var_ "x") (var_ "y")]) in
let expected = preprocess (bindall_ [
  ulet_ "t" commonExpr,
  ulet_ "x" (muli_ (var_ "t") (var_ "t")),
  ulet_ "y" (addi_ (var_ "t") (var_ "t")),
  addi_ (var_ "x") (var_ "y")]) in
utest cse t with expected using eqExpr in

let t = preprocess (ureclets_ [
  ("a", ulam_ "x" (addi_ (muli_ (var_ "x") commonExpr) commonExpr))]) in
let expected = preprocess (ureclets_ [
    ("a", ulam_ "x" (bindall_ [
      ulet_ "t" commonExpr,
      addi_ (muli_ (var_ "x") (var_ "t")) (var_ "t")]))]) in
utest cse t with expected using eqExpr in

let t = preprocess (
  if_ (eqi_ (int_ 0) (int_ 0))
    (muli_ commonExpr commonExpr)
    (int_ 0)) in
let expected = preprocess (if_ (eqi_ (int_ 0) (int_ 0))
    (bind_ (ulet_ "t" commonExpr) (muli_ (var_ "t") (var_ "t")))
    (int_ 0)) in
utest cse t with expected using eqExpr in

let t = preprocess (
  if_ (eqi_ (int_ 0) (int_ 0))
    (muli_ commonExpr commonExpr)
    (addi_ commonExpr commonExpr)) in
let expected = preprocess (bindall_ [
  ulet_ "t" commonExpr,
  if_ (eqi_ (int_ 0) (int_ 0))
    (muli_ (var_ "t") (var_ "t"))
    (addi_ (var_ "t") (var_ "t"))]) in
utest cse t with expected using eqExpr in

let t = preprocess (
  if_ (eqi_ (subi_ commonExpr commonExpr) (int_ 0))
    (int_ 1)
    (int_ 2)) in
let expected = preprocess (bindall_ [
  ulet_ "t" commonExpr,
  if_ (eqi_ (subi_ (var_ "t") (var_ "t")) (int_ 0))
    (int_ 1)
    (int_ 2)]) in
utest cse t with expected using eqExpr in

-- Partial applications are not eliminated (in this case, 'muli 2 _')
let t = preprocess (bindall_ [
  ulet_ "x" (muli_ (int_ 2) (int_ 3)),
  ulet_ "y" (muli_ (int_ 2) (int_ 4)),
  addi_ (var_ "x") (var_ "y")]) in
utest cse t with t using eqExpr in

let t = preprocess (bindall_ [
  type_ "Num" [] (tyvariant_ []),
  condef_ "CInt" (tyarrow_ tyint_ (tycon_ "Num")),
  ulet_ "x" (int_ 4),
  ulet_ "y" (conapp_ "CInt" (var_ "x")),
  ulet_ "z" (conapp_ "CInt" (var_ "x")),
  var_ "y",
  uunit_
]) in
let expected = preprocess (bindall_ [
  type_ "Num" [] (tyvariant_ []),
  condef_ "CInt" (tyarrow_ tyint_ (tycon_ "Num")),
  ulet_ "x" (int_ 4),
  ulet_ "t" (conapp_ "CInt" (var_ "x")),
  ulet_ "y" (var_ "t"),
  ulet_ "z" (var_ "t"),
  var_ "y",
  uunit_
]) in
utest cse t with expected using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "x" (urecord_ [("a", int_ 1), ("b", char_ 'x')]),
  ulet_ "y" (urecord_ [("b", char_ 'x'), ("a", int_ 1)]),
  unit_
]) in
let expected = preprocess (bindall_ [
  ulet_ "t" (urecord_ [("a", int_ 1), ("b", char_ 'x')]),
  ulet_ "x" (var_ "t"),
  ulet_ "y" (var_ "t"),
  unit_
]) in
utest cse t with expected using eqExpr in

let t = preprocess (ulam_ "a" (ulam_ "b" (
  match_ (utuple_ [var_ "a", var_ "b"])
    (ptuple_ [pint_ 1, pvarw_])
    (int_ 2)
    (match_ (utuple_ [var_ "a", var_ "b"])
      (ptuple_ [pvarw_, pint_ 1])
      (int_ 1)
      (int_ 3))))) in
let expected = preprocess (ulam_ "a" (ulam_ "b" (bindall_ [
  ulet_ "t" (utuple_ [var_ "a", var_ "b"]),
  match_ (var_ "t")
    (ptuple_ [pint_ 1, pvarw_])
    (int_ 2)
    (match_ (var_ "t")
      (ptuple_ [pvarw_, pint_ 1])
      (int_ 1)
      (int_ 3))]))) in
utest cse t with expected using eqExpr in

let t = preprocess (bindall_ [
  ureclets_ [("f", ulam_ "x" commonExpr)],
  commonExpr]) in
let expected = preprocess (bindall_ [
  ulet_ "t" commonExpr,
  ureclets_ [("f", ulam_ "x" (var_ "t"))],
  var_ "t"]) in
utest cse t with expected using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "k" commonExpr,
  ureclets_ [("f", ulam_ "x" commonExpr)],
  unit_
]) in
let expected = preprocess (bindall_ [
  ulet_ "t" commonExpr,
  ulet_ "k" (var_ "t"),
  ureclets_ [("f", ulam_ "x" (var_ "t"))],
  unit_
]) in
utest cse t with expected using eqExpr in

let t = preprocess (
  if_ true_
    (bind_
       (ulet_ "x"
          (if_ true_
             unit_
             unit_))
    (int_ 0))
    (if_ true_
      commonExpr
      commonExpr)) in
let expected = preprocess (if_ true_
  (bindall_ [
    ulet_ "t" unit_,
    ulet_ "x"
      (if_ true_
         (var_ "t")
         (var_ "t")),
    int_ 0
  ])
  (bindall_ [
    ulet_ "t" commonExpr,
    (if_ true_
      (var_ "t")
      (var_ "t"))])) in
utest cse t with expected using eqExpr in

-- Ignore subexpressions that are applications of recursive bindings
let t = preprocess (bindall_ [
  ureclets_ [
    ("f", ulam_ "x" (var_ "x"))
  ],
  ulet_ "x" (app_ (var_ "f") (int_ 3)),
  ulet_ "y" (app_ (var_ "f") (int_ 3)),
  unit_]) in
utest cse t with t using eqExpr in

()
