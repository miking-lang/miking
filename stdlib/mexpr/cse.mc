-- Implementation of global common subexpression elimination. Assumes that the
-- AST has been symbolized, annotated with types, and does not contain any
-- side-effects.

include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/type-annot.mc"

type Pos
con AfterIdent : Name -> Pos
con RecIdent : Name -> Pos
con AfterRec : () -> Pos
con MatchThn : () -> Pos
con MatchEls : () -> Pos

recursive let cmpPos : Pos -> Pos -> Int =
  lam p1. lam p2.
  let t = (p1, p2) in
  match t with (AfterIdent n1, AfterIdent n2) then nameCmp n1 n2
  else match t with (RecIdent n1, RecIdent n2) then nameCmp n1 n2
  else subi (constructorTag p1) (constructorTag p2)
end

let eqPos : Pos -> Pos -> Bool = lam p1. lam p2. eqi (cmpPos p1 p2) 0

type ProgramPos = [Pos]

let initialProgramPos = []

let cmpProgramPos : ProgramPos -> ProgramPos -> Int =
  lam l. lam r. seqCmp cmpPos l r

type ExprStatus
con Once : ProgramPos -> ExprStatus
con Multiple : ProgramPos -> ExprStatus
con Ineligible : ProgramPos -> ExprStatus

type CSESearchEnv = {
  currentPos : ProgramPos,
  subexprs : Map Expr ExprStatus
}

let emptySearchEnv = {
  currentPos = initialProgramPos,
  subexprs = use MExprCmp in mapEmpty cmpExpr
}

type CSEApplyEnv = {
  currentPos : ProgramPos,
  insertAtPos : Map ProgramPos [(Name, Expr)],
  exprIdent : Map Expr Name
}

let initApplyEnv = {
  currentPos = initialProgramPos,
  insertAtPos = mapEmpty cmpProgramPos,
  exprIdent = use MExprCmp in mapEmpty cmpExpr
}

recursive let mergeProgramPositions : ProgramPos -> ProgramPos
                                   -> Option ProgramPos =
  lam prevPos. lam newPos.
  let t = (prevPos, newPos) in
  match t with ([], []) then Some []
  else match t with ([h1] ++ t1, [h2] ++ t2) then
    match (h1, h2) with (AfterIdent n1, AfterIdent _) then
      optionMap
        (lam pos. cons (AfterIdent n1) pos)
        (mergeProgramPositions t1 t2)
    else match (h1, h2) with (MatchThn _, MatchEls _) |
                             (MatchEls _, MatchThn _) then
      Some []
    else match (h1, h2) with (RecIdent n1, RecIdent n2) then
      if nameEq n1 n2 then
        optionMap
          (lam pos. cons (RecIdent n1) pos)
          (mergeProgramPositions t1 t2)
      else None ()
    else if eqPos h1 h2 then
      optionMap
        (lam pos. cons h1 pos)
        (mergeProgramPositions t1 t2)
    else None ()
  else match t with ([RecIdent _] ++ _, []) then
    None ()
  else Some []
end

let insertSubexpressionDeclarations : CSEApplyEnv -> Expr -> Expr =
  use MExprAst in
  lam env. lam t.
  optionGetOrElse
    (lam. t)
    (optionMap
      (lam exprs : [(Name, Expr)].
        foldl
          (lam acc. lam namedExpr : (Name, Expr).
            match namedExpr with (id, e) then
              TmLet {ident = id, tyBody = ty e, body = e, inexpr = acc,
                     ty = ty acc, info = infoTm e}
            else never)
          t
          exprs)
      (mapLookup env.currentPos env.insertAtPos))

lang CSE = MExprCmp
  sem cseCount (env : CSESearchEnv) =
  | t ->
    let opt = mapLookup t env.subexprs in
    let env =
      match opt with None () then
        -- Subexpression found for the first time
        {env with subexprs = mapInsert t (Once env.currentPos) env.subexprs}
      else match opt with Some (Once pos | Multiple pos) then
        -- Subexpression found more than once
        let newPos =
          optionGetOrElse
            (lam. Ineligible ())
            (optionMap
              (lam newPos. Multiple newPos)
              (mergeProgramPositions pos env.currentPos)) in
        {env with subexprs = mapInsert t newPos env.subexprs}
      else match opt with Some (Ineligible ()) then
        -- Subexpression cannot be moved to common position
        env
      else never
    in
    sfold_Expr_Expr cseSearch env t

  sem cseSearch (env : CSESearchEnv) =
  | t -> sfold_Expr_Expr cseSearch env t

  sem cseReplace (env : CSEApplyEnv) =
  | t ->
    match mapLookup t env.exprIdent with Some ident then
      TmVar {ident = ident, ty = ty t, info = infoTm t}
    else smap_Expr_Expr (cseApply env) t

  sem cseApply (env : CSEApplyEnv) =
  | t -> smap_Expr_Expr (cseApply env) t

  sem cseH (searchEnv : CSESearchEnv) =
  | t ->
    let searchEnv : CSESearchEnv = cseSearch searchEnv t in
    let applyEnv : CSEApplyEnv =
      foldl
        (lam applyEnv : CSEApplyEnv. lam exprEntry : (Expr, ExprStatus).
          -- Ignore expression if it is only used once or if it cannot be
          -- turned into a common subexpression for some other reason.
          match exprEntry with (_, Ineligible _ | Once _) then applyEnv
          else match exprEntry with (expr, Multiple pos) then
            let tempId = nameSym "t" in
            let insertAtPos = mapInsertWith concat pos [(tempId, expr)]
                                            applyEnv.insertAtPos in
            {{applyEnv with insertAtPos = insertAtPos}
                       with exprIdent = mapInsert expr tempId applyEnv.exprIdent}
          else never)
        initApplyEnv
        (mapBindings searchEnv.subexprs) in
    let t = cseApply applyEnv t in
    insertSubexpressionDeclarations applyEnv t

  sem cse =
  | t -> cseH emptySearchEnv t
end

lang AppCSE = CSE + AppAst
  sem cseSearch (env : CSESearchEnv) =
  | (TmApp t) & app ->
    match t.ty with TyArrow _ then
      sfold_Expr_Expr cseSearch env app
    else cseCount env app

  sem cseApply (env : CSEApplyEnv) =
  | (TmApp _) & app -> cseReplace env app
end

lang LamCSE = CSE + LamAst
  sem cseSearch (env : CSESearchEnv) =
  | TmLam t ->
    let bodyPos = snoc env.currentPos (AfterIdent t.ident) in
    let env = {env with currentPos = bodyPos} in
    cseSearch env t.body

  sem cseApply (env : CSEApplyEnv) =
  | TmLam t ->
    let newPos = snoc env.currentPos (AfterIdent t.ident) in
    let bodyEnv = {env with currentPos = newPos} in
    let body = cseApply bodyEnv t.body in
    TmLam {t with body = insertSubexpressionDeclarations bodyEnv body}
end

lang LetCSE = CSE + LetAst
  sem cseSearch (env : CSESearchEnv) =
  | TmLet t ->
    let env : CSESearchEnv = cseSearch env t.body in
    let inexprPos = snoc env.currentPos (AfterIdent t.ident) in
    let env = {env with currentPos = inexprPos} in
    cseSearch env t.inexpr

  sem cseApply (env : CSEApplyEnv) =
  | TmLet t ->
    let body = cseApply env t.body in
    let inexprPos = snoc env.currentPos (AfterIdent t.ident) in
    let inexprEnv = {env with currentPos = inexprPos} in
    let inexpr = cseApply inexprEnv t.inexpr in
    TmLet {{t with body = body}
              with inexpr = insertSubexpressionDeclarations inexprEnv inexpr}
end

lang RecLetsCSE = CSE + RecLetsAst
  sem cseSearch (env : CSESearchEnv) =
  | TmRecLets t ->
    let bindEnv : CSESearchEnv =
      foldl
        (lam acc. lam bind : RecLetBinding.
          let bindingPos = snoc env.currentPos (RecIdent bind.ident) in
          cseSearch {acc with currentPos = bindingPos} bind.body)
        env t.bindings in
    let inexprPos = snoc env.currentPos (AfterRec ()) in
    let inexprEnv = {bindEnv with currentPos = inexprPos} in
    cseSearch inexprEnv t.inexpr

  sem cseApply (env : CSEApplyEnv) =
  | TmRecLets t ->
    let bindings =
      map
        (lam bind : RecLetBinding.
          let bindPos = snoc env.currentPos (RecIdent bind.ident) in
          let env = {env with currentPos = bindPos} in
          {bind with body = cseApply env bind.body})
        t.bindings in
    let inexprPos = snoc env.currentPos (AfterRec ()) in
    let inexprEnv = {env with currentPos = inexprPos} in
    let inexpr = insertSubexpressionDeclarations inexprEnv t.inexpr in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = inexpr}
end

lang MatchCSE = CSE + MatchAst
  sem cseSearch (env : CSESearchEnv) =
  | TmMatch t ->
    let env : CSESearchEnv = cseSearch env t.target in
    let thnPos = snoc env.currentPos (MatchThn ()) in
    let thnEnv : CSESearchEnv = {env with currentPos = thnPos} in
    let thnEnv : CSESearchEnv = cseSearch thnEnv t.thn in
    let elsPos = snoc env.currentPos (MatchEls ()) in
    let elsEnv = {thnEnv with currentPos = elsPos} in
    cseSearch elsEnv t.els

  sem cseApply (env : CSEApplyEnv) =
  | TmMatch t ->
    let thnPos = snoc env.currentPos (MatchThn ()) in
    let thnEnv = {env with currentPos = thnPos} in
    let elsPos = snoc env.currentPos (MatchEls ()) in
    let elsEnv = {env with currentPos = elsPos} in
    let thn = insertSubexpressionDeclarations thnEnv (cseApply thnEnv t.thn) in
    let els = insertSubexpressionDeclarations elsEnv (cseApply elsEnv t.els) in
    TmMatch {{{t with target = cseApply env t.target}
                 with thn = thn}
                 with els = els}
end

lang RecordCSE = CSE + RecordAst
  sem cseSearch (env : CSESearchEnv) =
  | (TmRecord _) & record -> cseCount env record

  sem cseApply (env : CSEApplyEnv) =
  | (TmRecord _) & record -> cseReplace env record
end

lang DataCSE = CSE + DataAst
  sem cseSearch (env : CSESearchEnv) =
  | (TmConApp _) & conApp -> cseCount env conApp

  sem cseApply (env : CSEApplyEnv) =
  | (TmConApp _) & conApp -> cseReplace env conApp
end

lang MExprCSE =
  AppCSE + LamCSE + LetCSE + RecLetsCSE + MatchCSE + RecordCSE + DataCSE +
  TypeAst + UtestAst + ExtAst

  -- Runs CSE on the expression only if it is a function, that is, if it is an
  -- expression wrapped in a sequence of lambdas.
  sem cseFunction (foundLambda : Bool) =
  | TmLam t ->
    TmLam {t with body = cseFunction true t.body}
  | t ->
    -- Only run CSE on the term if it is wrapped in a lambda.
    if foundLambda then cse t else t

  -- Performs global CSE by applying the algorithm on the bodies of all
  -- functions defined on the top-level of the given expression.
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

lang TestLang = MExprCSE + MExprEq + MExprSym + MExprTypeAnnot

mexpr

use TestLang in
use MExprPrettyPrint in

recursive let withoutTypes = lam e.
  match e with TmType t then
    withoutTypes t.inexpr
  else e
in

let preprocess = lam t.
  withoutTypes (typeAnnot (symbolize t))
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
  type_ "Num" tyunknown_,
  condef_ "CInt" (tyarrow_ tyint_ (tyvar_ "Num")),
  ulet_ "x" (int_ 4),
  ulet_ "y" (conapp_ "CInt" (var_ "x")),
  ulet_ "z" (conapp_ "CInt" (var_ "x")),
  var_ "y"]) in
let expected = preprocess (bindall_ [
  type_ "Num" tyunknown_,
  condef_ "CInt" (tyarrow_ tyint_ (tyvar_ "Num")),
  ulet_ "x" (int_ 4),
  ulet_ "t" (conapp_ "CInt" (var_ "x")),
  ulet_ "y" (var_ "t"),
  ulet_ "z" (var_ "t"),
  var_ "y"]) in
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
  commonExpr
]) in
utest cse t with t using eqExpr in

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

()
