-- Implementation of local common subexpression elimination, applied on
-- function and constructor applications.

include "mexpr/anf.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

type CSEApplyEnv = {
  -- Maps an expression to a tuple, containing the name to which it is mapped,
  -- and a boolean determining whether this is the first match or not.
  exprData : Map Expr (Bool, Name),

  -- Keeps track of the expressions with corresponding names that have been
  -- found in the current let-body. This is used to generate let-expressions of
  -- the common subexpressions at a valid position.
  --
  -- As the names are unique, this is a bijective relation between names and
  -- expressions. We map names to expressions as comparison of names is more
  -- efficient.
  found : Map Name Expr
}

lang CSE = MExprCmpClosed
  sem csePropagate =
  | t -> smap_Expr_Expr csePropagate t

  sem cseCount (exprCount : Map Expr Int) =
  | t -> sfold_Expr_Expr cseCount exprCount t

  sem cseApply (env : CSEApplyEnv) =
  | t -> smapAccumL_Expr_Expr cseApply env t

  sem cseApplyMatch (env : CSEApplyEnv) (firstMatch : Bool) (id : Name) =
  | t ->
    let env =
      if firstMatch then
        let exprData = mapInsert t (false, id) env.exprData in
        let found = mapInsert id t env.found in
        {{env with exprData = exprData} with found = found}
      else env
    in
    (env, TmVar {ident = id, ty = ty t, info = infoTm t})

  sem cseBlock =
  | t ->
    -- Count occurrences of subexpressions, to identify common expressions
    let count = cseCount (mapEmpty cmpExpr) t in

    -- Identify the common subexpressions - the subexpressions that are found
    -- more than once in the block.
    let commonExpressions =
      filter
        (lam entry : (Expr, Int). gti entry.1 1)
        (mapBindings count) in

    -- Eliminate common subexpressions by replacing them with a variable and
    -- adding let-expressions for said variables at the beginning of the block.
    let expressionMap =
      mapFromSeq cmpExpr
        (map
          (lam entry : (Expr, Int). (entry.0, (true, nameSym "t")))
          commonExpressions) in
    let env = {exprData = expressionMap, found = mapEmpty nameCmp} in
    match cseApply env t with (_, t) then
      t
    else never

  sem cse =
  | t -> csePropagate t
end

lang AppCSE = CSE + AppAst
  sem cseCount (exprCount : Map Expr Int) =
  | (TmApp t) & app ->
    let default = lam count. cseCount (cseCount count t.lhs) t.rhs in
    match t.ty with TyArrow _ then
      default exprCount
    else
      match mapLookup app exprCount with Some cnt then
        mapInsert app (addi cnt 1) exprCount
      else
        let exprCount = mapInsert app 1 exprCount in
        default exprCount

  sem cseApply (env : CSEApplyEnv) =
  | (TmApp t) & app ->
    match mapLookup app env.exprData with Some (firstMatch, id) then
      cseApplyMatch env firstMatch id app
    else
      match cseApply env t.lhs with (env, lhs) then
        match cseApply env t.rhs with (env, rhs) then
          (env, TmApp {{t with lhs = lhs} with rhs = rhs})
        else never
      else never
end

lang LamCSE = CSE + LamAst
  sem csePropagate =
  | TmLam ({body = !(TmLam _)} & t) ->
    TmLam {t with body = cseBlock t.body}

  sem cseCount (exprCount : Map Expr Int) =
  | TmLam _ -> exprCount

  sem cseApply (env : CSEApplyEnv) =
  | (TmLam _) & t -> (env, t)
end

lang LetCSE = CSE + LetAst
  sem cseApply (env : CSEApplyEnv) =
  | TmLet t ->
    match cseApply env t.body with (env, body) then
      let env : CSEApplyEnv = env in
      let found = env.found in
      let inexprEnv = {env with found = mapEmpty nameCmp} in
      match cseApply inexprEnv t.inexpr with (env, inexpr) then
        let expr =
          mapFoldWithKey
            (lam acc : Expr. lam key : Name. lam value : Expr.
              TmLet {ident = key, tyBody = ty value, body = value, inexpr = acc,
                     ty = ty acc, info = infoTm value})
            (TmLet {{t with body = body} with inexpr = inexpr})
            found in
        (env, expr)
      else never
    else never
end

lang DataCSE = CSE + DataAst
  sem cseCount (exprCount : Map Expr Int) =
  | (TmConApp t) & conapp ->
    match mapLookup conapp exprCount with Some cnt then
      mapInsert conapp (addi cnt 1) exprCount
    else
      let exprCount = mapInsert conapp 1 exprCount in
      cseCount exprCount t.body

  sem cseApply (env : CSEApplyEnv) =
  | (TmConApp t) & conapp ->
    match mapLookup conapp env.exprData with Some (firstMatch, id) then
      cseApplyMatch env firstMatch id conapp
    else
      match cseApply env t.body with (env, body) then
        (env, TmConApp {t with body = body})
      else never
end

lang MatchCSE = CSE + MatchAst
  sem csePropagate =
  | TmMatch t ->
    TmMatch {{t with thn = cseBlock t.thn}
                with els = cseBlock t.els}

  sem cseCount (exprCount : Map Expr Int) =
  | TmMatch {target = target} ->
    mapInsertWith (lam prev. lam. addi prev 1) target 1 exprCount

  sem cseApply (env : CSEApplyEnv) =
  | TmMatch t ->
    match mapLookup t.target env.exprData with Some (firstMatch, id) then
      cseApplyMatch env firstMatch id (TmMatch t)
    else
      match cseApply env t.target with (env, target) then
        (env, TmMatch {t with target = target})
      else never
end

lang MExprCSE = AppCSE + LamCSE + LetCSE + DataCSE + MatchCSE

lang TestLang = MExprCSE + MExprEq + MExprSym + MExprTypeAnnot + MExprPrettyPrint

mexpr

use TestLang in

let preprocess = lam t.
  typeAnnot (symbolize t)
in

recursive let withoutTypes = lam e.
  match e with TmType t then
    withoutTypes t.inexpr
  else e
in

let t = preprocess (
  ulet_ "f" (ulam_ "n" (bindall_ [
    ulet_ "x" (muli_ (int_ 2) (var_ "n")),
    ulet_ "y" (addi_ (int_ 4) (muli_ (int_ 2) (var_ "n"))),
    addi_ (var_ "x") (var_ "y")
  ]))
) in
let expected = preprocess (
  ulet_ "f" (ulam_ "n" (bindall_ [
    ulet_ "t" (muli_ (int_ 2) (var_ "n")),
    ulet_ "x" (var_ "t"),
    ulet_ "y" (addi_ (int_ 4) (var_ "t")),
    addi_ (var_ "x") (var_ "y")
  ]))
) in
utest cse t with expected using eqExpr in
utest cse expected with expected using eqExpr in

let t = preprocess (bindall_ [
  type_ "Num" tyunknown_,
  condef_ "CInt" (tyarrow_ tyint_ (tyvar_ "Num")),
  ulam_ "" (bindall_ [
    ulet_ "x" (int_ 4),
    ulet_ "y" (conapp_ "CInt" (var_ "x")),
    ulet_ "z" (conapp_ "CInt" (var_ "x")),
    var_ "y"
  ])
]) in
let expected = preprocess (bindall_ [
  type_ "Num" tyunknown_,
  condef_ "CInt" (tyarrow_ tyint_ (tyvar_ "Num")),
  ulam_ "" (bindall_ [
    ulet_ "x" (int_ 4),
    ulet_ "t" (conapp_ "CInt" (var_ "x")),
    ulet_ "y" (var_ "t"),
    ulet_ "z" (var_ "t"),
    var_ "y"
  ])
]) in
-- NOTE(larshum, 2021-07-09): Remove the type declarations before utests
-- because eqExpr has not been implemented for TmType.
let result = withoutTypes (cse t) in
let expected = withoutTypes expected in
utest result with expected using eqExpr in
utest cse expected with expected using eqExpr in

-- Common expressions in different branches are not eliminated
let branches = preprocess (ureclets_ [
  ("f", ulam_ "p" (ulam_ "s" (bindall_ [
    ulet_ "h" (head_ (var_ "s")),
    if_ (app_ (var_ "p") (var_ "h"))
      (cons_ (var_ "h") (appf2_ (var_ "f") (var_ "p") (tail_ (var_ "s"))))
      (appf2_ (var_ "f") (var_ "p") (tail_ (var_ "s")))
  ])))
]) in
utest cse branches with branches using eqExpr in

let t = preprocess (ulam_ "" (bindall_ [
  ulet_ "x" (addi_ (int_ 2) (int_ 3)),
  ulet_ "y" (addi_ (var_ "x") (int_ 1)),
  ulet_ "z" (muli_ (int_ 2) (addi_ (var_ "x") (int_ 1))),
  addi_ (var_ "y") (var_ "z")
])) in
let expected = preprocess (ulam_ "" (bindall_ [
  ulet_ "x" (addi_ (int_ 2) (int_ 3)),
  ulet_ "t" (addi_ (var_ "x") (int_ 1)),
  ulet_ "y" (var_ "t"),
  ulet_ "z" (muli_ (int_ 2) (var_ "t")),
  addi_ (var_ "y") (var_ "z")
])) in
utest cse t with expected using eqExpr in
utest cse expected with expected using eqExpr in

-- Partial applications are not eliminated (muli 2 _)
let partial = preprocess (ulam_ "" (bindall_ [
  ulet_ "x" (muli_ (int_ 2) (int_ 3)),
  ulet_ "y" (muli_ (int_ 2) (var_ "x")),
  muli_ (var_ "x") (var_ "y")
])) in
utest cse partial with partial using eqExpr in

()
