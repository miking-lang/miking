/-

  This file contains a naive implementation of constant folding.

  OPT(oerikss, 2023-05-16): The time complexity if this implementation is bad.

  NOTE(oerikss, 2023-05-16): The implementation relies on side-effect.mc to
                             handle side-effects. That implementatio is not well
                             tested so be aware if folding code with
                             side-effects.

 -/

include "log.mc"

include "ast.mc"
include "eval.mc"
include "pprint.mc"
include "boot-parser.mc"
include "side-effect.mc"

lang ConstantFoldCtx = Ast + SideEffect
  type VarCount = Map Name Int
  type ConstantFoldCtx = {
    _vars : VarCount,
    _env : Map Name Expr,
    sideEffectEnv : SideEffectEnv
  }

  sem constantfoldCtxEmpty : () -> ConstantFoldCtx
  sem constantfoldCtxEmpty =| _ ->
    {
      _vars = mapEmpty nameCmp,
      _env = mapEmpty nameCmp,
      sideEffectEnv = sideEffectEnvEmpty ()
    }

  sem constantfoldCtxReset : ConstantFoldCtx -> ConstantFoldCtx
  sem constantfoldCtxReset =| ctx ->
    { ctx with _vars = mapEmpty nameCmp, _env = mapEmpty nameCmp }

  sem constantfoldVarCount : Name -> ConstantFoldCtx -> Int
  sem constantfoldVarCount id =| ctx ->
    match mapLookup id ctx._vars with Some n then n else 0

  sem constantfoldVarCountIncr : Name -> ConstantFoldCtx -> ConstantFoldCtx
  sem constantfoldVarCountIncr id =| ctx ->
    let _vars =
      if mapMem id ctx._vars then
        mapInsert id (addi (mapFindExn id ctx._vars) 1) ctx._vars
      else mapInsert id 1 ctx._vars
    in
    { ctx with _vars = _vars }

  sem constantfoldVarCountDecr : Name -> ConstantFoldCtx -> ConstantFoldCtx
  sem constantfoldVarCountDecr id =| ctx ->
    let _vars =
      switch mapLookup id ctx._vars
      case Some 1 then mapRemove id ctx._vars
      case Some n then mapInsert id (subi n 1) ctx._vars
      case None _ then ctx._vars
      end
    in
    { ctx with _vars = _vars }

  sem constantfoldEnvInsert : Name -> Expr -> ConstantFoldCtx -> ConstantFoldCtx
  sem constantfoldEnvInsert id t =| ctx ->
    { ctx with _env = mapInsert id t ctx._env }

  sem constantfoldEnvLookup : Name -> ConstantFoldCtx -> Option Expr
  sem constantfoldEnvLookup id =| ctx -> mapLookup id ctx._env

  sem constantfoldEnvIsEmpty : ConstantFoldCtx -> Bool
  sem constantfoldEnvIsEmpty =| ctx -> mapIsEmpty ctx._env
end

lang ConstantFold = ConstantFoldCtx + MExprSideEffect + MExprPrettyPrint
  sem _constantfoldExpr : ConstantFoldCtx -> Expr -> Expr
  sem _constantfoldExpr ctx =| t ->
    let t = innermost (optimizeOnce ctx) t in
    -- logMsg logLevel.debug (lam. join ["innermost:\n", expr2str t]);
    let ctx = updateCtx (constantfoldCtxReset ctx) t in
    if constantfoldEnvIsEmpty ctx then t
    else _constantfoldExpr ctx t

  sem constantfoldExpr : ConstantFoldCtx -> Expr -> Expr
  sem constantfoldExpr ctx =| t ->
    let ctx = { ctx with sideEffectEnv = constructSideEffectEnv t } in
    let ctx = updateCtx (constantfoldCtxReset ctx) t in
    _constantfoldExpr ctx t

  sem constantfold : Expr -> Expr
  sem constantfold =| t -> constantfoldExpr (constantfoldCtxEmpty ()) t

  sem updateCtx : ConstantFoldCtx -> Expr -> ConstantFoldCtx
  sem updateCtx ctx =
  | t -> sfold_Expr_Expr updateCtx ctx t

  sem innermost : (Expr -> Option Expr) -> Expr -> Expr
  sem innermost f =| t1 ->
    let t2 = smap_Expr_Expr (innermost f) t1 in
    switch f t2
    case Some t3 then innermost f t3
    case None _ then t2
    end

  sem optimizeOnce : ConstantFoldCtx -> Expr -> Option Expr
  sem optimizeOnce ctx =| _ -> None ()
end

lang VarConstantFold = ConstantFold + VarAst
  sem optimizeOnce ctx =
  | TmVar r -> optionMap (lam x. x) (constantfoldEnvLookup r.ident ctx)

  sem updateCtx ctx =
  | TmVar r -> constantfoldVarCountIncr r.ident ctx
end

lang LamAppConstantFold = ConstantFold + LamAst + AppAst + VarAst + LetAst
  sem optimizeOnce ctx =
  -- | TmLam (lamr & ({body = TmApp {lhs = lhs, rhs = TmVar varr}})) ->
  --   if and
  --        (nameEqSymUnsafe lamr.ident varr.ident)
  --        (eqi (constantfoldVarCount lamr.ident ctx) 1)
  --   then Some lhs
  --   else None ()
  | TmApp (appr & {lhs = TmLam lamr}) ->
    let tyBody = tyTm appr.rhs in
    Some (TmLet {
      ident = lamr.ident,
      tyAnnot = tyBody,
      tyBody = tyBody,
      body = appr.rhs,
      inexpr = lamr.body,
      ty = appr.ty,
      info = appr.info
    })
end

lang LetConstantFold = ConstantFold + LetAst + ConstAst + LamAst
  sem optimizeOnce ctx =
  | TmLet r ->
    if optionIsSome (constantfoldEnvLookup r.ident ctx) then Some r.inexpr
    else None ()

  sem updateCtx ctx =
  | TmLet r ->
    let ctx = updateCtx (updateCtx ctx r.body) r.inexpr in
    switch r.body
    case TmVar _ then constantfoldEnvInsert r.ident r.body ctx
    case TmConst c | TmLam {body = TmConst c} then
      if exprHasSideEffect ctx.sideEffectEnv r.body then ctx
      else constantfoldEnvInsert r.ident r.body ctx
    case body then
      if and
           (not (exprHasSideEffect ctx.sideEffectEnv body))
           (lti (constantfoldVarCount r.ident ctx) 2)
      then constantfoldEnvInsert r.ident body ctx
      else ctx
    end
end

lang ArithFloatConstantFold = ConstantFold + ArithFloatEval + AppAst
  sem optimizeOnce ctx =
  | TmApp {
    lhs = TmApp {
      lhs = TmConst {val = c & CAddf _},
      rhs = a},
    rhs = b,
    info = info
  } ->
    switch (a, b)
    case (TmConst {val = CFloat f1}, TmConst {val = CFloat f2}) then
      Some (delta info (c, [a, b]))
    case (TmConst {val = CFloat f}, b) | (b, TmConst {val = CFloat f}) then
      if eqf f.val 0. then Some b else None ()
    case (_, _) then None ()
    end
  | TmApp {
    lhs = TmApp {
      lhs = TmConst {val = c & CMulf _},
      rhs = a},
    rhs = b,
    info = info
  } ->
    switch (a, b)
    case (TmConst {val = CFloat f1}, TmConst {val = CFloat f2}) then
      Some (delta info (c, [a, b]))
    case
      (a & TmConst {val = CFloat f}, b) | (b, a & TmConst {val = CFloat f})
    then
      if eqf f.val 1. then Some b
      else if and (eqf f.val 0.) (not (hasSideEffect b)) then Some a
      else None ()
    case (_, _) then None ()
    end
  | TmApp {
    lhs = TmApp (appr & {
      lhs = TmConst (constr & {val = c & CSubf _}),
      rhs = a}),
    rhs = b,
    info = info
  } ->
    switch (a, b)
    case (TmConst {val = CFloat f1}, TmConst {val = CFloat f2}) then
      Some (delta info (c, [a, b]))
    case (TmConst {val = CFloat f}, b) then
      if eqf f.val 0. then
        Some (TmApp {
          appr with lhs = TmConst { constr with val = CNegf () },
          rhs = b
        })
      else None ()
    case (a, TmConst {val = CFloat f}) then
      if eqf f.val 0. then Some a
      else None ()
    case (_, _) then None ()
    end
  | TmApp {
    lhs = TmApp {
      lhs = TmConst {val = c & CDivf _},
      rhs = a},
    rhs = b,
    info = info
  } ->
    switch (a, b)
    case (TmConst {val = CFloat f1}, TmConst {val = CFloat f2}) then
      Some (delta info (c, [a, b]))
    case (TmConst {val = CFloat f}, b) then
      if and (eqf f.val 0.) (not (hasSideEffect b)) then Some a
      else None ()
    case (a, TmConst {val = CFloat f}) then
      if eqf f.val 0. then
        errorSingle [info] "Division by zero"
      else if eqf f.val 1. then Some a
      else None ()
    case (_, _) then None ()
    end
  | TmApp {
    lhs = TmConst {val = CNegf _},
    rhs = TmApp {
      lhs = TmConst {val = CNegf _},
      rhs = a},
    info = info
  } -> Some a
  | TmApp {
    lhs = TmConst {val = c & CNegf _},
    rhs = (a & TmConst {val = CFloat _}),
    info = info} ->
    Some (delta info (c, [a]))
end

lang MExprConstantFold =
  -- Terms
  VarConstantFold + LamAppConstantFold + LetConstantFold +

  -- Constants
  ArithFloatConstantFold
end

lang TestLang = MExprConstantFold + MExprPrettyPrint + MExprEq + BootParser end

mexpr

use TestLang in

let _test = lam expr.
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "Before constantfold",
      expr2str expr
    ]);
  let expr = symbolizeAllowFree expr in
  match constantfold expr with expr in
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "After constantfold",
      expr2str expr
    ]);
  expr
in

let _parse =
  parseMExprString
    { _defaultBootParserParseMExprStringArg () with allowFree = true }
in

-----------------------
-- Test Let-bindings --
-----------------------

let prog = _parse "let x = y in x" in
utest _test prog with _parse "y" using eqExpr in

let prog = _parse "let x = y y in x x" in
utest _test prog with _parse "let x = y y in x x" using eqExpr in

let prog = _parse "let x = let z = y in z in x" in
utest _test prog with _parse "y" using eqExpr in

let prog = _parse "let x = let z = y in z in x" in
utest _test prog with _parse "y" using eqExpr in

let prog = _parse "let x = y in x x" in
utest _test prog with _parse "y y" using eqExpr in

let prog = _parse "let x = let y = z in y in x x" in
utest _test prog with _parse "z z" using eqExpr in

let prog = _parse "let x = 1 in x x" in
utest _test prog with _parse "1 1" using eqExpr in

let prog = _parse "let f = lam. 1 in (f x) (f x)" in
utest _test prog with _parse "1 1" using eqExpr in

let prog = _parse "let f = print \"hello world\" in f" in
utest _test prog with _parse "
let f =
  print
    \"hello world\"
in
f
  "
  using eqExpr
in

let prog = _parse "let f = print \"hello world\" in let g = f in g" in
utest _test prog with _parse "
let f =
  print
    \"hello world\"
in
f
  "
  using eqExpr
in

------------------
-- Test Lam App --
------------------

let prog = _parse "(lam x. x x z) y" in
utest _test prog with _parse "
y
  y
  z
  "
  using eqExpr
in

let prog = _parse "(lam. x x z) y" in
utest _test prog with _parse "
x
  x
  z
  "
  using eqExpr
in

let prog = _parse "(lam x. x x z) (lam x. x z)" in
utest _test prog with _parse "
let x =
  lam x1.
    x1
      z
in
x
  x
  z
  "
  using eqExpr
in

--------------
-- Test Lam --
--------------

let prog = _parse "lam x. x" in
utest _test prog with _parse "lam x. x" using eqExpr in

let prog = _parse "lam x. let y = x in y" in
utest _test prog with _parse "lam x. x" using eqExpr in

let prog = _parse "(lam x. x) y" in
utest _test prog with _parse "y" using eqExpr in

-------------------------------
-- Test Remove Eta-Expansion --
-------------------------------

-- let prog = _parse "lam x. y x" in
-- utest _test prog with _parse "y" using eqExpr in

let prog = _parse "let g = lam x. addf (subf x 1.) x in g" in
utest _test prog with _parse "lam x. addf (subf x 1.) x" using eqExpr in

-- logSetLogLevel logLevel.debug;

-- let prog = _parse "
--   let h = lam x. addf x x in
--   let g = lam x. mulf x (subf x 1.) in
--   lam x. addf (h x) (g x)
--   "
-- in
-- utest _test prog with _parse "lam x. addf (subf x 1.) x" using eqExpr in

---------------------------
-- Test Float Arithmetic --
---------------------------

let prog = _parse "
let x = negf (subf (divf (mulf (addf 1. 2.) 2.) 2.) 4.) in
x
  " in
utest _test prog with _parse "1." using eqExpr in

let prog = _parse "addf x 0." in
utest _test prog with _parse "x" using eqExpr in

let prog = _parse "addf 0. x" in
utest _test prog with _parse "x" using eqExpr in

let prog = _parse "subf x 0." in
utest _test prog with _parse "x" using eqExpr in

let prog = _parse "subf 0. x" in
utest _test prog with _parse "negf x" using eqExpr in

let prog = _parse "mulf x 0." in
utest _test prog with _parse "0." using eqExpr in

let prog = _parse "mulf 0. x" in
utest _test prog with _parse "0." using eqExpr in

let prog = _parse "mulf (print \"hello\"; y) 0." in
utest _test prog with _parse "
mulf
  (print \"hello\"; y)
  0.
  "
  using eqExpr
in

let prog = _parse "mulf 0. (print \"hello\"; y)" in
utest _test prog with _parse "
mulf
  0.
  (print \"hello\"; y)
  "
  using eqExpr
in


let prog = _parse "mulf x 1." in
utest _test prog with _parse "x" using eqExpr in

let prog = _parse "mulf 1. x" in
utest _test prog with _parse "x" using eqExpr in

let prog = _parse "divf x 1." in
utest _test prog with _parse "x" using eqExpr in

let prog = _parse "divf 0. x" in
utest _test prog with _parse "0." using eqExpr in

-- logSetLogLevel logLevel.debug;

let prog = _parse "divf 0. (print \"hello\"; x)" in
utest _test prog with _parse "
divf
  0.
  (print \"hello\"; x)
  "
  using eqExpr
in

let prog = _parse "negf (negf x)" in
utest _test prog with _parse "x" using eqExpr in

let prog = _parse "
let h =
  lam x6.
    subf
      x6
      2.
in
let dh =
  lam x5.
    1.
in
let g =
  lam x4.
    mulf
      x4
      (subf
         x4
         1.)
in
let dg =
  lam x3.
    addf
      (subf
         x3
         1.)
      x3
in
let f =
  lam x2.
    addf
      (addf
         (g
            x2)
         (h
            x2))
      (h
         (mulf
            2.
            x2))
in
let df =
  lam x1.
    addf
      (addf
         (dg
            x1)
         (dh
            x1))
      (mulf
         2.
         (dh
            (mulf
               2.
               x1)))
in
let df =
  lam x.
    df
      x
in
df
  1.
  " in

utest _test prog with _parse "
4.
  "
  using eqExpr
in

-- logSetLogLevel logLevel.debug;

let prog = _parse "
let h =
  lam x4.
    addf
      x4
      x4
in
let dh =
  lam x3.
    2.
in
let g =
  lam x2.
    mulf
      x2
      (subf
         x2
         1.)
in
let dh =
  lam x1.
    let t3 =
      subf
        x1
        1.
    in
    let t4 =
      addf
        t3
        x1
    in
    t4
in
lam x.
  let t =
    dh
      x
  in
  let t1 =
    dh
      x
  in
  let t2 =
    addf
      t
      t1
  in
  t2
  "
in

utest _test prog with _parse "
let dh =
  lam x1.
    addf
      (subf
         x1
         1.)
      x1
in
lam x.
  addf
    (dh
       x)
    (dh
       x)
  "
  using eqExpr
in

()
