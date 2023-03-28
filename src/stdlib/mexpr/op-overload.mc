-- A library for creating overloaded operators whose types are resolved at
-- compile-time.

include "mexpr/ast.mc"
include "mexpr/const-types.mc"
include "mexpr/desugar.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/type-check.mc"

lang OverloadedOpAst = Ast
  syn Op =
  syn Expr =
  | TmOverloadedOp {info: Info, op: Op, ty: Type}

  sem infoTm =
  | TmOverloadedOp x -> x.info
  sem withInfo info =
  | TmOverloadedOp x -> TmOverloadedOp {x with info = info}

  sem tyTm =
  | TmOverloadedOp x -> x.ty
  sem withType ty =
  | TmOverloadedOp x -> TmOverloadedOp {x with ty = ty}

  sem mkOp : Info -> Op -> Expr
  sem mkOp info = | op -> TmOverloadedOp
  { info = info
  , op = op
  , ty = tyunknown_
  }

  sem opMkTypes : Info -> TCEnv -> Op -> {params: [Type], return: Type}

  sem resolveOp : Info -> {params: [Type], return: Type, op: Op} -> Expr
  sem resolveOp info =
  | _ -> errorSingle [info] "Unable to resolve the type of the operator"
end

lang OverloadedOpTypeCheck = TypeCheck + OverloadedOpAst
  sem typeCheckExpr env =
  | TmOverloadedOp x ->
    let types = opMkTypes x.info env x.op in
    let ty = tyarrows_ (snoc types.params types.return) in
    TmOverloadedOp {x with ty = ty}
end

lang OverloadedOpDesugar = Desugar + OverloadedOpAst + FunTypeAst
  sem desugarExpr =
  | TmOverloadedOp x ->
    match unwrapType x.ty with TyArrow t then
      recursive let flattenArrow = lam acc. lam t.
        match unwrapType t with TyArrow t then flattenArrow (snoc acc t.from) t.to
        else snoc acc t
      in
      let types = map unwrapType (flattenArrow [t.from] t.to) in
      resolveOp x.info {params = init types, return = last types, op = x.op}
    else errorSingle [x.info] "Wrong type shape in desugarExpr"
end

lang OverloadedOpPrettyPrint = OverloadedOpAst + PrettyPrint
  sem getOpStringCode: Int -> PprintEnv -> Op -> (PprintEnv, String)
  sem opIsAtomic: Op -> Bool

  sem pprintCode indent env =
  | TmOverloadedOp x -> getOpStringCode indent env x.op

  sem isAtomic =
  | TmOverloadedOp x -> opIsAtomic x.op
end

lang OverloadedOp = OverloadedOpAst + OverloadedOpTypeCheck + OverloadedOpDesugar
                  + OverloadedOpPrettyPrint
end

-- A test language fragment. This fragment can be used as a template to create
-- overloaded operators.
lang _testOverloadedOp = OverloadedOpAst + OverloadedOpPrettyPrint + ArithIntAst
                       + ArithFloatAst + IntTypeAst + FloatTypeAst
                       + CmpIntTypeAst + CmpFloatTypeAst
  syn Op =
  | OAdd
  | ONeg

  sem opMkTypes info env =
  | OAdd _ ->
    let ty = newmonovar env.currentLvl info in
    {params = [ty, ty], return = ty}
  | ONeg _ ->
    let ty = newmonovar env.currentLvl info in
    {params = [ty], return = ty}

  sem resolveOp info =
  | x & {op = OAdd _, params = [TyInt _] ++ _}   -> mkConst info (CAddi ())
  | x & {op = OAdd _, params = [TyFloat _] ++ _} -> mkConst info (CAddf ())

  | x & {op = ONeg _, params = [TyInt _] ++ _}   -> mkConst info (CNegi ())
  | x & {op = ONeg _, params = [TyFloat _] ++ _} -> mkConst info (CNegf ())

  sem getOpStringCode indent env =
  | OAdd _ -> (env, "+")
  | ONeg _ -> (env, "-")

  sem opIsAtomic =
  | (OAdd _) | (ONeg _) -> true
end

lang TestLang = _testOverloadedOp + OverloadedOp + MExprTypeCheck + MExprEq
              + MExprPrettyPrint
end

mexpr

use TestLang in

-- add
utest
  let t = appf2_ (mkOp (NoInfo ()) (OAdd ())) (int_ 1) (int_ 2) in
  desugarExpr (typeCheck t)
with addi_ (int_ 1) (int_ 2)
using eqExpr
in

utest
  let t = appf2_ (mkOp (NoInfo ()) (OAdd ())) (float_ 1.) (float_ 2.) in
  desugarExpr (typeCheck t)
with addf_ (float_ 1.) (float_ 2.)
using eqExpr
in

utest expr2str (mkOp (NoInfo ()) (OAdd ())) with "+" in

-- negative test: type error from mixing types
-- utest
--   let t = appf2_ (mkOp (NoInfo ()) (OAdd ())) (float_ 1.) (int_ 2) in
--   desugarExpr (typeCheck t)
-- with unit_
-- using eqExpr
-- in

-- neg
utest
  let t = appf1_ (mkOp (NoInfo ()) (ONeg ())) (int_ 3) in
  desugarExpr (typeCheck t)
with negi_ (int_ 3)
using eqExpr
in

utest
  let t = appf1_ (mkOp (NoInfo ()) (ONeg ())) (float_ 3.) in
  desugarExpr (typeCheck t)
with negf_ (float_ 3.)
using eqExpr
in

utest expr2str (mkOp (NoInfo ()) (ONeg ())) with "-" in

-- negative test: type error from wrong number of arguments
-- utest
--   let t = appf2_ (mkOp (NoInfo ()) (ONeg ())) (float_ 1.) (int_ 2) in
--   desugarExpr (typeCheck t)
-- with unit_
-- using eqExpr
-- in

()
