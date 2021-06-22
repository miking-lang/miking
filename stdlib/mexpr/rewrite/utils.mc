include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/patterns.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

-- Gets the return type of the body of a function.
recursive let functionBodyReturnType : Expr -> Type =
  use MExprParallelKeywordMaker in
  lam expr.
  match expr with TmLam {body = body} then
    functionBodyReturnType body
  else ty expr
end

-- Replaces the body of a functiion body, excluding its top-level parameters,
-- with a new expression.
recursive let replaceFunctionBody : Expr -> Expr -> Expr =
  use MExprParallelKeywordMaker in
  lam funcExpr. lam newExpr.
  match funcExpr with TmLam t then
    let body = replaceFunctionBody t.body newExpr in
    let ty = TyArrow {from = t.tyIdent, to = ty body, info = infoTy t.ty} in
    TmLam {{t with body = body} with ty = ty}
  else newExpr
end

-- Substitutes all occurences of the expression from with the expression to in
-- the expression e.
let substituteExpression : Expr -> Expr -> Expr -> Expr =
  use MExprParallelKeywordMaker in
  lam e. lam from. lam to.
  recursive let work = lam e.
    if eqExpr e from then to
    else smap_Expr_Expr work e
  in work e

-- Substitutes all variables of the given expression with the expressions their
-- names have been mapped to.
let substituteVariables : Expr -> Map Name (Info -> Expr) -> Expr =
  use MExprParallelKeywordMaker in
  lam e. lam nameMap.
  recursive let work = lam e.
    match e with TmVar {ident = id, info = info} then
      match mapLookup id nameMap with Some exprFn then
        exprFn info
      else e
    else smap_Expr_Expr work e
  in work e

let substituteIdentifier : Expr -> Name -> Name -> (Info -> Expr) =
  use MExprAst in
  lam e. lam fromId. lam toId.
  let nameMap = mapFromSeq nameCmp
    [(fromId, lam info. TmVar {ident = toId, ty = TyUnknown {info = info},
                               info = info})] in
  substituteVariables e nameMap

-- Takes a function expression and produces a tuple containing a list of the
-- arguments and the function body without the lambdas.
let functionParametersAndBody : Expr -> ([(Name, Type, Info)], Expr) =
  use MExprAst in
  lam functionExpr.
  recursive let work = lam acc. lam e.
    match e with TmLam t then
      work (snoc acc (t.ident, t.tyIdent, t.info)) t.body
    else (acc, e)
  in work [] functionExpr

-- Collects the parameters of an application and returns them in a tuple
-- together with the target expression (the function being called).
let collectAppArguments : Expr -> (Expr, [Expr]) =
  use MExprAst in
  lam e.
  recursive let work = lam acc. lam e.
    match e with TmApp {lhs = !(TmApp _) & lhs, rhs = rhs} then
      (lhs, cons rhs acc)
    else match e with TmApp t then
      work (cons t.rhs acc) t.lhs
    else (e, acc)
  in
  work [] e

lang TestLang = MExprEq + MExprSym + MExprTypeAnnot

mexpr

use TestLang in

let eqType = eqType assocEmpty in

let t = typeAnnot (symbolize (lam_ "x" tyint_ (char_ 'c'))) in
utest functionBodyReturnType t with tychar_ using eqType in
let t = typeAnnot (symbolize (lam_ "x" tyint_ (uconst_ (CAddi ())))) in
utest functionBodyReturnType t with tyarrows_ [tyint_, tyint_, tyint_] using eqType in

let x = nameSym "x" in
let y = nameSym "y" in
let t = typeAnnot (nlam_ x tyint_ (char_ 'c')) in
let newBody = typeAnnot (nlam_ y tyint_ (addi_ (nvar_ x) (nvar_ y))) in
let b = replaceFunctionBody t newBody in
utest b with nulam_ x newBody using eqExpr in
utest ty b with tyarrows_ [tyint_, tyint_, tyint_] using eqType in

let names = mapFromSeq nameCmp [
  (x, lam info. TmConst {val = CInt {val = 2}, ty = TyInt {info = info},
                         info = info}),
  (y, lam. subi_ (int_ 0) (int_ 1))
] in
let t = addi_ (nvar_ x) (nvar_ y) in
utest substituteVariables t names with addi_ (int_ 2) (subi_ (int_ 0) (int_ 1)) using eqExpr in

let eqVariable = lam a : (Name, Type, Info). lam b : (Name, Type, Info).
  if nameEq a.0 b.0 then
    eqType a.1 b.1
  else false
in

let t = nlam_ x tyint_ (nlam_ y tychar_ (int_ 2)) in
let res : ([(Name, Type, Info)], Expr) = functionParametersAndBody t in
let arg1 = get res.0 0 in
let arg2 = get res.0 1 in
utest arg1 with (x, tyint_, NoInfo ()) using eqVariable in
utest arg2 with (y, tychar_, NoInfo ()) using eqVariable in
utest res.1 with int_ 2 using eqExpr in
let res : ([(Name, Type, Info)], Expr) = functionParametersAndBody (int_ 2) in
utest res.0 with [] using eqSeq eqVariable in
utest res.1 with int_ 2 using eqExpr in

let eqVar = lam var1. lam var2.
  match (var1, var2) with (TmVar {ident = id1}, TmVar {ident = id2}) then
    nameEq id1 id2
  else false
in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let t = collectAppArguments (appf2_ (nvar_ x) (nvar_ y) (nvar_ z)) in
let target = t.0 in
let args = t.1 in
utest t.0 with nvar_ x using eqVar in
utest t.1 with [nvar_ y, nvar_ z] using eqSeq eqVar in

()
