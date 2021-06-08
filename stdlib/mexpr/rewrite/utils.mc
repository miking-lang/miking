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

let substituteIdentifier : Expr -> Name -> (Info -> Expr) -> Expr =
  use MExprAst in
  lam e. lam fromId. lam toId.
  let nameMap = mapFromSeq nameCmp
    [(fromId, lam info. TmVar {ident = toId, info = info})] in
  substituteVariables e nameMap

-- Takes a function expression and produces a tuple containing a list of the
-- arguments and the function body without the lambdas.
let functionArgumentsAndBody : Expr -> ([(Name, Type, Info)], Expr) =
  use MExprAst in
  lam functionExpr.
  recursive let work = lam acc. lam e.
    match e with TmLam t then
      work (snoc acc (t.ident, t.tyIdent, t.info)) t.body
    else (acc, e)
  in work [] functionExpr

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

let t = nlam_ x tyint_ (nlam_ y tychar_ (int_ 2)) in
let res : ([(Name, Type, Info)], Expr) = functionArgumentsAndBody t in
let arg1 = get res.0 0 in
let arg2 = get res.0 1 in
utest arg1 with (x, tyint_, NoInfo ()) in
utest arg2 with (y, tychar_, NoInfo ()) in
utest res.1 with int_ 2 using eqExpr in

()
