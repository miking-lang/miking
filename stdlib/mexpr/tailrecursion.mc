-- This file defines a function for translating self-recursive functions into a
-- tail-recursive function, in the case where the self-recursive call is
-- wrapped in an associative binary operator (addi, muli or concat).

include "common.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/type-annot.mc"

let printMExpr = use MExprPrettyPrint in
  lam e : Expr.
  printLn (expr2str e)

recursive let getReturnType = use MExprAst in
  lam ty : Type.
  match ty with TyArrow {to = (TyArrow _) & t} then getReturnType t
  else match ty with TyArrow {to = to} then to
  else TyUnknown {info = infoTy ty}
end

recursive let setFunctionBody : Expr -> Expr -> Expr = use MExprAst in
  lam funcBody. lam newBody.
  match funcBody with TmLam t then
    let body = setFunctionBody t.body newBody in
    let ty = TyArrow {from = t.tyIdent, to = ty body, info = infoTm t.body} in
    TmLam {{t with body = body}
              with ty = ty}
  else newBody
end

recursive let substituteIdentifier = use MExprAst in
  lam from. lam to. lam e : Expr.
  match e with TmVar ({ident = id} & t) then
    if nameEq id from then
      TmVar {t with ident = to}
    else e
  else smap_Expr_Expr (substituteIdentifier from to) e
end

let functionBodyWithoutArguments : Expr -> Expr = use MExprAst in
  lam bodyWithArguments.
  recursive let work = lam e.
    match e with TmLam {body = body} then
      work body
    else e
  in work bodyWithArguments

let tailPositionBinaryOperator = use MExprAst in
  lam bodyWithArgs : Expr.
  let body = functionBodyWithoutArguments bodyWithArgs in
  match body with
    TmMatch {thn = TmApp {lhs = TmApp {lhs = TmConst _ & binop}},
             els = !(TmMatch _)}
  then
    Some binop
  else match body with
    TmMatch {els = TmApp {lhs = TmApp {lhs = TmConst _ & binop}},
             thn = !(TmMatch _)}
  then
    Some binop
  else None ()

let neutralElement = use MExprAst in
  lam binop : Expr.
  let i = infoTm binop in
  match binop with TmConst {val = CAddi _} then
    Some (TmConst {val = CInt {val = 0}, ty = TyInt {info = i}, info = i})
  else match binop with TmConst {val = CMuli _} then
    Some (TmConst {val = CInt {val = 1}, ty = TyInt {info = i}, info = i})
  else match binop with TmConst {val = CConcat _} then
    Some (TmSeq {tms = [], ty = TySeq {ty = TyUnknown {info = i}, info = i},
                 info = i})
  else None ()

let isSelfRecursive : Name -> Expr -> Bool = use MExprAst in
  lam funcId. lam expr.
  recursive let work = lam e.
    match e with TmVar {ident = id} then
      nameEq funcId id
    else match e with TmApp t then
      work t.lhs
    else false
  in work expr

let toTailRecursiveBody : RecLetBinding -> Expr -> Name -> Name -> Expr =
  use MExprEq in
  use MExprAst in
  lam binding : RecLetBinding. lam binop. lam tailFuncId. lam accId.
  let f = lam baseBranch. lam arg1. lam arg2.
    if isSelfRecursive binding.ident arg1 then
      let lhs = appf2_ binop baseBranch (nvar_ accId) in
      let rhs = app_ (substituteIdentifier binding.ident tailFuncId arg1)
                     (appf2_ binop arg2 (nvar_ accId)) in
      Some (lhs, rhs)
    else if isSelfRecursive binding.ident arg2 then
      let lhs = appf2_ binop (nvar_ accId) baseBranch in
      let rhs = app_ (substituteIdentifier binding.ident tailFuncId arg2)
                     (appf2_ binop (nvar_ accId) arg1) in
      Some (lhs, rhs)
    else None ()
  in
  let body = functionBodyWithoutArguments binding.body in
  match body with TmMatch ({thn = TmApp {lhs = TmApp {rhs = arg1},
                                         rhs = arg2}} & t) then
    optionMap
      (lam cases : (Expr, Expr).
        TmMatch {{t with thn = cases.1}
                    with els = cases.0})
      (f t.els arg1 arg2)
  else match body with TmMatch ({els = TmApp {lhs = TmApp {rhs = arg1},
                                              rhs = arg2}} & t) then
    optionMap
      (lam cases : (Expr, Expr).
        TmMatch {{t with thn = cases.0}
                    with els = cases.1})
      (f t.thn arg1 arg2)
  else None ()

let getFunctionParameters : Expr -> [(Name, Type)] = use MExprAst in
  lam funcBody.
  recursive let work = lam body. lam acc.
    match body with TmLam t then
      work t.body (snoc acc (t.ident, t.tyIdent))
    else acc
  in work funcBody []

let makeTailRecursiveBinding = use MExprAst in
  lam binding : RecLetBinding.
  match tailPositionBinaryOperator binding.body with Some op then
    match neutralElement op with Some ne then
      let tailFnId = nameSym (concat (nameGetStr binding.ident) "_tr") in
      let accId = nameSym "acc" in
      let accType = getReturnType binding.tyBody in
      match toTailRecursiveBody binding op tailFnId accId with Some tr then
        let trTyBody = TyArrow {from = ty ne, to = accType,
                                info = infoTm binding.body} in
        let trInnerBody = TmLam {ident = accId, tyIdent = accType, body = tr,
                                 ty = trTyBody, info = infoTm binding.body} in
        let trBody = setFunctionBody binding.body trInnerBody in
        let tailRecursiveBinding = {{{binding with ident = tailFnId}
                                              with body = trBody}
                                              with tyBody = ty trBody} in
        let params : [(Name, Type)] = getFunctionParameters binding.body in
        let originalFunctionBody =
          nlams_ params
            (appSeq_
              (nvar_ tailFnId)
              (snoc (map (lam arg : (Name, Type). nvar_ arg.0) params) ne)) in
        let originalBinding = {binding with body = originalFunctionBody} in
        [tailRecursiveBinding, originalBinding]
      else [binding]
    else [binding]
  else [binding]

lang MExprTailRecursion = MExprAst
  sem tailRecursive =
  | TmRecLets t ->
    TmRecLets {{t with bindings = join (map makeTailRecursiveBinding t.bindings)}
                  with inexpr = tailRecursive t.inexpr}
  | t -> smap_Expr_Expr tailRecursive t
end

lang TestLang = MExprTailRecursion + MExprTypeAnnot + MExprEq

mexpr

use TestLang in

let trFunctionName = nameSym "tr" in
let accName = nameSym "acc" in

let factName = nameSym "fact" in
let n = nameSym "n" in
let fact = tailRecursive (nreclets_ [
  (factName, tyarrow_ tyint_ tyint_, nlam_ n tyint_
    (if_ (leqi_ (nvar_ n) (int_ 1))
      (int_ 1)
      (muli_ (nvar_ n) (app_ (nvar_ factName) (subi_ (nvar_ n) (int_ 1))))))
]) in

let factTailRecursive = nreclets_ [
  (trFunctionName, tyunknown_,
    nlam_ n tyint_
      (nlam_ accName tyint_
        (if_ (leqi_ (nvar_ n) (int_ 1))
             (muli_ (nvar_ accName) (int_ 1))
             (appf2_ (nvar_ trFunctionName)
                     (subi_ (nvar_ n) (int_ 1)) 
                     (muli_ (nvar_ accName) (nvar_ n)))))),
  (factName, tyunknown_,
    nlam_ n tyint_
      (appf2_ (nvar_ trFunctionName) (nvar_ n) (int_ 1)))] in

utest fact with factTailRecursive using eqExpr in
utest tailRecursive factTailRecursive with factTailRecursive using eqExpr in

let mapName = nameSym "map" in
let f = nameSym "f" in
let s = nameSym "s" in
let map = tailRecursive (nreclets_ [
  (mapName, tyarrows_ [tyarrow_ tyunknown_ tyunknown_, tyseq_ tyunknown_,
                       tyseq_ tyunknown_],
    nlam_ f (tyarrow_ tyunknown_ tyunknown_) (nlam_ s (tyseq_ tyunknown_) (
      if_
        (null_ (nvar_ s))
        (seq_ [])
        (concat_ (seq_ [app_ (nvar_ f) (head_ (nvar_ s))])
                 (appf2_ (nvar_ mapName) (nvar_ f) (tail_ (nvar_ s)))))))
]) in

let mapTailRecursive = nreclets_ [
  (trFunctionName, tyunknown_, nulam_ f (nulam_ s (nulam_ accName (
    if_
      (null_ (nvar_ s))
      (concat_ (nvar_ accName) (seq_ []))
      (appf3_ (nvar_ trFunctionName)
        (nvar_ f) (tail_ (nvar_ s))
        (concat_ (nvar_ accName) (seq_ [app_ (nvar_ f) (head_ (nvar_ s))]))))))),
  (mapName, tyunknown_, nulam_ f (nulam_ s
    (appf3_ (nvar_ trFunctionName) (nvar_ f) (nvar_ s) (seq_ []))))
] in

utest map with mapTailRecursive using eqExpr in
utest tailRecursive mapTailRecursive with mapTailRecursive using eqExpr in

let h = nameSym "h" in
let t = nameSym "t" in
let mapUsingCons = tailRecursive (nreclets_ [
  (mapName, tyunknown_, nulam_ f (nulam_ s (
    match_
      (nvar_ s)
      (pseqedgen_ [npvar_ h] t [])
      (cons_ (app_ (nvar_ f) (nvar_ h))
             (appf2_ (nvar_ mapName) (nvar_ f) (nvar_ t)))
      (seq_ []))))
]) in

utest tailRecursive mapUsingCons with mapUsingCons using eqExpr in

()
