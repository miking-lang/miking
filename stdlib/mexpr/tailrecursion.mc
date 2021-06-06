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

recursive let isSelfRecursiveApp = use MExprAst in
  lam id : Name. lam e : Expr.
  match e with TmApp {lhs = lhs, rhs = rhs} then
    isSelfRecursiveApp id lhs
  else match e with TmVar t then
    nameEq id t.ident
  else false
end

recursive let substituteIdentifier = use MExprAst in
  lam from. lam to. lam e : Expr.
  match e with TmVar ({ident = id} & t) then
    if nameEq id from then
      TmVar {t with ident = to}
    else e
  else smap_Expr_Expr (substituteIdentifier from to) e
end

let neutralElement = use MExprAst in
  lam e : Expr.
  match e with TmConst {val = CAddi _} then
    Some (TmConst {val = CInt {val = 0}, ty = tyunknown_, info = NoInfo ()})
  else match e with TmConst {val = CMuli _} then
    Some (TmConst {val = CInt {val = 1}, ty = tyunknown_, info = NoInfo ()})
  else match e with TmConst {val = CConcat _} then
    Some (TmSeq {tms = [], ty = tyunknown_, info = NoInfo ()})
  else None ()

let toTailRecursiveForm = use MExprAst in
  lam id : Name. lam op : Expr. lam trId : Name. lam accId : Name. lam e : Expr.
  match e with TmNever _ then
    Some e
  else match e with TmApp {lhs = TmApp {lhs = TmConst {val = c} & binop,
                                        rhs = arg1},
                           rhs = arg2} then
    if optionIsSome (neutralElement binop) then
      if isSelfRecursiveApp id arg1 then
        Some (TmApp {
          lhs = substituteIdentifier id trId arg1,
          rhs = TmApp {
            lhs = TmApp {
              lhs = binop,
              rhs = arg2,
              ty = tyunknown_,
              info = infoTm arg2
            },
            rhs = TmVar {ident = accId, ty = ty e, info = infoTm e},
            ty = tyunknown_,
            info = infoTm arg2
          },
          ty = tyunknown_,
          info = infoTm e
        })
      else if isSelfRecursiveApp id arg2 then
        Some (TmApp {
          lhs = substituteIdentifier id trId arg2,
          rhs = TmApp {
            lhs = TmApp {
              lhs = binop,
              rhs = TmVar {ident = accId, ty = ty e, info = infoTm e},
              ty = tyunknown_,
              info = infoTm arg1
            },
            rhs = arg1,
            ty = tyunknown_,
            info = infoTm arg1
          },
          ty = tyunknown_,
          info = infoTm e
        })
      else None ()
    else None ()
  else Some (appf2_ op e (nvar_ accId))

let findAssociativeBinaryOperator = use MExprEq in
  lam e : Expr.
  let assocOperator : Expr -> Option Expr = lam e.
    match e with TmApp {lhs = TmApp {lhs = TmConst _ & op}} then
      optionMap (lam. op) (neutralElement op)
    else None ()
  in
  recursive let work : Expr -> Option Expr = lam e.
    match e with TmMatch t then
      match assocOperator t.thn with Some op1 then
        match work t.els with Some op2 then
          if eqExpr op1 op2 then Some op1 else None ()
        else Some op1
      else work t.els
    else assocOperator e
  in
  work e

let toTailRecursiveExpression = use MExprAst in
  lam binding : RecLetBinding. lam tailFnId. lam accId.
  recursive let splitResult : Expr -> Expr -> (Expr, Expr) = lam acc. lam e.
    match e with TmLet t then
      splitResult (bind_ acc (TmLet {t with inexpr = unit_})) t.inexpr
    else match e with TmLam t then
      splitResult (bind_ acc (TmLam {t with body = unit_})) t.body
    else match e with TmRecLets t then
      splitResult (bind_ acc (TmRecLets {t with inexpr = unit_})) t.inexpr
    else match e with TmType t then
      splitResult (bind_ acc (TmType {t with inexpr = unit_})) t.inexpr
    else match e with TmConDef t then
      splitResult (bind_ acc (TmConDef {t with inexpr = unit_})) t.inexpr
    else match e with TmUtest t then
      splitResult (bind_ acc (TmUtest {t with next = unit_})) t.next
    else match e with TmExt t then
      splitResult (bind_ acc (TmExt {t with inexpr = unit_})) t.inexpr
    else
      (acc, e)
  in
  recursive let transformResultExpressionCases : Expr -> Expr -> Option Expr =
    lam op. lam e.
    match e with TmMatch t then
      optionJoin
        (optionMap
          (lam thn.
            optionMap
              (lam els.
                TmMatch {{t with thn = thn} with els = els})
              (transformResultExpressionCases op t.els))
          (toTailRecursiveForm binding.ident op tailFnId accId t.thn))
    else toTailRecursiveForm binding.ident op tailFnId accId e
  in
  match splitResult unit_ binding.body with (funcBody, resultExpr) then
    optionJoin
      (optionMap
        (lam op.
          optionMap
            (lam expr.
              (op, bind_ funcBody expr))
            (transformResultExpressionCases op resultExpr))
        (findAssociativeBinaryOperator resultExpr))
  else never

recursive let addParameter = use MExprAst in
  lam paramId. lam paramTy. lam body.
  match body with TmLam t then
    let body = addParameter paramId paramTy t.body in
    let ty = TyArrow {from = t.tyIdent, to = ty body, info = t.info} in
    TmLam {{t with body = body}
              with ty = ty}
  else
    TmLam {
      ident = paramId,
      tyIdent = paramTy,
      body = body,
      ty = TyArrow {from = paramTy, to = ty body, info = NoInfo ()},
      info = NoInfo ()
    }
end

recursive let getReturnType = use MExprAst in
  lam ty : Type.
  match ty with TyArrow {to = to} then
    to
  else TyUnknown {info = infoTy ty}
end

let getFunctionArguments = use MExprAst in
  lam e : Expr.
  recursive let work = lam acc. lam e.
    match e with TmLam t then
      work (snoc acc (t.ident, t.tyIdent)) t.body
    else acc
  in
  work [] e

let tailRecursiveBinding = use MExprAst in
  lam binding : RecLetBinding.
  let tailFnId = nameSym (concat (nameGetStr binding.ident) "_tr") in
  let accId = nameSym "acc" in
  let accType = getReturnType binding.tyBody in
  match toTailRecursiveExpression binding tailFnId accId with Some (op, body) then
    let trBody = addParameter accId accType body in
    let tailRecursiveBinding =
      {{{binding with ident = tailFnId}
                 with body = trBody}
                 with tyBody = ty trBody} in
    let functionArgs : [(Name, Type)] = getFunctionArguments body in
    match neutralElement op with Some ne then
      let originalFunctionBody =
        nlams_ functionArgs
          (appSeq_
            (nvar_ tailFnId)
            (snoc (map (lam arg : (Name, Type). nvar_ arg.0) functionArgs) ne))
      in
      let originalBinding = {binding with body = originalFunctionBody} in
      [tailRecursiveBinding, originalBinding]
    else [binding]
  else [binding]

lang MExprTailRecursive = MExprAst
  sem tailRecursive =
  | TmRecLets t ->
    TmRecLets {t with bindings = join (map tailRecursiveBinding t.bindings)}
  | t -> smap_Expr_Expr tailRecursive t
end

lang TestLang = MExprTailRecursive + MExprTypeAnnot + MExprEq

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
             (muli_ (int_ 1) (nvar_ accName))
             (appf2_ (nvar_ trFunctionName)
                     (subi_ (nvar_ n) (int_ 1)) 
                     (muli_ (nvar_ accName) (nvar_ n)))))),
  (factName, tyunknown_,
    nlam_ n tyint_
      (appf2_ (nvar_ trFunctionName) (nvar_ n) (int_ 1)))] in

utest fact with factTailRecursive using eqExpr in

let mapName = nameSym "map" in
let f = nameSym "f" in
let s = nameSym "s" in
let h = nameSym "h" in
let t = nameSym "t" in
let map = tailRecursive (nreclets_ [
  (mapName, tyunknown_, nulam_ f (nulam_ s (
    match_
      (nvar_ s)
      (pseqedgen_ [npvar_ h] t [])
      (concat_ (seq_ [app_ (nvar_ f) (nvar_ h)])
               (appf2_ (nvar_ mapName) (nvar_ f) (nvar_ t)))
      (seq_ []))))
]) in

let mapTailRecursive = nreclets_ [
  (trFunctionName, tyunknown_, nulam_ f (nulam_ s (nulam_ accName (
    match_
      (nvar_ s)
      (pseqedgen_ [npvar_ h] t [])
      (appf3_ (nvar_ trFunctionName) (nvar_ f) (nvar_ t)
              (concat_ (nvar_ accName) (seq_ [app_ (nvar_ f) (nvar_ h)])))
      (concat_ (seq_ []) (nvar_ accName))
    )))),
  (mapName, tyunknown_, nulam_ f (nulam_ s
    (appf3_ (nvar_ trFunctionName) (nvar_ f) (nvar_ s) (seq_ []))))
] in

utest map with mapTailRecursive using eqExpr in

let fibName = nameSym "fib" in
let fib = tailRecursive (nreclets_ [
  (fibName, tyunknown_, nulam_ n (
    if_ (eqi_ (nvar_ n) (int_ 0))
      (int_ 0)
      (if_ (eqi_ (nvar_ n) (int_ 1))
        (int_ 1)
        (addi_ (app_ (nvar_ fibName) (subi_ (nvar_ n) (int_ 1)))
               (app_ (nvar_ fibName) (subi_ (nvar_ n) (int_ 2)))))))
]) in

let fibTailRecursive = nreclets_ [
  (trFunctionName, tyunknown_, nulam_ n (nulam_ accName (
    if_ (eqi_  (nvar_ n) (int_ 0))
      (addi_ (int_ 0) (nvar_ accName))
      (if_ (eqi_ (nvar_ n) (int_ 1))
        (addi_ (int_ 1) (nvar_ accName))
        (appf2_ (nvar_ trFunctionName)
          (subi_ (nvar_ n) (int_ 1))
          (addi_ (app_ (nvar_ fibName) (subi_ (nvar_ n) (int_ 2)))
                 (nvar_ accName))))))),
  (fibName, tyunknown_, nulam_ n (
    appf2_ (nvar_ trFunctionName) (nvar_ n) (int_ 0)))
] in

utest fib with fibTailRecursive using eqExpr in
utest tailRecursive fibTailRecursive with fibTailRecursive using eqExpr in

let 

()
