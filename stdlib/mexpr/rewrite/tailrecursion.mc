-- Provides a function for translating a recursive binding written in a certain
-- way into a tail-recursive function. A binding will be rewritten if it
-- contains a base-case and a recursive case which is wrapped in an associative
-- binary operator (currently one of addi, muli or concat).

include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"

-- Determines whether the given expression is an application targeting the
-- identifier of the given function.
let isRecursiveCall : Expr -> Name -> Bool =
  use MExprAst in
  lam expr. lam ident.
  match collectAppArguments expr with (TmVar {ident = functionId}, _) then
    nameEq ident functionId
  else false

let containsRecursiveCall : Expr -> Name -> Bool =
  use MExprAst in
  lam expr. lam ident.
  recursive let work = lam acc. lam expr.
    match expr with TmVar t then
      or acc (nameEq ident t.ident)
    else sfold_Expr_Expr work acc expr
  in
  work false expr

-- Attempts to find a unique binary operator that is used in all return
-- expressions, such that one of the arguments is a recursive call.
let findTailPositionBinaryOperator : Expr -> Name -> Option Expr =
  use MExprEq in
  lam body. lam ident.
  recursive let findTailExpression : Expr -> Expr = lam body.
    match body with TmLet t then findTailExpression t.inexpr
    else match body with TmRecLets t then findTailExpression t.inexpr
    else match body with TmType t then findTailExpression t.inexpr
    else match body with TmConDef t then findTailExpression t.inexpr
    else match body with TmUtest t then findTailExpression t.next
    else match body with TmExt t then findTailExpression t.inexpr
    else body
  in
  let consistentBinaryOperatorUse : Option Expr -> Expr -> Option Expr =
    lam binop. lam expr.
    if isRecursiveCall expr ident then
      binop
    else match expr with TmApp {lhs = TmApp {lhs = op2, rhs = arg1},
                                rhs = arg2} then
      if (or (isRecursiveCall arg1 ident) (isRecursiveCall arg2 ident)) then
        match binop with Some op1 then
          if eqExpr op1 op2 then Some op1 else None ()
        else Some op2
      else None ()
    else binop
  in
  recursive let findUniqueBinaryOperator : Option Expr -> Expr -> Option Expr =
    lam binop. lam expr.
    match expr with TmMatch t then
      -- If we found a binary operator, but the result of the call is None (),
      -- it means we found an inconsistency.
      let op = consistentBinaryOperatorUse binop t.thn in
      match (binop, op) with (Some _, None ()) then
        None ()
      else findUniqueBinaryOperator op t.els
    else match expr with TmNever t then
      binop
    else consistentBinaryOperatorUse binop expr
  in
  match functionParametersAndBody body with (_, bodyWithoutArgs) then
    let expr = findTailExpression bodyWithoutArgs in
    match expr with TmMatch _ then
      findUniqueBinaryOperator (None ()) expr
    else None ()
  else never

-- Returns an option containing the neutral element of the given operation,
-- given that its neutral element is known and it is known to be associative.
let getNeutralElementOfAssociativeOperator : Expr -> Option Expr =
  use MExprAst in
  lam binop.
  let i = infoTm binop in
  match binop with TmConst {val = CAddi _} then
    Some (TmConst {val = CInt {val = 0}, ty = TyInt {info = i}, info = i})
  else match binop with TmConst {val = CMuli _} then
    Some (TmConst {val = CInt {val = 1}, ty = TyInt {info = i}, info = i})
  else match binop with TmConst {val = CConcat _} then
    Some (TmSeq {tms = [], ty = TySeq {ty = TyUnknown {info = i}, info = i},
                 info = i})
  else None ()

recursive let replaceApplicationTarget = use MExprAst in
  lam app. lam replacement.
  match app with TmApp ({lhs = !(TmApp _)} & t) then
    TmApp {t with lhs = replacement}
  else match app with TmApp t then
    TmApp {t with lhs = replaceApplicationTarget t.lhs replacement}
  else error "Expected application"
end

-- Attempts to translate a recursive binding into a tail-recursive form, and
-- returns the result if this succeeds. The recursive binding must be written
-- such that its recursive case contains the given binary operator.
let toTailRecursiveForm : RecLetBinding -> Expr -> Expr -> Option RecLetBinding =
  use MExprEq in
  lam binding. lam binop. lam ne.

  -- We give the binding a new identifier, so that we can easily find the calls
  -- which have to be updated by adding an accumulator argument.
  let newIdent = nameSym (nameGetStr binding.ident) in
  let accIdent = nameSym "acc" in

  let makeFnApp = lam info. lam binop. lam lhs. lam rhs. lam recursiveApp.
    let resultTy = tyWithInfo info binding.tyBody in
    let innerAppTy = TyArrow {from = ty rhs, to = resultTy, info = info} in
    let t = TmApp {
      lhs = TmVar {ident = newIdent, ty = TyUnknown {info = info},
                   info = info},
      rhs = TmApp {lhs = TmApp {lhs = binop, rhs = lhs, ty = innerAppTy,
                                info = info},
                   rhs = rhs, ty = resultTy, info = info},
      ty = TyUnknown {info = info}, info = info} in
    replaceApplicationTarget recursiveApp t
  in
  recursive let rewriteTailRecursive : Expr -> Option Expr = lam expr.
    match expr with TmMatch t then
      match rewriteTailRecursive t.thn with Some thn then
        match rewriteTailRecursive t.els with Some els then
          Some (TmMatch {{t with thn = thn} with els = els})
        else None ()
      else None ()
    else
      let info = infoTm expr in
      let acc = TmVar {ident = accIdent, ty = tyWithInfo info (ty expr),
                       info = info} in
      if isRecursiveCall expr binding.ident then
        let appWithAcc = TmApp {
          lhs = TmVar {ident = newIdent, ty = TyUnknown {info = info},
                       info = info},
          rhs = TmVar {ident = accIdent, ty = TyUnknown {info = info},
                       info = info},
          ty = TyUnknown {info = info}, info = info} in
        Some (replaceApplicationTarget expr appWithAcc)
      else match expr with TmApp {lhs = TmApp {lhs = bop, rhs = arg1},
                                  rhs = arg2} then
        if isRecursiveCall arg1 binding.ident then
          Some (makeFnApp info bop arg2 acc arg1)
        else if isRecursiveCall arg2 binding.ident then
          Some (makeFnApp info bop acc arg1 arg2)
        else None ()
      else if eqExpr expr ne then
          Some acc
      else
        let resultTy = tyWithInfo info (ty expr) in
        let innerAppTy = TyArrow {from = ty acc, to = resultTy, info = info} in
        Some (TmApp {lhs = TmApp {lhs = binop, rhs = acc, ty = innerAppTy,
                                  info = info},
                     rhs = expr, ty = resultTy, info = info})
  in
  match functionParametersAndBody binding.body with (params, body) then
    match rewriteTailRecursive body with Some body then
      let body = replaceFunctionBody binding.body body in
      let bodyWithAcc = TmLam {
        ident = accIdent,
        tyIdent = ty body,
        body = body,
        ty = TyArrow {from = ty body, to = binding.tyBody, info = binding.info},
        info = binding.info
      } in
      Some ({{{binding with ident = newIdent}
                       with tyBody = ty bodyWithAcc}
                       with body = bodyWithAcc})
    else error (join ["Unexpected error encountered while attempting rewrite",
                      " of function", nameGetStr binding.ident,
                      " to a tail-recursive form"])
  else never

lang MExprTailRecursion = MExprParallelKeywordMaker
  sem tailRecursiveRewrite (subMap : Map Name (Info -> Expr)) =
  | t ->
    let t : RecLetBinding = t in
    -- Ensure that the recursive binding has the expected structure, and if so,
    -- extract the binary operator.
    match findTailPositionBinaryOperator t.body t.ident with Some binop then
      -- Check that the identified binary operator is associative and has a
      -- neutral element.
      match getNeutralElementOfAssociativeOperator binop with Some ne then
        match toTailRecursiveForm t binop ne with Some binding then
          let oldIdent = t.ident in
          let replacementFn = lam info.
            TmApp {
              lhs = TmVar {ident = binding.ident,
                           ty = tyWithInfo info binding.tyBody,
                           info = binding.info},
              rhs = ne,
              ty = tyWithInfo info binding.tyBody,
              info = info
            }
          in
          Some (mapInsert oldIdent replacementFn subMap, binding)
        else None ()
      else None ()
    else None ()

  sem tailRecursiveH (subMap : Map Name (Info -> Expr)) =
  | TmVar t ->
    match mapLookup t.ident subMap with Some subFn then
      (subMap, subFn t.info)
    else (subMap, TmVar t)
  | TmRecLets t ->
    let tailRecursiveBinding = lam subMap. lam binding : RecLetBinding.
      optionGetOrElse
        (lam. (subMap, binding))
        (tailRecursiveRewrite subMap binding)
    in
    -- Rewrite compatible bindings to a tail-recursive form
    match mapAccumL tailRecursiveBinding subMap t.bindings
    with (subMap, bindings) then
      -- Update calls within the binding bodies based on the contents of the
      -- updated substitution map.
      let bindings =
        map
          (lam bind : RecLetBinding.
            match tailRecursiveH subMap bind.body with (_, body) then
              {bind with body = body}
            else never)
          bindings in

      -- Perform tail-recursive translation on later expressions using the
      -- updated substitution map.
      match tailRecursiveH subMap t.inexpr with (subMap, inexpr) then
        (subMap, TmRecLets {{t with bindings = bindings} with inexpr = inexpr})
      else never
    else never
  | t -> smapAccumL_Expr_Expr tailRecursiveH subMap t

  sem tailRecursive =
  | t ->
    match tailRecursiveH (mapEmpty nameCmp) t with (_, t) then
      t
    else never
end

lang TestLang = MExprTailRecursion + MExprTypeAnnot + MExprEq + MExprPrettyPrint

mexpr

use TestLang in

let factName = nameSym "fact" in
let acc = nameSym "acc" in
let n = nameSym "n" in
let x = nameSym "x" in
let fact = bindall_ [
  nreclets_ [
    (factName, tyunknown_, nulam_ n (
      if_ (leqi_ (nvar_ n) (int_ 1))
        (int_ 1)
        (muli_ (nvar_ n) (app_ (nvar_ factName) (subi_ (nvar_ n) (int_ 1))))
    ))
  ],
  nulet_ x (app_ (nvar_ factName) (int_ 10))
] in
let factTr = bindall_ [
  nreclets_ [
    (factName, tyunknown_, nulam_ acc (nulam_ n (
      if_ (leqi_ (nvar_ n) (int_ 1))
        (nvar_ acc)
        (appf2_ (nvar_ factName) (muli_ (nvar_ acc) (nvar_ n))
                                 (subi_ (nvar_ n) (int_ 1)))
    )))
  ],
  nulet_ x (appf2_ (nvar_ factName) (int_ 1) (int_ 10))
] in
utest tailRecursive fact with factTr using eqExpr in
utest tailRecursive factTr with factTr using eqExpr in

let mapName = nameSym "map" in 
let addOne = nameSym "addOne" in
let f = nameSym "f" in
let s = nameSym "s" in
let x = nameSym "x" in
let id = nameSym "id" in
let map = bindall_ [
  nreclets_ [
    (mapName, tyunknown_, nulam_ f (nulam_ s (
      if_ (null_ (nvar_ s))
        (seq_ [])
        (concat_ (seq_ [app_ (nvar_ f) (head_ (nvar_ s))])
                 (appf2_ (nvar_ mapName) (nvar_ f) (tail_ (nvar_ s))))
    ))),
    (addOne, tyunknown_, nulam_ s (
      appf2_ (nvar_ mapName)
        (nulam_ x (addi_ (nvar_ x) (int_ 1)))
        (nvar_ s)
    ))
  ],
  nulet_ x (appf2_ (nvar_ mapName) (nvar_ id) (seq_ [int_ 1, int_ 4]))
] in
let mapTr = bindall_ [
  nreclets_ [
    (mapName, tyunknown_, nulam_ acc (nulam_ f (nulam_ s (
      if_ (null_ (nvar_ s))
        (nvar_ acc)
        (appf3_ (nvar_ mapName)
          (concat_ (nvar_ acc) (seq_ [app_ (nvar_ f) (head_ (nvar_ s))]))
          (nvar_ f)
          (tail_ (nvar_ s)))
    )))),
    (addOne, tyunknown_, nulam_ s (
      appf3_ (nvar_ mapName)
        (seq_ [])
        (nulam_ x (addi_ (nvar_ x) (int_ 1)))
        (nvar_ s)
    ))
  ],
  nulet_ x (appf3_ (nvar_ mapName) (seq_ []) (nvar_ id) (seq_ [int_ 1, int_ 4]))
] in
utest tailRecursive map with mapTr using eqExpr in
utest tailRecursive mapTr with mapTr using eqExpr in

let filterName = nameSym "filter" in
let p = nameSym "p" in
let filter = nreclets_ [
  (filterName, tyunknown_, nulam_ p (nulam_ s (
    if_ (null_ (nvar_ s))
      (seq_ [])
      (if_ (app_ (nvar_ p) (head_ (nvar_ s)))
        (concat_ (seq_ [head_ (nvar_ s)]) (appf2_ (nvar_ filterName) (nvar_ p) (tail_ (nvar_ s))))
        (appf2_ (nvar_ filterName) (nvar_ p) (tail_ (nvar_ s))))
  )))
] in
let filterTr = nreclets_ [
  (filterName, tyunknown_, nulam_ acc (nulam_ p (nulam_ s (
    if_ (null_ (nvar_ s))
      (nvar_ acc)
      (if_ (app_ (nvar_ p) (head_ (nvar_ s)))
        (appf3_ (nvar_ filterName)
          (concat_ (nvar_ acc) (seq_ [head_ (nvar_ s)]))
          (nvar_ p) (tail_ (nvar_ s)))
        (appf3_ (nvar_ filterName) (nvar_ acc) (nvar_ p) (tail_ (nvar_ s))))
  ))))
] in
utest tailRecursive filter with filterTr using eqExpr in
utest tailRecursive filterTr with filterTr using eqExpr in

let fibName = nameSym "fib" in
let fib = nreclets_ [
  (fibName, tyunknown_, nulam_ n (
    if_ (eqi_ (nvar_ n) (int_ 0))
      (int_ 0)
      (if_ (eqi_ (nvar_ n) (int_ 1))
        (int_ 1)
        (addi_ (app_ (nvar_ fibName) (subi_ (nvar_ n) (int_ 1)))
               (app_ (nvar_ fibName) (subi_ (nvar_ n) (int_ 2)))))
  ))
] in
let fibTr = nreclets_ [
  (fibName, tyunknown_, nulam_ acc (nulam_ n (
    if_ (eqi_ (nvar_ n) (int_ 0))
      (nvar_ acc)
      (if_ (eqi_ (nvar_ n) (int_ 1))
        (addi_ (nvar_ acc) (int_ 1))
        (appf2_ (nvar_ fibName)
          (addi_ (appf2_ (nvar_ fibName) (int_ 0) (subi_ (nvar_ n) (int_ 2))) (nvar_ acc))
          (subi_ (nvar_ n) (int_ 1))))
  )))
] in
utest tailRecursive fib with fibTr using eqExpr in
utest tailRecursive fibTr with fibTr using eqExpr in

()
