-- Transforms recursive bindings fulfilling a set of properties into a
-- tail-recursive version of the same function using an accumulator.
--
-- A simplified summary of these requirements on a binding f are:
-- * It has an expression at tail position of the form 'binop (f x) y' (the
--   recursive case may also be the right-hand side argument), where 'binop' is
--   an associative binary operator with a known neutral element, 'x'
--   represents the arguments of f, and 'y' is an arbitrary expression.
-- * If there are more than one such expression, they must all be using the
--   same binary operator 'binop' and the position of the recursive call must
--   be the same.

include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "pmexpr/ast.mc"
include "pmexpr/function-properties.mc"
include "pmexpr/utils.mc"

type TailRecursiveEnv = use Ast in {
  binop : Expr,
  ne : Expr,
  leftArgRecursion : Bool
}

type Side
con LeftSide : () -> Side
con RightSide : () -> Side
con Both : () -> Side

-- Finds a compatible side which agrees with both given side values. The value
-- None represents neither side (the minimal element), while Some (BothSides ())
-- represents either side (the maximal element).
let compatibleSide : Option Side -> Option Side -> Option Side =
  optionCombine
    (lam l. lam r.
      let o = (l, r) in
      match o with (Both (), rhs) then Some rhs
      else match o with (lhs, Both ()) then Some lhs
      else match o with (LeftSide (), LeftSide ()) then Some (LeftSide ())
      else match o with (RightSide (), RightSide ()) then Some (RightSide ())
      else None ())

-- Determines whether a given expression is a recursive call to a function with
-- the given identifier.
let isRecursiveCall : use Ast in Expr -> Name -> Bool =
  use MExprAst in
  lam expr. lam ident.
  match collectAppArguments expr with (TmVar {ident = functionId}, _) then
    nameEq ident functionId
  else false

-- Finds the binary operator and the side at which the recursive call takes
-- place, if any, in a given tail position expression of a recursive binding.
-- If no such binary operator is found, None is returned. If no recursive call
-- takes place within either of the arguments of the binary operator, then the
-- result is None.
type TailPosInfo = use Ast in {binop : Expr, side : Option Side}
let tailPositionExpressionInfo : use Ast in Name -> Expr -> Option TailPosInfo =
  lam ident. lam expr.
  use MExprAst in
  match expr with TmApp {lhs = TmApp {lhs = binop, rhs = arg1}, rhs = arg2} then
    let lrec = isRecursiveCall arg1 ident in
    let rrec = isRecursiveCall arg2 ident in
    let side =
      if lrec then if rrec then Some (Both ()) else Some (LeftSide ())
      else if rrec then Some (RightSide ())
      else None () in
    optionBind
      side
      (lam. Some {binop = binop, side = side})
  else None ()

lang PMExprTailRecursion = PMExprAst + PMExprFunctionProperties +
                           PMExprVariableSub
  -- Attempts to construct a tail-recursion rewrite environment from the given
  -- recursive binding. If this succeeds, this environment can be used to rewrite
  -- the given binding into a tail-recursive form. Otherwise, None is returned.
  sem getTailRecursiveRewriteEnv =
  | t ->
    let binding : RecLetBinding = t in
    recursive let findExpressionsAtTailPosition : Expr -> [Expr] = lam expr.
      match expr with TmLam t then findExpressionsAtTailPosition t.body
      else match expr with TmLet t then findExpressionsAtTailPosition t.inexpr
      else match expr with TmRecLets t then findExpressionsAtTailPosition t.inexpr
      else match expr with TmType t then findExpressionsAtTailPosition t.inexpr
      else match expr with TmConDef t then findExpressionsAtTailPosition t.inexpr
      else match expr with TmUtest t then findExpressionsAtTailPosition t.next
      else match expr with TmExt t then findExpressionsAtTailPosition t.inexpr
      else match expr with TmMatch t then
        concat
          (findExpressionsAtTailPosition t.thn)
          (findExpressionsAtTailPosition t.els)
      else [expr]
    in
    let compatibleBinop : Option Expr -> Option TailPosInfo -> Option Expr =
      lam acc. lam info.
      let binop = optionMap (lam info : TailPosInfo. info.binop) info in
      optionCombine
        (lam l. lam r.
          if eqExpr l r then Some l else None ())
        acc binop in
    let compatibleArgumentSide : Option Side -> Option TailPosInfo -> Option Side =
      lam acc. lam info.
      let side = optionJoin (optionMap (lam info : TailPosInfo. info.side) info) in
      compatibleSide acc side in
    let exprs = findExpressionsAtTailPosition binding.body in
    let tailPosInfo = map (tailPositionExpressionInfo binding.ident) exprs in
    match foldl compatibleBinop (None ()) tailPosInfo with Some binop then
      match tyTm binop with TyArrow {from = elemTy, to = TyArrow _} then
        if isAssociative binop then
          match getNeutralElement binop with Some ne then
            let ne = withType elemTy (withInfo binding.info ne) in
            match foldl compatibleArgumentSide (None ()) tailPosInfo with Some side then
              let leftArgRecursion =
                match side with LeftSide () | Both () then true else false
              in
              Some {binop = binop, ne = ne, leftArgRecursion = leftArgRecursion}
            else None ()
          else None ()
        else None ()
      else None ()
    else None ()

  -- Rewrites a given binding into a tail-recursive form
  sem toTailRecursiveForm (env : TailRecursiveEnv) =
  | t ->
    -- env = {binop : Expr, ne : Expr, leftArgRecursion : Bool}
    let binding : RecLetBinding = t in

    -- Generate a new symbol for the name so that we can easily identify calls
    -- to which we need to add an accumulator argument.
    let oldIdent = binding.ident in
    let newIdent = nameSetNewSym binding.ident in
    let accIdent = nameSym "acc" in
    let accType = tyTm env.ne in

    -- Handles the recursive case, where the recursive call and the left- and
    -- right-hand side arguments of the updated accumulator value are given.
    -- The resulting expression is a call to the tail-recursive function with
    -- an accumulator.
    let makeRecursiveCallWithAccumulator : Info -> Expr -> Expr -> Expr -> Expr =
      lam info. lam recursiveApp. lam larg. lam rarg.
      let accTy = tyWithInfo info accType in
      let innerAppTy = TyArrow {from = tyTm rarg, to = accTy,
                                info = info} in
      let bindingBodyTy = tyWithInfo info binding.tyBody in
      let functionWithAccTy = TyArrow {from = accTy, to = bindingBodyTy,
                                       info = info} in
      let t = TmApp {
        lhs = TmVar {ident = newIdent, ty = functionWithAccTy,
                     info = info, frozen = false},
        rhs = TmApp {lhs = TmApp {lhs = env.binop, rhs = larg, ty = innerAppTy,
                                  info = info},
                     rhs = rarg, ty = accTy, info = info},
        ty = bindingBodyTy, info = info
      } in
      -- Replace the old identifier with an application of the accumulator
      -- value on the new function identifier.
      let substituteMap =
        mapFromSeq nameCmp [(oldIdent, lam. t)] in
      substituteVariables substituteMap recursiveApp
    in

    -- Handles the base case, where the expression is added as one of the
    -- arguments, the other being the accumulator value, to the binary
    -- operator.
    let baseCase = lam expr. lam acc.
      let info = infoTm acc in
      let args = if env.leftArgRecursion then (expr, acc) else (acc, expr) in
      match args with (larg, rarg) then
        let resultTy = tyWithInfo info (tyTm acc) in
        let innerAppTy = TyArrow {from = tyTm rarg, to = resultTy,
                                  info = info} in
        TmApp {lhs = TmApp {lhs = env.binop, rhs = larg, ty = innerAppTy,
                            info = info},
               rhs = rarg, ty = resultTy, info = info}
      else never
    in

    recursive let rewriteTailRecursive : Expr -> Expr = lam expr.
      match expr with TmLam t then
        TmLam {t with body = rewriteTailRecursive t.body}
      else match expr with TmLet t then
        TmLet {t with inexpr = rewriteTailRecursive t.inexpr}
      else match expr with TmRecLets t then
        TmRecLets {t with inexpr = rewriteTailRecursive t.inexpr}
      else match expr with TmType t then
        TmType {t with inexpr = rewriteTailRecursive t.inexpr}
      else match expr with TmConDef t then
        TmConDef {t with inexpr = rewriteTailRecursive t.inexpr}
      else match expr with TmUtest t then
        TmUtest {t with next = rewriteTailRecursive t.next}
      else match expr with TmExt t then
        TmExt {t with inexpr = rewriteTailRecursive t.inexpr}
      else match expr with TmMatch t then
        TmMatch {{t with thn = rewriteTailRecursive t.thn}
                    with els = rewriteTailRecursive t.els}
      else
        let info = infoTm expr in
        let acc = TmVar {ident = accIdent, ty = tyWithInfo info (tyTm expr),
                         info = info, frozen = false} in
        match expr with TmApp {lhs = TmApp {lhs = bop, rhs = arg1}, rhs = arg2} then
          if eqExpr env.binop bop then
            if and env.leftArgRecursion (isRecursiveCall arg1 binding.ident) then
              makeRecursiveCallWithAccumulator info arg1 arg2 acc
            else if and (not env.leftArgRecursion)
                        (isRecursiveCall arg2 binding.ident) then
              makeRecursiveCallWithAccumulator info arg2 acc arg1
            else baseCase expr acc
          else baseCase expr acc
        else if eqExpr expr env.ne then
          acc
        else baseCase expr acc
    in

    match functionParametersAndBody binding.body with (_, body) then
      let body = rewriteTailRecursive body in
      let functionBody = replaceFunctionBody binding.body body in
      let bodyWithAcc = TmLam {
        ident = accIdent,
        tyAnnot = accType,
        tyParam = accType,
        body = functionBody,
        ty = TyArrow {from = accType, to = binding.tyBody, info = binding.info},
        info = binding.info
      } in
      Some ({{{binding with ident = newIdent}
                       with tyBody = tyTm bodyWithAcc}
                       with body = bodyWithAcc})
    else never

  sem tailRecursiveRewrite (subMap : Map Name (Info -> Expr)) =
  | t ->
    let t : RecLetBinding = t in
    match getTailRecursiveRewriteEnv t with Some env then
      let env : TailRecursiveEnv = env in
      match toTailRecursiveForm env t with Some tailRecursiveBinding then
        let binding : RecLetBinding = tailRecursiveBinding in
        let oldIdent = t.ident in
        let replacementFunctionCall = lam info.
          TmApp {
            lhs = TmVar {
              ident = binding.ident,
              ty = tyWithInfo info binding.tyBody,
              info = binding.info,
              frozen = false
            },
            rhs = env.ne,
            ty = tyWithInfo info t.tyBody,
            info = info
          }
        in
        Some (mapInsert oldIdent replacementFunctionCall subMap, binding)
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
    -- Try to rewrite the bindings into a tail-recursive form.
    match mapAccumL tailRecursiveBinding subMap t.bindings
    with (subMap, bindings) then
      -- Translate calls to rewritten bindings within each binding.
      let bindings =
        map
          (lam bind : RecLetBinding.
            match tailRecursiveH subMap bind.body with (_, body) then
              {bind with body = body}
            else never)
          bindings in

      -- Translate calls to rewritten bindings in the inexpr term.
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

lang TestLang =
  PMExprTailRecursion + MExprTypeCheck + MExprSym + MExprEq + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam e. typeCheck (symbolize e) in

let fact = preprocess (bindall_ [
  ureclets_ [
    ("fact", ulam_ "n" (
      if_ (leqi_ (var_ "n") (int_ 1))
        (int_ 1)
        (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))
    ))],
  app_ (var_ "fact") (int_ 10)]) in
let factTr = preprocess (bindall_ [
  ureclets_ [
    ("fact", ulam_ "acc" (ulam_ "n" (
      if_ (leqi_ (var_ "n") (int_ 1))
        (var_ "acc")
        (appf2_ (var_ "fact")
          (muli_ (var_ "acc") (var_ "n"))
          (subi_ (var_ "n") (int_ 1)))
    )))],
  (appf2_ (var_ "fact") (int_ 1) (int_ 10))]) in
utest tailRecursive fact with factTr using eqExpr in
utest tailRecursive factTr with factTr using eqExpr in

let filter = preprocess (ureclets_ [
  ("filter", ulam_ "p" (ulam_ "s" (
    if_ (null_ (var_ "s"))
      (seq_ [])
      (if_ (app_ (var_ "p") (head_ (var_ "s")))
        (concat_ (seq_ [head_ (var_ "s")])
                 (appf2_ (var_ "filter") (var_ "p") (tail_ (var_ "s"))))
        (appf2_ (var_ "filter") (var_ "p") (tail_ (var_ "s")))))))]) in
let filterTr = preprocess (ureclets_ [
  ("filter", ulam_ "acc" (ulam_ "p" (ulam_ "s" (
    if_ (null_ (var_ "s"))
      (var_ "acc")
      (if_ (app_ (var_ "p") (head_ (var_ "s")))
        (appf3_ (var_ "filter")
          (concat_ (var_ "acc") (seq_ [head_ (var_ "s")]))
          (var_ "p") (tail_ (var_ "s")))
        (concat_
          (var_ "acc")
          (appf3_ (var_ "filter") (seq_ []) (var_ "p")
                                  (tail_ (var_ "s")))))))))]) in
utest tailRecursive filter with filterTr using eqExpr in

let fib = preprocess (ureclets_ [
  ("fib", ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (int_ 0)
      (if_ (eqi_ (var_ "n") (int_ 1))
        (int_ 1)
        (addi_ (app_ (var_ "fib") (subi_ (var_ "n") (int_ 1)))
               (app_ (var_ "fib") (subi_ (var_ "n") (int_ 2)))))))]) in
let fibTr = preprocess (ureclets_ [
  ("fib", ulam_ "acc" (ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (var_ "acc")
      (if_ (eqi_ (var_ "n") (int_ 1))
        (addi_ (int_ 1) (var_ "acc"))
        (appf2_ (var_ "fib")
          (addi_ (appf2_ (var_ "fib") (int_ 0)
                 (subi_ (var_ "n") (int_ 2))) (var_ "acc"))
          (subi_ (var_ "n") (int_ 1)))))))]) in
utest tailRecursive fib with fibTr using eqExpr in
utest tailRecursive fibTr with fibTr using eqExpr in

let map0 = preprocess (ureclets_ [
  ("map0", ulam_ "f" (ulam_ "s" (
    match_ (var_ "s") (pseqedge_ [pvar_ "h"] "t" [])
      (concat_ (seq_ [app_ (var_ "f") (var_ "h")]) (appf2_ (var_ "map0") (var_ "f") (var_ "t")))
      (seq_ [int_ 0]))))]) in
let map0Tr = preprocess (ureclets_ [
  ("map0", ulam_ "acc" (ulam_ "f" (ulam_ "s" (
    match_ (var_ "s") (pseqedge_ [pvar_ "h"] "t" [])
      (appf3_ (var_ "map0")
        (concat_ (var_ "acc") (seq_ [app_ (var_ "f") (var_ "h")]))
        (var_ "f") (var_ "t"))
      (concat_ (var_ "acc") (seq_ [int_ 0]))))))]) in
utest tailRecursive map0 with map0Tr using eqExpr in
utest tailRecursive map0Tr with map0Tr using eqExpr in

()
