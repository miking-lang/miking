-- Traverse tail positions in a recursive let.

include "set.mc"

include "mexpr/mexpr.mc"
include "mexpr/anf.mc"
include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"

lang TailPositions = MExprAst
  sem tailPositionsReclet : all a. all b.
       (a -> b -> Expr -> Expr)
    -> (a -> b -> Expr -> (a, Expr))
    -> (b -> Expr -> (b, Expr -> Expr))
    -> b -> a -> Expr
    -> (a, Expr)
  sem tailPositionsReclet baseCase tailCall letexpr lacc acc =
  | TmRecLets t ->
    let lets: [Name] = map (lam b: RecLetBinding. b.ident) t.bindings in
    let lets = setOfSeq nameCmp lets in
    match mapAccumL (lam acc: a. lam b: RecLetBinding.
        match visitTailPositions baseCase tailCall letexpr (lets, acc, lacc) b.body
        with ((_,acc,_), body)
        in (acc, {b with body = body})
      ) acc t.bindings
    with (acc, bindings) in
    (acc, TmRecLets {t with bindings = bindings})

  | t ->
    smapAccumL_Expr_Expr (tailPositionsReclet baseCase tailCall letexpr lacc) acc t

  sem tailPositionBaseCase =
  | TmConst _ -> true
  | TmRecord _ -> true
  | TmRecordUpdate _ -> true
  | TmVar _ -> true
  | TmConApp _ -> true
  | TmSeq _ -> true
  | TmType _ -> true
  | TmConDef _ -> true
  | t -> false

  sem visitTailPositions : all a. all b.
       (a -> b -> Expr -> Expr)
    -> (a -> b -> Expr -> (a, Expr))
    -> (b -> Expr -> (b, Expr -> Expr))
    -> (Set Name, a, b)
    -> Expr
    -> ((Set Name, a, b), Expr)

  sem visitTailPositions baseCase tailCall letexpr acc =
  | TmLam ({ body = (TmVar v)} & t) ->
    match acc with (_, tacc, lacc) in
    let helperLetExpr = bind_ (nulet_ v.ident t.body) t.body in
    (acc, TmLam { t with body = baseCase tacc lacc helperLetExpr })
  | TmRecLets t ->
    match acc with (env, tacc, lacc) in
    match tailPositionsReclet baseCase tailCall letexpr lacc tacc (TmRecLets t)
    with (tacc, TmRecLets t) in
    match visitTailPositions baseCase tailCall letexpr (env, tacc, lacc) t.inexpr
    with (acc, inexpr) in
    (acc, TmRecLets {t with inexpr = inexpr})
  | TmLet t ->
    match acc with (env, tacc, lacc0) in
    match letexpr lacc0 (TmLet t) with (lacc, prepend) in
    let acc = (env, tacc, lacc) in
    match
    switch t
    case { inexpr = TmVar vin } then
      -- The case 'let t = ... in t', i.e. the body of the let is in tail
      -- position.
      if nameEq vin.ident t.ident then
        -- Yes.
        switch t
        -- Application: tail call?
        case { body = TmApp {lhs = TmVar vlhs} } then
          if setMem vlhs.ident env then
            match tailCall tacc lacc t.body with (tacc, body) in
            ((env, tacc, lacc), TmLet { t with body = body })
          else (acc, baseCase tacc lacc (TmLet t))
        -- Match: one of the branches returns a variable?
        case { body = TmMatch m } then
          match
            match m with {thn = TmVar v} then
              let helperLetExpr = bind_ (nulet_ v.ident m.thn) m.thn in
              (acc, baseCase tacc lacc helperLetExpr)
            else visitTailPositions baseCase tailCall letexpr acc m.thn
          with (acc, thn) in
          match
            match m with {els = TmVar v} then
              let helperLetExpr = bind_ (nulet_ v.ident m.els) m.els in
              (acc, baseCase tacc lacc helperLetExpr)
            else visitTailPositions baseCase tailCall letexpr acc m.els
          with (acc, els) in
          let body = TmMatch {{m with thn = thn} with els = els} in
          (acc, TmLet {t with body = body})
        -- All other cases
        case _ then
          if tailPositionBaseCase t.body then
            (acc, baseCase tacc lacc (TmLet t))
          else
            smapAccumL_Expr_Expr (
              visitTailPositions baseCase tailCall letexpr) acc (TmLet t)
        end
      else
        -- No, only the variable being returned is in tail position.
        let helperLetExpr = bind_ (nulet_ vin.ident t.inexpr) t.inexpr in
        (acc, TmLet {t with inexpr = baseCase tacc lacc helperLetExpr})
    -- Redefinition of recursive functions
    case ({body = (TmApp {lhs = TmVar v} | TmVar v)}) & (!{inexpr = TmVar _}) then
      let env =
        if setMem v.ident env then
          setInsert t.ident env
        else env
      in
      match visitTailPositions baseCase tailCall letexpr (env, tacc, lacc0) t.inexpr
      with (acc, inexpr) in
      (acc, TmLet { t with inexpr = inexpr })
    case _ then
      smapAccumL_Expr_Expr (visitTailPositions baseCase tailCall letexpr) (env, tacc, lacc0) (TmLet t)
    end
    with (acc, expr) in
    (acc, prepend expr)
  | t ->
    smapAccumL_Expr_Expr (visitTailPositions baseCase tailCall letexpr) acc t
end

lang TestLang =
  TailPositions + BootParser + MExprPrettyPrint + MExprANFAll + MExprSym +
  MExprEval
end

mexpr

use TestLang in

let debug = false in

let parse = lam str.
  let ast = parseMExprStringKeywordsExn [] str in
  symbolize ast
in

let debugPrint = lam debug.
  if debug then printLn
  else (lam. ())
in

let test = lam debug. lam t. lam acc. lam lacc. lam baseCase. lam tailCall. lam letexpr.
  use MExprPrettyPrint in
  debugPrint debug "--- BEFORE ---";
  debugPrint debug (expr2str t);
  debugPrint debug "--- ANF ---";
  let t = normalizeTerm t in
  debugPrint debug (expr2str t);
  debugPrint debug "--- AFTER ---";
  match tailPositionsReclet baseCase tailCall letexpr lacc acc t with (acc, t) in
  debugPrint debug (expr2str t);
  debugPrint debug "-------------";
  let res = eval (evalCtxEmpty ()) t in
  debugPrint debug (expr2str res);
  (acc, expr2str res)
in

let letexprNoop = lam lacc. lam e. (lacc, lam x. x) in
let baseCaseInexpr = lam inexpr. lam. lam. lam x.
  match x with TmLet t in TmLet {t with inexpr = inexpr}
in

-- Base cases
let t = parse
"
type Foo in
con Con : Int -> Foo in
recursive
  let a = lam x.
    1
  let b = lam x.
    x
  let c = lam x.
    let y = negi x in
    3
  let d = lam x.
    let y = addi x 2 in
    let z = subi x 2 in
    y
  let e = lam x.
    match x with true then false
    else true
  let f = lam x.
    let t =
      match x with true then false
      else true
    in
    addi 3 1
  let g = lam x.
    {key = x}
  let h = lam x.
    let v = x in
    v
  let i = lam x.
    Con 1
  let j = lam x.
    let s = [1,2,3] in
    x
in
(a (), b (), c 1, d 1, e (), f (), g (), h (), i (), j ())
"
in

utest test debug t 0 0 (baseCaseInexpr (int_ 42)) (lam a. lam. lam x. (a,x)) letexprNoop
with (0, "(42, 42, 42, 42, 42, 42, 42, 42, 42, 42)") in

-- Tail calls
let t = parse
"
let t = 4 in
recursive
  let a = lam x.
    if eqi x 0 then 2
    else a (subi x 1)
  let b = lam x.
    a x
  let c = lam x.
    let res = a x in
    addi res 1
  let d = lam x. lam y.
    d x y
  let e = lam x. lam y.
    d x y
  let f = lam x.
    if eqi x 0 then 1
    else
      let res = f (subi x 1) in
      let t = addi 1 2 in
      res
in
(a 2, b 3, c 1, d 0 0, e 0 0, f 2)
" in

utest test debug t 0 0 (lam. lam. lam x. x) (lam acc. lam lacc. lam x. (addi acc 1, addi_ (int_ 1) (int_ 2))) letexprNoop
with (4, "(3, 3, 4, 3, 3, 1)") in

-- Nested reclets
let t = parse
"
recursive
  let f = lam x.
    recursive
      let a = lam x.
        if eqi x 0 then a x
        else
          let callF = f 0 in
          callF
    in
    let res = a x in
    addi res 1
in
f 2
" in

utest test debug t 0 0 (baseCaseInexpr (int_ 10)) (lam acc. lam lacc. lam x. (addi acc 1, int_ 42)) letexprNoop
with (1, "10") in

-- Only consider some let expressions
let t = parse
"
let t = 4 in
recursive
  let a = lam x.
    let aExpr =
      if eqi x 0 then 2
      else a (subi x 1)
    in aExpr
  let b = lam x.
    a x
  let c = lam x.
    let res = a x in
    addi res 1
  let d = lam x. lam y.
    d x y
  let e = lam x. lam y.
    let eExpr = d x y in eExpr
  let f = lam x.
    if eqi x 0 then 1
    else
      let res = f (subi x 1) in
      let t = addi 1 2 in
      res
in
(a 2, b 3, c 1, d 0 0, e 0 0, f 2)
" in

let strs = setOfSeq cmpString ["aExpr","eExpr"] in

let letexpr = lam flag: Bool. lam e: Expr.
  match e with TmLet t in
  if flag then (true, lam x. x) else
    let newFlag = setMem (nameGetStr t.ident) strs in
    if newFlag then (true, lam e. bindSemi_ (negi_ (int_ 1)) e)
    else (false, lam x. x)
in

let tailCall = lam acc: Int. lam flag. lam x.
  if flag then (addi acc 1, int_ 42) else (acc, int_ 3)
in

utest test debug t 0 false (lam. lam. lam x. x) tailCall letexpr
with (2, "(42, 3, 43, 3, 42, 1)") in

-- Base case within a match
let t = parse
"
recursive
  let f1 = lam x.
    match x with 1 then x
    else x

  let f2 = lam x.
    match x with 1 then {lbl=1}
    else {lbl=2}
in

(f1 1, f1 2, f2 1, f2 2)
" in

let baseCase = baseCaseInexpr (int_ 42) in
let tailCall = lam a. lam b. lam e. (a, e) in

utest test debug t 0 0 baseCase tailCall letexprNoop
with (0, "(42, 42, 42, 42)") in


-- Base case within a match
let t = parse
"
let r = ref 0 in

recursive
  let f1 = lam x.
    let t =
      match x with 1 then modref r 1
      else ()
    in
    x
in
let res = f1 1 in
(res, deref r)
" in

let baseCase = baseCaseInexpr (int_ 42) in
let tailCall = lam a. lam b. lam e. (a, e) in

utest test debug t 0 0 baseCase tailCall letexprNoop
with (0, "(42, 1)") in



()
