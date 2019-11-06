-- TODO: Change string variables to deBruijn indices
-- TODO: Generate unique symbols for data constructors
include "string.mc"

lang Var
  syn Expr =
  | TmVar (Dyn) -- String

  sem eval (env : Dyn) = -- (env : Env)
  | TmVar x ->
    let lookup = fix (lam lookup. lam x. lam env.
      if eqi (length env) 0
      then error (concat "Unknown variable: " x)
      else if eqstr (head env).0 x
      then (head env).1
      else lookup x (tail env)
    ) in
    eval env (lookup x env)
end

lang Fun = Var
  syn Expr =
  | TmLam (Dyn, Dyn) -- (String, Expr)
  | TmClos (Dyn, Dyn, Dyn) -- (String, Expr, Env)
  | TmApp (Dyn, Dyn) -- (Expr, Expr)

  sem apply (arg : Dyn) = -- (arg : Dyn)
  | TmClos t ->
      let x = t.0 in
      let body = t.1 in
      let env2 = t.2 in
      eval (cons (x, arg) env2) body
  | _ -> error "Bad application"

  sem eval (env : Dyn) = -- env : Env
  | TmLam t ->
    let x = t.0 in
    let body = t.1 in
    TmClos(x, body, env)
  | TmClos t -> TmClos t
  | TmApp t ->
    let t1 = t.0 in
    let t2 = t.1 in
    apply (eval env t2) (eval env t1)
end

lang Fix = Fun
  syn Expr =
  | TmFix

  sem apply (arg : Dyn) = -- (arg : Expr)
  | TmFix ->
  match arg with TmClos clos then
    let x = clos.0 in
    let body = clos.1 in
    let env2 = clos.2 in
    eval (cons (x, TmApp (TmFix, TmClos clos)) env2) body
  else
    error "Not fixing a function"

  sem eval (env : Dyn) = -- (env : Env)
  | TmFix -> TmFix
 end

lang Let = Var
  syn Expr =
  | TmLet (Dyn, Dyn, Dyn) -- (String, Expr, Expr)

  sem eval (env : Dyn) = -- (Env)
  | TmLet t ->
    let x = t.0 in
    let t1 = t.1 in
    let t2 = t.2 in
    eval (cons (x, eval env t1) env) t2
end

lang Const
  syn Const =

  syn Expr =
  | TmConst (Dyn) -- (Const)

  sem delta (arg : Dyn) = -- (arg : Expr)

  sem apply (arg : Dyn) = -- (arg : Expr)
  | TmConst c -> delta arg c

  sem eval (env : Dyn) = -- (env : Env)
  | TmConst c -> TmConst c
end

lang Unit = Const
  syn Const =
  | CUnit
end

lang Arith
  syn Const =
  | CInt (Dyn) -- (int)
  | CAddi
  | CAddi2 (Dyn)
  -- TODO: Add more operations

  sem delta (arg : Dyn) = -- (arg : Expr)
  | CAddi ->
    match arg with TmConst c then
      match c with CInt n then
        TmConst(CAddi2 n)
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
  | CAddi2 n1 ->
    match arg with TmConst c then
      match c with CInt n2 then
        TmConst(CInt (addi n1 n2))
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
end

lang Bool
  syn Const =
  | CBool (Dyn) -- (bool)
  | CNot

  syn Expr =
  | TmIf (Dyn, Dyn, Dyn)

  sem delta (arg : Dyn) = -- (arg : Expr)
  | CNot ->
    match arg with TmConst c then
      match c with CBool b then
        TmConst(CBool (not b))
      else error "Not negating a boolean constant"
    else error "Not negating a constant"

  sem eval (env : Dyn) = -- (env : Env)
  | TmIf t ->
    let cond = t.0 in
    let thn  = t.1 in
    let els  = t.2 in
    match eval env cond with TmConst c then
      match c with CBool b then
        if b then eval env thn else eval env els
      else error "Condition is not a boolean"
    else error "Condition is not a constant"
end

lang Seq = Arith
  syn Const =
  | CSeq (Dyn) -- ([Expr])
  | CNth
  | CNth2 (Dyn) -- ([Expr])

  syn Expr =
  | TmSeq (Dyn) -- ([Expr])

  sem delta (arg : Dyn) = -- (arg : Expr)
  | CNth ->
    match arg with TmConst c then
      match c with CSeq tms then
        TmConst(CNth2 tms)
      else error "Not nth of a sequence"
    else error "Not nth of a constant"
  | CNth2 tms ->
    match arg with TmConst c then
      match c with CInt n then
        nth tms n
      else error "n in nth is not a number"
    else error "n in nth is not a constant"

  sem eval (env : Dyn) = -- (env : Expr)
  | TmSeq tms ->
    let vs = map (eval env) tms in
    TmConst(CSeq vs)
end

lang Tuple = Arith
  syn Expr =
  | TmTuple (Dyn) -- ([Expr])
  | TmProj (Dyn, Dyn) -- (Expr, int)

  sem eval (env : Dyn) = -- (env : Expr)
  | TmTuple tms ->
    let vs = map (eval env) tms in
    TmTuple(vs)
  | TmProj t ->
    let tup = t.0 in
    let idx = t.1 in
    match eval env tup with TmTuple tms then
      nth tms idx
    else error "Not projecting from a tuple"
end

lang Data
  -- TODO: Constructors have no generated symbols
  syn Expr =
  | TmData (Dyn, Dyn) -- (String, Expr)
  | TmConFun (Dyn) -- (String)
  | TmCon (Dyn, Dyn) -- (String, Expr)
  | TmMatch (Dyn, Dyn, Dyn, Dyn, Dyn) -- (Expr, String, String, Expr, Expr)

  sem apply (arg : Dyn) = -- (arg : Dyn)
  | TmConFun k -> TmCon (k, arg)

  sem eval (env : Dyn) = -- (env : Env)
  | TmData t ->
    let k = t.0 in
    let body = t.1 in
    eval (cons (k, TmConFun(k)) env) body
  | TmConFun t -> TmConFun t
  | TmCon t -> TmCon t
  | TmMatch t ->
    let target = t.0 in
    let k2 = t.1 in
    let x = t.2 in
    let thn = t.3 in
    let els = t.4 in
    match eval env target with TmCon t1 then
      let k1 = t1.0 in
      let v = t1.1 in
      if eqstr k1 k2
      then eval (cons (x, v) env) thn
      else eval env els
    else error "Not matching on constructor"
end

lang Utest
  syn Expr =
  | TmUtest (Dyn, Dyn, Dyn) -- (Expr, Expr, Expr)

  sem eval (env : Dyn) = -- (env : Env)
  | TmUtest t ->
    let test = t.0 in
    let expected = t.1 in
    let next = t.2 in
    let v1 = eval env test in
    let v2 = eval env expected in
    let eq = (lam x. lam y. true) in -- TODO: Need generic comparisons
    let _ = if eq v1 v2 then print "Test passed\n" else print "Test failed\n" in
    eval env next
end

lang MExpr = Fun + Fix + Let
           + Seq + Tuple + Data + Utest
           + Const + Arith + Bool + Unit

main
use MExpr in
let id = TmLam ("x", TmVar "x") in
let bump = TmLam ("x", TmApp (TmApp (TmConst CAddi, TmVar "x"), TmConst(CInt 1))) in
let fst = TmLam ("t", TmProj (TmVar "t", 0)) in
let app_id_unit = TmApp (id, TmConst CUnit) in
let app_bump_3 = TmApp (bump, TmConst(CInt 3)) in
let app_fst =
  TmApp (fst, TmTuple([TmApp (TmConst CNot, TmConst(CBool false))
                      ,TmApp (TmApp (TmConst CAddi, TmConst (CInt 1)), TmConst(CInt 2))])) in
utest eval [] app_id_unit with TmConst CUnit in
utest eval [] app_bump_3 with TmConst (CInt 4) in
utest eval [] app_fst with TmConst (CBool true) in

let unit = TmConst CUnit in

let data_decl = TmData ("Foo",
                  TmMatch (TmApp (TmVar "Foo", TmTuple [unit, unit])
                          ,"Foo", "u", TmProj(TmVar "u",0)
                          ,id)) in
utest eval [] data_decl with unit in

let num = lam n. TmApp (TmVar "Num", TmConst(CInt n)) in
let one = num 1 in -- Num 1
let two = num 2 in -- Num 2
let three = num 3 in -- Num 3
let add = lam n1. lam n2. TmApp (TmVar "Add", TmTuple([n1, n2])) in
let add_one_two = add one two in -- Add (Num 1, Num 2)
let num_case = lam arg. lam els. -- match arg with Num n then Num n else els
    TmMatch (arg, "Num", "n", TmApp (TmVar "Num", (TmVar "n")), els)
in
-- match arg with Add t then
--   let e1 = t.0 in
--   let e2 = t.1 in
--   match eval e1 with Num n1 then
--     match eval e2 with Num n2 then
--       Num (addi n1 n2)
--     else ()
--   else ()
-- else els
let result =
  TmApp (TmVar "Num", (TmApp (TmApp (TmConst CAddi, TmVar "n1"), TmVar "n2"))) in
let match_inner =
  TmMatch (TmApp (TmVar "eval", TmVar "e2")
          ,"Num", "n2", result
          ,unit) in
let match_outer =
  TmMatch (TmApp (TmVar "eval", TmVar "e1")
          ,"Num", "n1", match_inner
          ,unit) in
let deconstruct = lam t.
  TmLet ("e1", TmProj (t, 0)
        ,TmLet ("e2", TmProj(t, 1), match_outer)) in
let add_case = lam arg. lam els.
  TmMatch (arg, "Add", "t", deconstruct (TmVar "t"), els) in
let eval_fn = -- fix (lam eval. lam e. match e with then ... else ())
  TmApp (TmFix, TmLam ("eval", TmLam ("e",
         num_case (TmVar "e") (add_case (TmVar "e") unit)))) in

let wrap_in_decls = lam t. -- con Num in con Add in let eval = ... in t
  TmData("Num", TmData ("Add", TmLet ("eval", eval_fn, t))) in

let eval_add1 = wrap_in_decls (TmApp (TmVar "eval", add_one_two)) in
let add_one_two_three = add (add one two) three in
let eval_add2 = wrap_in_decls (TmApp (TmVar "eval", add_one_two_three)) in

utest eval [] eval_add1 with TmCon("Num", TmConst(CInt 3)) in
utest eval [] eval_add2 with TmCon("Num", TmConst(CInt 6)) in

()