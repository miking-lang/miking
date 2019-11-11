-- TODO: Generate unique symbols for data constructors
-- TODO: Add types
include "string.mc"

-- TODO: Change string variables to deBruijn indices
type Env = [(String, Expr)]

lang Var
  syn Expr =
  | TmVar String

  sem eval (env : Env) =
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
  syn Type =
  | Arrow (Type, Type)
  syn Expr =
  | TmLam (String, Option, Expr) -- Option Type
  | TmClos (String, Option, Expr, Env) -- Option Type
  | TmApp (Expr, Expr)

  sem apply (arg : Expr) =
  | TmClos t ->
      let x = t.0 in
      let body = t.1 in
      let env2 = t.2 in
      eval (cons (x, arg) env2) body
  | _ -> error "Bad application"

  sem eval (env : Env) =
  | TmLam t ->
    let x = t.0 in
    let body = t.2 in
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

  sem apply (arg : Expr) =
  | TmFix ->
  match arg with TmClos clos then
    let x = clos.0 in
    let body = clos.1 in
    let env2 = clos.2 in
    eval (cons (x, TmApp (TmFix, TmClos clos)) env2) body
  else
    error "Not fixing a function"

  sem eval (env : Env) =
  | TmFix -> TmFix
 end

lang Let = Var
  syn Expr =
  | TmLet (String, Expr, Expr)

  sem eval (env : Env) =
  | TmLet t ->
    let x = t.0 in
    let t1 = t.1 in
    let t2 = t.2 in
    eval (cons (x, eval env t1) env) t2
end

lang Const
  syn Const =

  syn Expr =
  | TmConst (Const)

  sem delta (arg : Expr) =

  sem apply (arg : Expr) =
  | TmConst c -> delta arg c

  sem eval (env : Env) =
  | TmConst c -> TmConst c
end

lang Unit = Const
  syn Const =
  | CUnit
end

lang Arith
  syn Const =
  | CInt Int
  | CAddi
  | CAddi2 Int
  -- TODO: Add more operations
  -- TODO: Add floating point numbers (maybe in its own fragment)

  sem delta (arg : Expr) =
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
  | CBool Bool
  | CNot
  | CAnd
  | CAnd2 Bool
  | COr
  | COr2 Bool

  syn Expr =
  | TmIf (Expr, Expr, Expr)

  sem delta (arg : Expr) =
  | CNot ->
    match arg with TmConst c then
      match c with CBool b then
        TmConst(CBool (not b))
      else error "Not negating a boolean constant"
    else error "Not negating a constant"
  | CAnd ->
    match arg with TmConst c then
      match c with CBool b then
        TmConst(CAnd2 b)
      else error "Not and-ing a boolean constant"
    else error "Not and-ing a constant"
  | CAnd2 b1 ->
    match arg with TmConst c then
      match c with CBool b2 then
        TmConst(CBool (and b1 b2))
      else error "Not and-ing a boolean constant"
    else error "Not and-ing a constant"
  | COr ->
    match arg with TmConst c then
      match c with CBool b then
        TmConst(COr2 b)
      else error "Not or-ing a boolean constant"
    else error "Not or-ing a constant"
  | COr2 b1 ->
    match arg with TmConst c then
      match c with CBool b2 then
        TmConst(CBool (or b1 b2))
      else error "Not or-ing a boolean constant"
    else error "Not or-ing a constant"

  sem eval (env : Env) =
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

lang Cmp = Arith + Bool
  syn Const =
  | CEqi
  | CEqi2 Int

  sem delta (arg : Expr) =
  | CEqi ->
    match arg with TmConst c then
      match c with CInt n then
        TmConst(CEqi2 n)
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CEqi2 n1 ->
    match arg with TmConst c then
      match c with CInt n2 then
        TmConst(CBool (eqi n1 n2))
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
end

lang Seq = Arith
  syn Const =
  | CSeq [Expr]
  | CNth
  | CNth2 [Expr]

  syn Expr =
  | TmSeq [Expr]

  sem delta (arg : Expr) =
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

  sem eval (env : Env) =
  | TmSeq tms ->
    let vs = map (eval env) tms in
    TmConst(CSeq vs)
end

lang Tuple = Arith
  syn Expr =
  | TmTuple [Expr]
  | TmProj (Expr, Int)

  sem eval (env : Env) =
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
  | TmConDef (String, Expr)
  | TmConFun (String)
  | TmCon (String, Expr)
  | TmMatch (Expr, String, String, Expr, Expr)

  sem apply (arg : Expr) =
  | TmConFun k -> TmCon (k, arg)

  sem eval (env : Env) =
  | TmConDef t ->
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
  | TmUtest (Expr, Expr, Expr)

  sem eq (e1 : Expr) =
  | _ -> error "Equality not defined for expression"

  sem eval (env : Env) =
  | TmUtest t ->
    let test = t.0 in
    let expected = t.1 in
    let next = t.2 in
    let v1 = eval env test in
    let v2 = eval env expected in
    let _ = if eq v1 v2 then print "Test passed\n" else print "Test failed\n" in
    eval env next
end

lang MExpr = Fun + Fix + Let
           + Seq + Tuple + Data + Utest
           + Const + Arith + Bool + Cmp + Unit
  sem eq (e1 : Expr) =
  | TmConst c2 -> const_expr_eq c2 e1
  | TmCon d2 -> data_eq d2 e1
  | TmTuple tms2 -> tuple_eq tms2 e1
  | TmSeq seq2 -> seq_eq seq2 e1

  sem const_expr_eq (c1 : Const) =
  | TmConst c2 -> const_eq c1 c2
  | _ -> false

  sem const_eq (c1 : Const) =
  | CUnit -> is_unit c1
  | CInt n2 -> int_eq n2 c1
  | CBool b2 -> bool_eq b2 c1

  sem is_unit =
  | CUnit -> true
  | _ -> false

  sem int_eq (n1 : Int) =
  | CInt n2 -> eqi n1 n2
  | _ -> false

  sem bool_eq (b1 : Bool) =
  | CBool b2 -> or (and b1 b2) (and (not b1) (not b2))
  | _ -> false

  sem data_eq (d1 : (String, Expr)) =
  | TmCon d2 ->
    let k1 = d1.0 in
    let k2 = d2.0 in
    let v1 = d1.1 in
    let v2 = d2.1 in
    and (eqstr k1 k2) (eq v1 v2)

  sem tuple_eq (tms1 : [Expr]) =
  | TmTuple tms2 ->
    and (eqi (length tms1) (length tms2))
        (all (lam b.b) (zipWith eq tms1 tms2))
  | _ -> false

  sem seq_eq (seq1 : [Expr]) =
  | TmSeq seq2 ->
    and (eqi (length seq1) (length seq2))
        (all (lam b.b) (zipWith eq seq1 seq2))
  | _ -> false
end

main
use MExpr in
let id = TmLam ("x", None, TmVar "x") in
let bump = TmLam ("x", None, TmApp (TmApp (TmConst CAddi, TmVar "x"), TmConst(CInt 1))) in
let fst = TmLam ("t", None, TmProj (TmVar "t", 0)) in
let app_id_unit = TmApp (id, TmConst CUnit) in
let app_bump_3 = TmApp (bump, TmConst(CInt 3)) in
let app_fst =
  TmApp (fst, TmTuple([TmApp (TmConst CNot, TmConst(CBool false))
                      ,TmApp (TmApp (TmConst CAddi, TmConst (CInt 1)), TmConst(CInt 2))])) in
utest eval [] app_id_unit with TmConst CUnit in
utest eval [] app_bump_3 with TmConst (CInt 4) in
utest eval [] app_fst with TmConst (CBool true) in

let unit = TmConst CUnit in

let data_decl = TmConDef ("Foo",
                  TmMatch (TmApp (TmVar "Foo", TmTuple [unit, unit])
                          ,"Foo", "u", TmProj(TmVar "u",0)
                          ,id)) in
utest eval [] data_decl with unit in

let utest_test1 = TmUtest (TmConst (CInt 1), TmConst (CInt 1), unit) in
let utest_test2 =
  TmUtest (TmTuple [TmConst (CInt 1),
                    TmApp (TmApp (TmConst CAddi, TmConst (CInt 1)), TmConst (CInt 2))]
          ,TmTuple [TmConst (CInt 1), TmConst (CInt 3)], unit)
in
let utest_test3 =
  TmConDef ("Foo",
    TmUtest (TmApp (TmVar "Foo", unit), TmApp (TmVar "Foo", unit), unit))
in
utest eval [] utest_test1 with unit in
utest eval [] utest_test2 with unit in
utest eval [] utest_test3 with unit in

-- Implementing an interpreter
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
  TmApp (TmFix, TmLam ("eval", None, TmLam ("e", None,
         num_case (TmVar "e") (add_case (TmVar "e") unit)))) in

let wrap_in_decls = lam t. -- con Num in con Add in let eval = ... in t
  TmConDef("Num", TmConDef ("Add", TmLet ("eval", eval_fn, t))) in

let eval_add1 = wrap_in_decls (TmApp (TmVar "eval", add_one_two)) in
let add_one_two_three = add (add one two) three in
let eval_add2 = wrap_in_decls (TmApp (TmVar "eval", add_one_two_three)) in

utest eval [] eval_add1 with TmCon("Num", TmConst(CInt 3)) in
utest eval [] eval_add2 with TmCon("Num", TmConst(CInt 6)) in

()