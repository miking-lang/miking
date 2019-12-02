-- TODO: Generate unique symbols for data constructors
-- TODO: Add types
include "string.mc"

-- TODO: Change string variables to deBruijn indices
type Env = [(String, Expr)]

recursive
  let lookup = lam x. lam env.
    if eqi (length env) 0
    then None
    else if eqstr (head env).0 x
    then Some (head env).1
    else lookup x (tail env)
end

let fresh : String -> Env -> String = lam var. lam env.
  match lookup var env with None then
    var
  else
    recursive let find_free = lam n.
      let new = concat var (int2string n) in
      match lookup new env with None then
        new
      else
        find_free (addi n 1)
    in find_free 0

lang Var
  syn Expr =
  | TmVar String
end

lang VarEval = Var
  sem eval (env : Env) =
  | TmVar x ->
    match lookup x env with Some t then
      eval env t
    else
      error (concat "Unknown variable: " x)
end

lang App
  syn Expr =
  | TmApp (Expr, Expr)
end

lang AppEval = App
  sem apply (arg : Expr) =
  | _ -> error "Bad application"

  sem eval (env : Env) =
  | TmApp t ->
    let t1 = t.0 in
    let t2 = t.1 in
    apply (eval env t2) (eval env t1)
end

lang Fun = Var + App
  syn Type =
  | TyArrow (Type, Type)
  syn Expr =
  | TmLam (String, Option, Expr) -- Option Type
end

lang FunEval = Fun + VarEval + AppEval
  syn Type =
  syn Expr =
  | TmClos (String, Option, Expr, Env) -- Option Type

  sem apply (arg : Expr) =
  | TmClos t ->
      let x = t.0 in
      let body = t.1 in
      let env2 = t.2 in
      eval (cons (x, arg) env2) body

  sem eval (env : Env) =
  | TmLam t ->
    let x = t.0 in
    let body = t.2 in
    TmClos(x, body, env)
  | TmClos t -> TmClos t
end

lang Fix = Fun
  syn Expr =
  | TmFix ()
end

lang FixEval = Fix + FunEval
  sem apply (arg : Expr) =
  | TmFix _ ->
  match arg with TmClos clos then
    let x = clos.0 in
    let body = clos.1 in
    let env2 = clos.2 in
    eval (cons (x, TmApp (TmFix (), TmClos clos)) env2) body
  else
    error "Not fixing a function"

  sem eval (env : Env) =
  | TmFix _ -> TmFix ()
 end

lang Let = Var
  syn Expr =
  | TmLet (String, Option, Expr, Expr) -- Option Type
end

lang LetEval = Let + VarEval
  sem eval (env : Env) =
  | TmLet t ->
    let x = t.0 in
    let t1 = t.2 in
    let t2 = t.3 in
    eval (cons (x, eval env t1) env) t2
end

lang RecLets = Var
  syn Type =
  syn Expr =
  | TmRecLets ([(String, Option, Expr)], Expr) -- Option Type
end

lang RecLetsEval = RecLets + VarEval + Fix + FixEval
  sem eval (env : Env) =
  | TmRecLets t ->
    let bindings = t.0 in
    let body = t.1 in
    let foldli = lam f. lam init. lam seq.
      (foldl (lam acc. lam x. (addi acc.0 1, f acc.0 acc.1 x)) (0, init) seq).1 in
    utest foldli (lam i. lam acc. lam x. concat (concat acc (int2string i)) x) "" ["a", "b", "c"]
      with "0a1b2c" in
    let eta_str = fresh "eta" env in
    let eta_var = TmVar(eta_str) in
    let unpack_from = lam var. lam body.
      foldli
        (lam i. lam body. lam binding.
          TmLet(binding.0, binding.1, TmLam(eta_str, None, TmApp(TmProj(var, i), eta_var)), body))
        body
        bindings in
    let lst_str = fresh "lst" env in
    let lst_var = TmVar(lst_str) in
    let func_tuple = TmTuple (map (lam x. x.2) bindings) in
    let unfixed_tuple = TmLam(lst_str, None (), unpack_from lst_var func_tuple) in
    eval (cons (lst_str, TmApp(TmFix (), unfixed_tuple)) env) (unpack_from lst_var body)
end

lang Const
  syn Const =

  syn Expr =
  | TmConst (Const)
end

lang ConstEval = Const
  sem delta (arg : Expr) =

  sem apply (arg : Expr) =
  | TmConst c -> delta arg c

  sem eval (env : Env) =
  | TmConst c -> TmConst c
end

lang Unit = Const
  syn Const =
  | CUnit ()
end

lang UnitPat = Unit
  syn Pat =
  | UnitPat ()

  sem tryMatch (t : Expr) =
  | UnitPat _ ->
    match t with TmConst CUnit _ then Some [] else None ()
end

-- Included for symmetry
lang UnitEval = Unit + ConstEval

lang Int = Const
  syn Const =
  | CInt Int
end

lang IntPat = Int
  syn Pat =
  | IntPat Int

  sem tryMatch (t : Expr) =
  | IntPat i -> match t with TmConst CInt i2 then
    if eqi i i2 then Some [] else None ()
    else None ()
end

lang Arith = Const + Int
  syn Const =
  | CAddi ()
  | CAddi2 Int
  | CSubi ()
  | CSubi2 Int
  | CMuli
  | CMuli2 Int
  -- TODO: Add more operations
  -- TODO: Add floating point numbers (maybe in its own fragment)
end

lang ArithEval = Arith + ConstEval
  sem delta (arg : Expr) =
  | CAddi _ ->
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
  | CSubi _ ->
    match arg with TmConst c then
      match c with CInt n then
        TmConst(CSubi2 n)
      else error "Not subbing a numeric constant"
    else error "Not subbing a constant"
  | CSubi2 n1 ->
    match arg with TmConst c then
      match c with CInt n2 then
        TmConst(CInt (subi n1 n2))
      else error "Not subbing a numeric constant"
    else error "Not subbing a constant"
  | CMuli ->
    match arg with TmConst c then
      match c with CInt n then
        TmConst(CMuli2 n)
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
  | CMuli2 n1 ->
    match arg with TmConst c then
      match c with CInt n2 then
        TmConst(CInt (muli n1 n2))
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
end

lang Bool
  syn Const =
  | CBool Bool
  | CNot ()
  | CAnd ()
  | CAnd2 Bool
  | COr ()
  | COr2 Bool

  syn Expr =
  | TmIf (Expr, Expr, Expr)
end

lang BoolPat = Bool
  syn Pat =
  | BoolPat Bool

  sem tryMatch (t : Expr) =
  | BoolPat b ->
    match t with TmConst CBool b2 then
      if or (and b b2) (and (not b) (not b2)) then Some [] else None () -- TODO: is there a nicer way to do equality on bools? 'eqb' is unbound
    else None ()
end

lang BoolEval = Bool + ConstEval
  sem delta (arg : Expr) =
  | CNot _ ->
    match arg with TmConst c then
      match c with CBool b then
        TmConst(CBool (not b))
      else error "Not negating a boolean constant"
    else error "Not negating a constant"
  | CAnd _ ->
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
  | COr _ ->
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

lang Cmp = Int + Bool
  syn Const =
  | CEqi ()
  | CEqi2 Int
  | CLti ()
  | CLti2 Int
end

lang CmpEval = Cmp + ConstEval
  sem delta (arg : Expr) =
  | CEqi _ ->
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
  | CLti _ ->
    match arg with TmConst c then
      match c with CInt n then
        TmConst(CLti2 n)
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLti2 n1 ->
    match arg with TmConst c then
      match c with CInt n2 then
        TmConst(CBool (lti n1 n2))
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
end

lang Char = Const
  syn Const =
  | CChar Char
end

lang CharEval = Char + ConstEval
end

lang Seq = Int
  syn Const =
  | CSeq [Expr]
  | CNth ()
  | CNth2 [Expr]

  syn Expr =
  | TmSeq [Expr]
end

lang SeqEval = Seq + ConstEval
  sem delta (arg : Expr) =
  | CNth _ ->
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

lang Tuple
  syn Expr =
  | TmTuple [Expr]
  | TmProj (Expr, Int)
end

lang TupleEval = Tuple
  sem eval (env : Env) =
  | TmTuple tms ->
    let vs = map (eval env) tms in
    TmTuple vs
  | TmProj t ->
    let tup = t.0 in
    let idx = t.1 in
    match eval env tup with TmTuple tms then
      nth tms idx
    else error "Not projecting from a tuple"
end

lang TuplePat = Tuple
  syn Pat =
  | TuplePat [Pat]

  sem tryMatch (t : Expr) =
  | TuplePat pats ->
    match t with TmTuple tms then
      if eqi (length pats) (length tms) then
        let results = zipWith tryMatch tms pats in
        let go = lam left. lam right.
          match (left, right) with (Some l, Some r)
          then Some (concat l r)
          else None () in
        foldl go (Some []) results
      else None ()
    else None ()
end

lang Data
  -- TODO: Constructors have no generated symbols
  syn Expr =
  | TmConDef (String, Expr)
end

lang DataEval = Data + AppEval
  syn Expr =
  | TmConFun (String)
  | TmCon (String, Expr)

  sem apply (arg : Expr) =
  | TmConFun k -> TmCon (k, arg)

  sem eval (env : Env) =
  | TmConDef t ->
    let k = t.0 in
    let body = t.2 in
    eval (cons (k, TmConFun(k)) env) body
  | TmConFun t -> TmConFun t
  | TmCon t -> TmCon t
end

lang DataPat = Data
  syn Pat =
  | ConPat (String, Pat)

  sem tryMatch (t : Expr) =
  | ConPat x -> -- INCONSISTENCY: this won't follow renames in the constructor, but the ml interpreter will
    let constructor = x.0 in
    let subpat = x.1 in
    match t with TmCon (constructor2, subexpr) then
      if eqstr constructor constructor2
        then tryMatch subexpr subpat
        else None ()
    else None ()
end

lang Match
  syn Expr =
  | TmMatch (Expr, Pat, Expr, Expr)

  syn Pat =
end

lang MatchEval = Match
  sem eval (env : Env) =
  | TmMatch t ->
    let target = t.0 in
    let pat = t.1 in
    let thn = t.2 in
    let els = t.3 in
    match tryMatch (eval env target) pat with Some newEnv then
      eval (concat newEnv env) thn
    else eval env els

  sem tryMatch (t : Expr) =
  | _ -> None ()
end

lang VarPat
  syn Pat =
  | VarPat String

  sem tryMatch (t : Expr) =
  | VarPat ident -> Some [(ident, t)]
end

lang Utest
  syn Expr =
  | TmUtest (Expr, Expr, Expr)
end

lang UtestEval = Utest
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

lang DynType
  syn Type =
  | TyDyn
end

lang UnitType
  syn Type =
  | TyUnit
end

lang SeqType
  syn Type =
  | TySeq Type
end

lang TupleType
  syn Type =
  | TyProd [Type]
end

lang DataType
  syn Type =
  | TyCon String
end

lang ArithType
  syn Type =
  | TyInt
end

lang BoolType
  syn Type =
  | TyBool
end

lang AppType
  syn Type =
  | TyApp (Type, Type)
end

-- TODO: Add more types! Think about design

lang MExpr = FunEval + LetEval + RecLetsEval
           + SeqEval + TupleEval + DataEval + UtestEval
           + ArithEval + BoolEval + CmpEval + CharEval + UnitEval
           + MatchEval + DataPat + VarPat + IntPat + TuplePat
           + BoolPat + UnitPat + DynType + UnitType + SeqType
           + TupleType + DataType + ArithType + BoolType + AppType
  sem eq (e1 : Expr) =
  | TmConst c2 -> const_expr_eq c2 e1
  | TmCon d2 -> data_eq d2.0 d2.1 e1
  | TmConFun k -> enum_eq k e1
  | TmTuple tms2 -> tuple_eq tms2 e1
  | TmSeq seq2 -> seq_eq seq2 e1

  sem const_expr_eq (c1 : Const) =
  | TmConst c2 -> const_eq c1 c2
  | _ -> false

  sem const_eq (c1 : Const) =
  | CUnit _ -> is_unit c1
  | CInt n2 -> int_eq n2 c1
  | CBool b2 -> bool_eq b2 c1
  | CChar chr2 -> char_eq chr2 c1

  sem is_unit =
  | CUnit _ -> true
  | _ -> false

  sem int_eq (n1 : Int) =
  | CInt n2 -> eqi n1 n2
  | _ -> false

  sem bool_eq (b1 : Bool) =
  | CBool b2 -> or (and b1 b2) (and (not b1) (not b2))
  | _ -> false

  sem char_eq (c1 : Char) =
  | CChar c2 -> eqi (char2int c1) (char2int c2)
  | _ -> false

  sem data_eq (k1 : String) (v1 : Expr) =
  | TmCon d2 ->
    let k2 = d2.0 in
    let v2 = d2.1 in
    and (eqstr k1 k2) (eq v1 v2)
  | _ -> false

  sem enum_eq (k1 : String) =
  | TmConFun k2 -> eqstr k1 k2
  | _ -> false

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

mexpr

use MExpr in
let id = TmLam ("x", None (), TmVar "x") in
let bump = TmLam ("x", None (), TmApp (TmApp (TmConst (CAddi ()), TmVar "x"), TmConst(CInt 1))) in
let fst = TmLam ("t", None (), TmProj (TmVar "t", 0)) in
let app_id_unit = TmApp (id, TmConst (CUnit ())) in
let app_bump_3 = TmApp (bump, TmConst(CInt 3)) in
let app_fst =
  TmApp (fst, TmTuple([TmApp (TmConst (CNot ()), TmConst(CBool false))
                      ,TmApp (TmApp (TmConst (CAddi ()), TmConst (CInt 1)), TmConst(CInt 2))])) in
utest eval [] app_id_unit with TmConst (CUnit ()) in
utest eval [] app_bump_3 with TmConst (CInt 4) in
utest eval [] app_fst with TmConst (CBool true) in

let unit = TmConst (CUnit ()) in

let data_decl = TmConDef ("Foo", None,
                  TmMatch (TmApp (TmVar "Foo", TmTuple [unit, unit])
                          ,ConPat("Foo", VarPat "u"), TmProj(TmVar "u",0)
                          ,id)) in
utest eval [] data_decl with unit in

-- Commented out to not clutter the test suite
-- let utest_test1 = TmUtest (TmConst (CInt 1), TmConst (CInt 1), unit) in
-- let utest_test2 =
--   TmUtest (TmTuple [TmConst (CInt 1),
--                     TmApp (TmApp (TmConst CAddi, TmConst (CInt 1)), TmConst (CInt 2))]
--           ,TmTuple [TmConst (CInt 1), TmConst (CInt 3)], unit)
-- in
-- let utest_test3 =
--   TmConDef ("Foo",
--     TmUtest (TmApp (TmVar "Foo", unit), TmApp (TmVar "Foo", unit), unit))
-- in
-- utest eval [] utest_test1 with unit in
-- utest eval [] utest_test2 with unit in
-- utest eval [] utest_test3 with unit in

-- Implementing an interpreter
let num = lam n. TmApp (TmVar "Num", TmConst(CInt n)) in
let one = num 1 in -- Num 1
let two = num 2 in -- Num 2
let three = num 3 in -- Num 3
let add = lam n1. lam n2. TmApp (TmVar "Add", TmTuple([n1, n2])) in
let add_one_two = add one two in -- Add (Num 1, Num 2)
let num_case = lam arg. lam els. -- match arg with Num n then Num n else els
    TmMatch (arg, ConPat ("Num", VarPat "n"), TmApp (TmVar "Num", (TmVar "n")), els)
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
  TmApp (TmVar "Num", (TmApp (TmApp (TmConst (CAddi ()), TmVar "n1"), TmVar "n2"))) in
let match_inner =
  TmMatch (TmApp (TmVar "eval", TmVar "e2")
          ,ConPat ("Num", VarPat "n2"), result
          ,unit) in
let match_outer =
  TmMatch (TmApp (TmVar "eval", TmVar "e1")
          ,ConPat ("Num", VarPat "n1"), match_inner
          ,unit) in
let deconstruct = lam t.
  TmLet ("e1", None, TmProj (t, 0)
        ,TmLet ("e2", None, TmProj(t, 1), match_outer)) in
let add_case = lam arg. lam els.
  TmMatch (arg, ConPat ("Add", VarPat "t"), deconstruct (TmVar "t"), els) in
let eval_fn = -- fix (lam eval. lam e. match e with then ... else ())
  TmApp (TmFix (), TmLam ("eval", None (), TmLam ("e", None,
         num_case (TmVar "e") (add_case (TmVar "e") unit)))) in

let wrap_in_decls = lam t. -- con Num in con Add in let eval = ... in t
  TmConDef("Num", None,
    TmConDef ("Add", None, TmLet ("eval", None, eval_fn, t))) in

let eval_add1 = wrap_in_decls (TmApp (TmVar "eval", add_one_two)) in
let add_one_two_three = add (add one two) three in
let eval_add2 = wrap_in_decls (TmApp (TmVar "eval", add_one_two_three)) in

utest eval [] eval_add1 with TmCon("Num", TmConst(CInt 3)) in
utest eval [] eval_add2 with TmCon("Num", TmConst(CInt 6)) in



let app = lam f. lam x. TmApp(f, x) in
let app_seq = lam f. lam seq. foldl app f seq in
let var = lam v. TmVar(v) in
let int = lam i. TmConst (CInt i) in
let lambda = lam var. lam body. TmLam(var, None (), body) in
let if_ = lam cond. lam th. lam el. TmIf(cond, th, el) in
let true_ = TmConst (CBool true)in
let false_ = TmConst (CBool false)in
let eqi_ = lam a. lam b. app_seq (TmConst (CEqi ())) [a, b] in
let lti_ = lam a. lam b. app_seq (TmConst (CLti ())) [a, b] in
let subi_ = lam a. lam b. app_seq (TmConst (CSubi ())) [a, b] in
let odd_even = lam body.
  TmRecLets(
    [ ( "odd"
      , None
      , lambda "x"
        (if_ (eqi_ (var "x") (int 1))
          true_
          (if_ (lti_ (var "x") (int 1))
            false_
            (app (var "even") (subi_ (var "x") (int 1))))))
    , ( "even"
      , None
      , lambda "x"
        (if_ (eqi_ (var "x") (int 0))
          true_
          (if_ (lti_ (var "x") (int 0))
            false_
            (app (var "odd") (subi_ (var "x") (int 1))))))
    ]
    , body) in
utest eval [] (odd_even (app (var "odd") (int 4))) with TmConst (CBool false) in
utest eval [] (odd_even (app (var "odd") (int 3))) with TmConst (CBool true) in
utest eval [] (odd_even (app (var "even") (int 4))) with TmConst (CBool true) in
utest eval [] (odd_even (app (var "even") (int 3))) with TmConst (CBool false) in

let match_ = lam x. lam pat. lam thn. lam els. TmMatch(x, pat, thn, els) in
let conpat = lam ctor. lam pat. ConPat(ctor, pat) in
let tuppat = lam pats. TuplePat(pats) in
let varpat = lam x. VarPat(x) in
let addi_ = lam a. lam b. app_seq (TmConst (CAddi ())) [a, b] in
let num = lam x. app (var "Num") x in
-- lam arg. match arg with Add (Num n1, Num n2) then
--   Num (addi n1 n2)
-- else ()
let add_eval_nested = lambda "arg"
  (match_ (var "arg") (tuppat [(conpat "Num" (varpat "n1")), (conpat "Num" (varpat "n2"))])
    (num (addi_ (var "n1") (var "n2")))
    (unit)) in

let tup = lam x. TmTuple(x) in
let cint = lam x. TmConst (CInt x) in
utest eval [] (wrap_in_decls (app add_eval_nested (tup [num (cint 1), num (cint 2)]))) with TmCon("Num", cint 3) in

()
