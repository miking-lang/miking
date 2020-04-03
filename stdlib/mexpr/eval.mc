-- TODO: Generate unique symbols for data constructors
-- TODO: Add types

include "string.mc"
include "mexpr/ast.mc"

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

lang VarEval = VarAst + VarPat
  sem eval (ctx : {env : Env}) =
  | TmVar x ->
    match lookup x.ident ctx.env with Some t then
      eval ctx t
    else
      error (concat "Unknown variable: " x)

  sem tryMatch (t : Expr) =
  | PVar v -> Some [(v.ident, t)]
end

lang AppEval = AppAst
  sem apply (ctx : {env : Env}) (arg : Expr) =
  | _ -> error "Bad application"

  sem eval (ctx : {env : Env}) =
  | TmApp t -> apply ctx (eval ctx t.rhs) (eval ctx t.lhs)
end


lang FunEval = FunAst + VarEval + AppEval
  syn Type =
  syn Expr =
  | TmClos {ident : String,
            body : Expr,
            env : Env}

  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmClos t -> eval {ctx with env = (cons (t.ident, arg) t.env)} t.body

  sem eval (ctx : {env : Env}) =
  | TmLam t -> TmClos {ident = t.ident,
                       body = t.body,
                       env = ctx.env}
  | TmClos t -> TmClos t
end

-- Fix is only needed for eval. Hence, it is not in ast.mc
lang Fix = FunAst
  syn Expr =
  | TmFix ()
end

lang FixEval = Fix + FunEval
  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmFix _ ->
  match arg with TmClos clos then
    let x = clos.ident in
    let body = clos.body in
    let env2 = clos.env in
    eval {ctx with
          env = (cons (x, TmApp {lhs = TmFix (), rhs = TmClos clos}) env2)} body
  else
    error "Not fixing a function"

  sem eval (ctx : {env : Env}) =
  | TmFix _ -> TmFix ()
 end

lang LetEval = LetAst + VarEval
  sem eval (ctx : {env : Env}) =
  | TmLet t -> eval {ctx with
                     env = cons (t.ident, eval ctx t.body) ctx.env} t.inexpr
end


lang ConstEval = ConstAst
  sem delta (arg : Expr) =

  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmConst c -> delta arg c.val

  sem eval (ctx : {env : Env}) =
  | TmConst c -> TmConst c
end

-- Included for symmetry
lang UnitEval = UnitAst + UnitPat + ConstEval
  sem tryMatch (t : Expr) =
  | PUnit _ ->
    match t with TmConst c then
      match c.val with CUnit _ then
        Some []
      else None ()
    else None ()
end

lang IntEval = IntAst + IntPat
  sem tryMatch (t : Expr) =
  | PInt i ->
    match t with TmConst c then
      match c.val with CInt i2 then
        if eqi i.val i2.val then Some [] else None ()
      else None ()
    else None ()
end


lang ArithIntEval = ArithIntAst + ConstEval
  syn Const =
  | CAddi2 Int
  | CSubi2 Int
  | CMuli2 Int

  sem delta (arg : Expr) =
  | CAddi _ ->
    match arg with TmConst c then
      match c.val with CInt n then
        TmConst {val = CAddi2 n.val}
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
  | CAddi2 n1 ->
    match arg with TmConst c then
      match c.val with CInt n2 then
        TmConst {val = CInt {val = addi n1 n2.val}}
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
  | CSubi _ ->
    match arg with TmConst c then
      match c.val with CInt n then
        TmConst {val = CSubi2 n.val}
      else error "Not subbing a numeric constant"
    else error "Not subbing a constant"
  | CSubi2 n1 ->
    match arg with TmConst c then
      match c.val with CInt n2 then
        TmConst {val = CInt {val = subi n1 n2.val}}
      else error "Not subbing a numeric constant"
    else error "Not subbing a constant"
  | CMuli _ ->
    match arg with TmConst c then
      match c.val with CInt n then
        TmConst {val = CMuli2 n.val}
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
  | CMuli2 n1 ->
    match arg with TmConst c then
      match c.val with CInt n2 then
        TmConst {val = CInt {val = muli n1 n2.val}}
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
end


lang ArithFloatEval = ArithFloatAst + ConstEval
  syn Const =
  | CAddf2 Float
  | CSubf2 Float
  | CMulf2 Float
  | CDivf2 Float

  sem delta (arg : Expr) =
  | CAddf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {val = CAddf2 f.val}
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
  | CAddf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {val = CFloat {val = addf f1 f2.val}}
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
  | CSubf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {val = CSubf2 f.val}
      else error "Not subtracting a numeric constant"
    else error "Not subtracting a constant"
  | CSubf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {val = CFloat {val = subf f1 f2.val}}
      else error "Not subtracting a numeric constant"
    else error "Not subtracting a constant"
  | CMulf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {val = CMulf2 f.val}
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
  | CMulf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {val = CFloat {val = mulf f1 f2.val}}
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
  | CDivf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {val = CDivf2 f.val}
      else error "Not dividing a numeric constant"
    else error "Not dividing a constant"
  | CDivf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {val = CFloat {val = divf f1 f2.val}}
      else error "Not dividing a numeric constant"
    else error "Not dividing a constant"
  | CNegf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {val = CFloat {val = negf f.val}}
      else error "Not negating a numeric constant"
    else error "Not negating a constant"
end

lang BoolEval = BoolAst + BoolPat + ConstEval
  syn Const =
  | CAnd2 Bool
  | COr2 Bool

  sem delta (arg : Expr) =
  | CNot _ ->
    match arg with TmConst c then
      match c.val with CBool b then
        TmConst {val = CBool {val = not b.val}}
      else error "Not negating a boolean constant"
    else error "Not negating a constant"
  | CAnd _ ->
    match arg with TmConst c then
      match c.val with CBool b then
        TmConst {val = CAnd2 b.val}
      else error "Not and-ing a boolean constant"
    else error "Not and-ing a constant"
  | CAnd2 b1 ->
    match arg with TmConst c then
      match c.val with CBool b2 then
        TmConst {val = CBool {val = and b1 b2.val}}
      else error "Not and-ing a boolean constant"
    else error "Not and-ing a constant"
  | COr _ ->
    match arg with TmConst c then
      match c.val with CBool b then
        TmConst {val = COr2 b.val}
      else error "Not or-ing a boolean constant"
    else error "Not or-ing a constant"
  | COr2 b1 ->
    match arg with TmConst c then
      match c.val with CBool b2 then
        TmConst {val = CBool {val = or b1 b2.val}}
      else error "Not or-ing a boolean constant"
    else error "Not or-ing a constant"

  sem eval (ctx : {env : Env}) =
  | TmIf t ->
    match eval ctx t.cond with TmConst c then
      match c.val with CBool b then
        if b.val then eval ctx t.thn else eval ctx t.els
      else error "Condition is not a boolean"
    else error "Condition is not a constant"

  sem tryMatch (t : Expr) =
  | PBool b ->
    let xnor = lam x. lam y. or (and x y) (and (not x) (not y)) in
    match t with TmConst c then
      match c.val with CBool b2 then
        if xnor b.val b2.val then Some [] else None ()
      else None ()
    else None ()
end


lang CmpEval = CmpAst + ConstEval
  syn Const =
  | CEqi2 Int
  | CLti2 Int

  sem delta (arg : Expr) =
  | CEqi _ ->
    match arg with TmConst c then
      match c.val with CInt n then
        TmConst {val = CEqi2 n.val}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CEqi2 n1 ->
    match arg with TmConst c then
      match c.val with CInt n2 then
        TmConst {val = CBool {val = eqi n1 n2.val}}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLti _ ->
    match arg with TmConst c then
      match c.val with CInt n then
        TmConst {val = CLti2 n.val}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLti2 n1 ->
    match arg with TmConst c then
      match c.val with CInt n2 then
        TmConst {val = CBool {val = lti n1 n2.val}}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
end

lang CharEval = CharAst + ConstEval
end

lang SeqEval = SeqAst + ConstEval
  syn Const =
  | CGet2 [Expr]

  sem delta (arg : Expr) =
  | CGet _ ->
    match arg with TmConst c then
      match c.val with CSeq s then
        TmConst {val = CGet2 s.tms}
      else error "Not get of a sequence"
    else error "Not get of a constant"
  | CGet2 tms ->
    match arg with TmConst c then
      match c.val with CInt n then
        get tms n.val
      else error "n in get is not a number"
    else error "n in get is not a constant"

  sem eval (ctx : {env : Env}) =
  | TmSeq s ->
    let vs = map (eval ctx) s.tms in
    TmConst {val = CSeq {s with tms = vs}}
end


lang TupleEval = TupleAst + TuplePat
  sem eval (ctx : {env : Env}) =
  | TmTuple v ->
    let vs = map (eval ctx) v.tms in
    TmTuple {v with tms = vs}
  | TmProj t ->
    match eval ctx t.tup with TmTuple v then
      get v.tms t.idx
    else error "Not projecting from a tuple"

  sem tryMatch (t : Expr) =
  | PTuple p ->
    match t with TmTuple v then
      if eqi (length p.pats) (length v.tms) then
        let results = zipWith tryMatch v.tms p.pats in
        let go = lam left. lam right.
          match (left, right) with (Some l, Some r)
          then Some (concat l r)
          else None () in
        foldl go (Some []) results
      else None ()
    else None ()
end

lang RecLetsEval = RecLetsAst + VarEval + Fix + FixEval + TupleEval + LetEval
  sem eval (ctx : {env : Env}) =
  | TmRecLets t ->
    let foldli = lam f. lam init. lam seq.
      (foldl (lam acc. lam x. (addi acc.0 1, f acc.0 acc.1 x)) (0, init) seq).1 in
    utest foldli (lam i. lam acc. lam x. concat (concat acc (int2string i)) x) "" ["a", "b", "c"]
      with "0a1b2c" in
    let eta_str = fresh "eta" ctx.env in
    let eta_var = TmVar {ident = eta_str} in
    let unpack_from = lam var. lam body.
      foldli
        (lam i. lam bodyacc. lam binding.
          TmLet {ident = binding.ident,
                 tpe = binding.tpe,
                 body = TmLam {ident = eta_str,
                               tpe = None (),
                               body = TmApp {lhs = TmProj {tup = var, idx = i},
                                             rhs = eta_var}},
                 inexpr = bodyacc}
        )
        body
        t.bindings in
    let lst_str = fresh "lst" ctx.env in
    let lst_var = TmVar {ident = lst_str} in
    let func_tuple = TmTuple {tms = map (lam x. x.body) t.bindings} in
    let unfixed_tuple = TmLam {ident = lst_str,
                               tpe = None (),
                               body = unpack_from lst_var func_tuple} in

    eval {ctx with env = cons (lst_str
                              , TmApp {lhs = TmFix ()
                              , rhs = unfixed_tuple}) ctx.env}
         (unpack_from lst_var t.inexpr)
end

lang RecordEval = RecordAst
  sem eval (ctx : {env : Env}) =
  | TmRecord t ->
    let bs = map (lam b. {b with value = eval ctx b.value}) t.bindings in
    TmRecord {t with bindings = bs}
  | TmRecordProj t ->
    recursive let reclookup = lam key. lam bindings.
      if eqi (length bindings) 0 then
        error "Could not project from Record"
      else if eqstr (head bindings).key key then
        (head bindings).value
      else
        reclookup key (tail bindings)
    in
    match eval ctx t.rec with TmRecord t2 then
      reclookup t.key t2.bindings
    else error "Not projecting a Record"
  | TmRecordUpdate u ->
    match eval ctx u.rec with TmRecord t then
      recursive let recupdate = lam bindings.
        if eqi (length bindings) 0 then
          [{key = u.key, value = u.value}]
        else
          let e = head bindings in
          if eqstr u.key e.key then
            cons {key = u.key, value = u.value} (tail bindings)
          else
            cons e (recupdate (tail bindings))
      in
      TmRecord {t with bindings = recupdate t.bindings}
    else error "Not updating a record"
end

lang DataEval = DataAst + DataPat + AppEval
  syn Expr =
  | TmCon {ident : String, body : Expr}

  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmConFun t -> TmCon {ident = t.ident, body = arg}

  sem eval (ctx : {env : Env}) =
  | TmConDef t -> eval {ctx with
                        env = cons (t.ident , TmConFun {ident = t.ident})
                                   ctx.env
                       } t.inexpr
  | TmConFun t -> TmConFun t
  | TmCon t -> TmCon t

  sem tryMatch (t : Expr) =
  | PCon x -> -- INCONSISTENCY: this won't follow renames in the constructor, but the ml interpreter will
    match t with TmCon cn then
      let constructor = cn.ident in
      let subexpr = cn.body in
      if eqstr x.ident constructor
        then tryMatch subexpr x.subpat
        else None ()
    else None ()
end


lang MatchEval = MatchAst
  sem eval (ctx : {env : Env}) =
  | TmMatch t ->
    match tryMatch (eval ctx t.target) t.pat with Some newEnv then
      eval {ctx with env = concat newEnv ctx.env} t.thn
    else eval ctx t.els

  sem tryMatch (t : Expr) =
  | _ -> None ()
end


lang UtestEval = UtestAst
  sem eq (e1 : Expr) =
  | _ -> error "Equality not defined for expression"

  sem eval (ctx : {env : Env}) =
  | TmUtest t ->
    let v1 = eval ctx t.test in
    let v2 = eval ctx t.expected in
    let _ = if eq v1 v2 then print "Test passed\n" else print "Test failed\n" in
    eval ctx t.next
end


-- TODO: Add more types! Think about design

lang MExprEval = FunEval + LetEval + RecLetsEval + SeqEval + TupleEval + RecordEval
               + DataEval + UtestEval + IntEval + ArithIntEval + ArithFloatEval
               + BoolEval + CmpEval + CharEval + UnitEval + MatchEval
               + DynTypeAst + UnitTypeAst + SeqTypeAst + TupleTypeAst + RecordTypeAst
               + DataTypeAst + ArithTypeAst + BoolTypeAst + AppTypeAst
  sem eq (e1 : Expr) =
  | TmConst c2 -> constExprEq c2.val e1
  | TmCon d2 -> dataEq d2.ident d2.body e1
  | TmConFun k -> enumEq k.ident e1
  | TmTuple t -> tupleEq t.tms e1
  | TmSeq s -> seqEq s.tms e1
  | TmRecord t -> recordEq t.bindings e1

  sem constExprEq (c1 : Const) =
  | TmConst c2 -> constEq c1 c2.val
  | _ -> false

  sem constEq (c1 : Const) =
  | CUnit _ -> isUnit c1
  | CInt n2 -> intEq n2.val c1
  | CBool b2 -> boolEq b2.val c1
  | CChar chr2 -> charEq chr2.val c1

  sem isUnit =
  | CUnit _ -> true
  | _ -> false

  sem intEq (n1 : Int) =
  | CInt n2 -> eqi n1 n2.val
  | _ -> false

  sem boolEq (b1 : Bool) =
  | CBool b2 -> or (and b1 b2.val) (and (not b1) (not b2.val))
  | _ -> false

  sem charEq (c1 : Char) =
  | CChar c2 -> eqi (char2int c1) (char2int c2.val)
  | _ -> false

  sem dataEq (k1 : String) (v1 : Expr) =
  | TmCon d2 ->
    let k2 = d2.ident in
    let v2 = d2.body in
    and (eqstr k1 k2) (eq v1 v2)
  | _ -> false

  sem enumEq (k1 : String) =
  | TmConFun k2 -> eqstr k1 k2.ident
  | _ -> false

  sem tupleEq (tms1 : [Expr]) =
  | TmTuple t ->
    and (eqi (length tms1) (length t.tms))
        (all (lam b. b) (zipWith eq tms1 t.tms))
  | _ -> false

  sem recordEq (bindings1 : [{key : String, value : Expr}]) =
  | TmRecord t ->
    and (eqi (length bindings1) (length t.bindings))
        (all (lam e1. any (lam e2. and (eqstr e1.key e2.key)
                                       (eq e1.value e2.value))
                          (bindings1))
             (t.bindings))
  | _ -> false

  sem seqEq (seq1 : [Expr]) =
  | TmSeq s ->
    and (eqi (length seq1) (length s.tms))
        (all (lam b.b) (zipWith eq seq1 s.tms))
  | _ -> false
end

mexpr

use MExprEval in
let id = TmLam {ident = "x",
                tpe = None (),
                body = TmVar {ident = "x"}}
in
let bump = TmLam {ident = "x",
                  tpe = None (),
                  body = TmApp {lhs = TmApp {lhs = TmConst {val = CAddi ()},
                                             rhs = TmVar {ident = "x"}},
                                rhs = TmConst {val = CInt {val = 1}}}}
in
let fst = TmLam {ident = "t",
                 tpe = None (),
                 body = TmProj {tup = TmVar {ident = "t"},
                                idx = 0}}
in
let appIdUnit = TmApp {lhs = id,
                       rhs = TmConst {val = CUnit ()}}
in
let appBump3 = TmApp {lhs = bump,
                      rhs = TmConst {val = CInt {val = 3}}} in
let appFst = TmApp {lhs = fst,
                    rhs = TmTuple {tms = [TmApp {lhs = TmConst {val = CNot ()},
                                                 rhs = TmConst {val = CBool {val = false}}},
                                          TmApp {lhs = TmApp {lhs = TmConst {val = CAddi ()},
                                                              rhs = TmConst {val = CInt {val = 1}}},
                                                 rhs = TmConst {val = CInt {val = 2}}}]}}
in
utest eval {env = []} appIdUnit with TmConst {val = CUnit ()} in
utest eval {env = []} appBump3 with TmConst {val = CInt {val = 4}} in
utest eval {env = []} appFst with TmConst {val = CBool {val = true}} in

let unit = TmConst {val = CUnit ()} in

let dataDecl = TmConDef {ident = "Foo",
                         tpe = None,
                         inexpr = TmMatch {target = TmApp {lhs = TmVar {ident = "Foo"},
                                                           rhs = TmTuple {tms = [unit, unit]}},
                                           pat = PCon {ident = "Foo",
                                                       subpat = PVar {ident = "u"}},
                                           thn = TmProj {tup = TmVar {ident = "u"},
                                                         idx = 0},
                                           els = id}}
in
utest eval {env = []} dataDecl with unit in

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
-- utest eval {env = []} utest_test1 with unit in
-- utest eval {env = []} utest_test2 with unit in
-- utest eval {env = []} utest_test3 with unit in

-- Implementing an interpreter
let num = lam n. TmApp {lhs = TmVar {ident = "Num"},
                        rhs = TmConst {val = CInt {val = n}}}
in
let one = num 1 in -- Num 1
let two = num 2 in -- Num 2
let three = num 3 in -- Num 3
let add = lam n1. lam n2. TmApp {lhs = TmVar {ident = "Add"},
                                 rhs = TmTuple {tms = [n1, n2]}}
in
let addOneTwo = add one two in -- Add (Num 1, Num 2)
let num_case = lam arg. lam els. -- match arg with Num n then Num n else els
    TmMatch {target = arg,
             pat = PCon {ident = "Num",
                         subpat = PVar {ident = "n"}},
             thn = TmApp {lhs = TmVar {ident = "Num"},
                          rhs = TmVar {ident = "n"}},
             els = els}
in
-- match arg with Add t then
--   let e1 = t.0 in
--   let e2 = t.1 in
--   match eval e1 with Num n1 then
--     match eval e2 with Num n2 then
--       Num (addi n1 n2)
--     else repl()
--   else ()
-- else els
let result = TmApp {lhs = TmVar {ident = "Num"},
                    rhs = TmApp {lhs = TmApp {lhs = TmConst {val = CAddi ()},
                                              rhs = TmVar {ident = "n1"}},
                                 rhs = TmVar {ident = "n2"}}}
in
let matchInner = TmMatch {target = TmApp {lhs = TmVar {ident = "eval"},
                                          rhs = TmVar {ident = "e2"}},
                          pat = PCon {ident = "Num",
                                      subpat = PVar {ident = "n2"}},
                          thn = result,
                          els = unit}
in
let matchOuter = TmMatch {target = TmApp {lhs = TmVar {ident = "eval"},
                                          rhs = TmVar {ident = "e1"}},
                          pat = PCon {ident = "Num",
                                      subpat = PVar {ident = "n1"}},
                          thn = matchInner,
                          els = unit}
in
let deconstruct = lam t. TmLet {ident = "e1",
                                tpe = None (),
                                body = TmProj {tup = t,
                                               idx = 0},
                                inexpr = TmLet {ident = "e2",
                                                tpe = None (),
                                                body = TmProj {tup = t,
                                                               idx = 1},
                                                inexpr = matchOuter}}
in
let addCase = lam arg. lam els. TmMatch {target = arg,
                                         pat = PCon {ident = "Add",
                                                     subpat = PVar {ident = "t"}},
                                         thn = deconstruct (TmVar {ident = "t"}),
                                         els = els}
in
 -- fix (lam eval. lam e. match e with then ... else ())
let evalFn = TmApp {lhs = TmFix (),
                    rhs = TmLam {ident = "eval",
                                 tpe = None (),
                                 body = TmLam {ident = "e",
                                               tpe = None (),
                                               body = num_case (TmVar {ident = "e"}) (addCase (TmVar {ident = "e"}) unit)}}}
in

-- con Num in con Add in let eval = ... in t
let wrapInDecls = lam t. TmConDef {ident = "Num",
                                   tpe = None (),
                                   inexpr = TmConDef {ident = "Add",
                                                      tpe = None (),
                                                      inexpr = TmLet {ident = "eval",
                                                                      tpe = None (),
                                                                      body = evalFn,
                                                                      inexpr = t}}}
in

let evalAdd1 = wrapInDecls (TmApp {lhs = TmVar {ident = "eval"},
                                   rhs = addOneTwo}) in
let addOneTwoThree = add (add one two) three in
let evalAdd2 = wrapInDecls (TmApp {lhs = TmVar {ident = "eval"},
                                   rhs = addOneTwoThree}) in

utest eval {env = []} evalAdd1 with TmCon {ident = "Num", body = TmConst {val = CInt {val = 3}}} in
utest eval {env = []} evalAdd2 with TmCon {ident = "Num", body = TmConst {val = CInt {val = 6}}} in

let evalUTestIntInUnit = TmUtest {
    test = TmConst {val = CInt {val = 3}},
    expected = TmConst {val = CInt {val = 3}},
    next = TmConst {val = CUnit ()}}
in

utest eval {env = []} evalUTestIntInUnit with TmConst {val = CUnit ()} in

let app = lam f. lam x. TmApp {lhs = f, rhs = x} in
let appSeq = lam f. lam seq. foldl app f seq in
let var = lam v. TmVar {ident = v} in
let int = lam i. TmConst {val = CInt {val = i}} in
let lambda = lam var. lam body. TmLam {ident = var,
                                       tpe = None (),
                                       body = body}
in
let if_ = lam cond. lam th. lam el. TmIf {cond = cond,
                                          thn = th,
                                          els = el}
in
let true_ = TmConst {val = CBool {val = true}} in
let false_ = TmConst {val = CBool {val = false}} in
let eqi_ = lam a. lam b. appSeq (TmConst {val = CEqi ()}) [a, b] in
let lti_ = lam a. lam b. appSeq (TmConst {val = CLti ()}) [a, b] in
let subi_ = lam a. lam b. appSeq (TmConst {val = CSubi ()}) [a, b] in
let oddEven = lam bdy.
  let odd = {ident = "odd",
             tpe = None (),
             body = lambda "x"
                    (if_ (eqi_ (var "x") (int 1))
                      true_
                      (if_ (lti_ (var "x") (int 1))
                        false_
                        (app (var "even") (subi_ (var "x") (int 1)))))}
  in
  let even = {ident = "even",
              tpe = None (),
              body = lambda "x"
                     (if_ (eqi_ (var "x") (int 0))
                       true_
                       (if_ (lti_ (var "x") (int 0))
                         false_
                         (app (var "odd") (subi_ (var "x") (int 1)))))}
  in
  TmRecLets {bindings = [odd, even],
             inexpr = bdy}
in
utest eval {env = []} (oddEven (app (var "odd") (int 4))) with TmConst {val = CBool {val = false}} in
utest eval {env = []} (oddEven (app (var "odd") (int 3))) with TmConst {val = CBool {val = true}} in
utest eval {env = []} (oddEven (app (var "even") (int 4))) with TmConst {val = CBool {val = true}} in
utest eval {env = []} (oddEven (app (var "even") (int 3))) with TmConst {val = CBool {val = false}} in

let match_ = lam x. lam pat. lam thn. lam els. TmMatch {target = x,
                                                        pat = pat,
                                                        thn = thn,
                                                        els = els}
in
let conpat = lam ctor. lam pat. PCon {ident = ctor,
                                      subpat = pat}
in
let tuppat = lam pats. PTuple {pats = pats} in
let varpat = lam x. PVar {ident = x} in
let addi_ = lam a. lam b. appSeq (TmConst {val = CAddi ()}) [a, b] in
let num = lam x. app (var "Num") x in
-- lam arg. match arg with Add (Num n1, Num n2) then
--   Num (addi n1 n2)
-- else ()
let addEvalNested = lambda "arg"
  (match_ (var "arg") (tuppat [(conpat "Num" (varpat "n1")), (conpat "Num" (varpat "n2"))])
    (num (addi_ (var "n1") (var "n2")))
    (unit)) in

let tup = lam x. TmTuple {tms = x} in
utest eval {env = []} (wrapInDecls (app addEvalNested (tup [num (int 1), num (int 2)]))) with TmCon {ident = "Num", body = int 3} in



let record_ = TmRecord {bindings = []} in
let recAdd = lam key. lam value. lam rec.
  match rec with TmRecord t then
    TmRecord {t with bindings = cons {key = key, value = value} t.bindings}
  else error "Not adding to a Record"
in
let recAddTups = lam tups. lam rec.
  foldl (lam recacc. lam t. recAdd t.0 t.1 recacc) rec tups in

let recordproj_ = lam key. lam rec. TmRecordProj {rec = rec,
                                                  key = key}
in
let recordupdate_ = lam key. lam value. lam rec. TmRecordUpdate {rec = rec,
                                                                 key = key,
                                                                 value = value}
in

let recordProj = TmLet {ident = "myrec",
                        tpe = None (),
                        body = recAddTups [("a", int 10),("b", int 37),("c", int 23)] record_,
                        inexpr = TmRecordProj {rec = var "myrec",
                                               key = "b"}} in

let recordUpdate = TmLet {ident = "myrec",
                          tpe = None (),
                          body = recAddTups [("a", int 10),("b", int 37),("c", int 23)] record_,
                          inexpr = TmRecordProj {rec = recordupdate_ "c" (int 11) (var "myrec"),
                                                 key = "c"}} in

-- This updates the record with a non-existent value, should this case be allowed?
let recordUpdate2 = TmLet {ident = "myrec",
                           tpe = None (),
                           body = recAddTups [("a", int 10),("b", int 37),("c", int 23)] record_,
                           inexpr = TmRecordProj {rec = recordupdate_ "d" (int 1729) (var "myrec"),
                                                  key = "d"}} in

utest eval {env = []} recordProj with TmConst {val = CInt {val = 37}} in
utest eval {env = []} recordUpdate with TmConst {val = CInt {val = 11}} in
utest eval {env = []} recordUpdate2 with TmConst {val = CInt {val = 1729}} in

let evalUTestRecordInUnit = TmUtest {
    test = recAddTups [("a", int 10), ("b", int 13)] record_,
    expected = recAddTups [("b", int 13), ("a", int 10)] record_,
    next = TmConst {val = CUnit ()}}
in
utest eval {env = []} evalUTestRecordInUnit with TmConst {val = CUnit ()} in

let float = lam f. TmConst {val = CFloat {val = f}} in
let addf_ = lam a. lam b. appSeq (TmConst {val = CAddf ()}) [a, b] in
let subf_ = lam a. lam b. appSeq (TmConst {val = CSubf ()}) [a, b] in
let mulf_ = lam a. lam b. appSeq (TmConst {val = CMulf ()}) [a, b] in
let divf_ = lam a. lam b. appSeq (TmConst {val = CDivf ()}) [a, b] in
let negf_ = lam a. appSeq (TmConst {val = CNegf ()}) [a] in

utest eval {env = []} (addf_ (float 1.) (float 2.)) with float 3. in
utest eval {env = []} (subf_ (float 1.) (float 2.)) with float (negf 1.) in
utest eval {env = []} (mulf_ (float 1.) (float 2.)) with float 2. in
utest eval {env = []} (divf_ (float 1.) (float 2.)) with float 0.5 in
utest eval {env = []} (negf_ (float 1.)) with float (negf 1.) in

utest eval {env = []} (app id (int 1)) with int 1 in

utest eval {env = []} (app (lambda "x" (app (var "x") (int 1))) id)
with int 1 in

utest eval {env = []}
           (appSeq (lambda "x" (lambda "y" (addi_ (var "x") (var "y"))))
                   [int 1, int 2])
with int 3 in

utest eval {env = []}
           (appSeq (lambda "x" (lambda "y" (addi_ (var "x") (int 1))))
                   [int 1, int 2])
with int 2 in

utest eval {env = []}
           (appSeq (lambda "x" (lambda "x" (addi_ (var "x") (int 1))))
                   [int 1, int 2])
with int 3 in
()
