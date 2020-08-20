-- TODO: Generate unique symbols for data constructors
-- TODO: Add types

include "string.mc"
include "assoc.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
-- include "mexpr/pprint.mc"

----------------------------
-- EVALUATION ENVIRONMENT --
----------------------------
-- TODO Symbolize changes

type Env = [(String, Expr)]

recursive
  let lookup = lam x. lam env.
    if eqi (length env) 0
    then None ()
    else if eqstr (head env).0 x
    then Some (head env).1
    else lookup x (tail env)
end

let fresh : String -> Env -> String = lam var. lam env.
  match lookup var env with None () then
    var
  else
    recursive let find_free = lam n.
      let new = concat var (int2string n) in
      match lookup new env with None () then
        new
      else
        find_free (addi n 1)
    in find_free 0


-----------
-- TERMS --
-----------

lang VarEval = VarAst
  sem eval (ctx : {env : Env}) =
  | TmVar x ->
    match lookup x.ident ctx.env with Some t then
      eval ctx t
    else
      error (concat "Unknown variable: " x)
end

lang AppEval = AppAst
  sem apply (ctx : {env : Env}) (arg : Expr) =
  | _ -> error "Bad application"

  sem eval (ctx : {env : Env}) =
  | TmApp t -> apply ctx (eval ctx t.rhs) (eval ctx t.lhs)
end

lang FunEval = FunAst + VarEval + AppEval
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

lang LetEval = LetAst + VarEval
  sem eval (ctx : {env : Env}) =
  | TmLet t -> eval {ctx with
                     env = cons (t.ident, eval ctx t.body) ctx.env} t.inexpr
end

-- Fixpoint operator is only needed for eval. Hence, it is not in ast.mc
lang FixAst = FunAst
  syn Expr =
  | TmFix ()
end

lang FixEval = FixAst + FunEval
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

lang RecordEval = RecordAst
  sem eval (ctx : {env : Env}) =
  | TmRecord t ->
    let bs = map (lam b. (b.0, (eval ctx b.1))) t.bindings in
    TmRecord {t with bindings = bs}
  | TmRecordUpdate u ->
    let mem = assocMem {eq = eqstr} in
    let insert = assocInsert {eq = eqstr} in
    match eval ctx u.rec with TmRecord t then
      if mem u.key t.bindings then
        TmRecord { bindings = insert u.key (eval ctx u.value) t.bindings }
      else error "Key does not exist in record"
    else error "Not updating a record"
end

lang RecLetsEval = RecLetsAst + VarEval + FixAst + FixEval + RecordEval + LetEval
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
                               body = TmApp {lhs = tupleproj_ i var,
                                             rhs = eta_var}},
                 inexpr = bodyacc}
        )
        body
        t.bindings in
    let lst_str = fresh "lst" ctx.env in
    let lst_var = TmVar {ident = lst_str} in
    let func_tuple = tuple_ (map (lam x. x.body) t.bindings) in
    let unfixed_tuple = TmLam {ident = lst_str,
                               tpe = None (),
                               body = unpack_from lst_var func_tuple} in

    eval {ctx with env = cons (lst_str
                              , TmApp {lhs = TmFix ()
                              , rhs = unfixed_tuple}) ctx.env}
         (unpack_from lst_var t.inexpr)
end

lang ConstEval = ConstAst
  sem delta (arg : Expr) =

  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmConst c -> delta arg c.val

  sem eval (ctx : {env : Env}) =
  | TmConst c -> TmConst c
end

lang DataEval = DataAst + AppEval
  sem eval (ctx : {env : Env}) =
  | TmConDef t -> eval ctx t.inexpr
  | TmConApp t -> TmConApp {t with body = eval ctx t.body}
end

lang MatchEval = MatchAst
  sem eval (ctx : {env : Env}) =
  | TmMatch t ->
    match tryMatch ctx.env (eval ctx t.target) t.pat with Some newEnv then
      eval {ctx with env = concat newEnv ctx.env} t.thn
    else eval ctx t.els

  sem tryMatch (env : Env) (t : Expr) =
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

lang SeqEval = SeqAst
  sem eval (ctx : {env : Env}) =
  | TmSeq s ->
    let vs = map (eval ctx) s.tms in
    TmSeq {s with tms = vs}
end

lang NeverEval = NeverAst
  --TODO
end

---------------
-- CONSTANTS --
---------------
-- All constants in boot have not been implemented. Missing ones can be added
-- as needed.

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

-- TODO Move pattern matching to own fragment?
lang BoolEval = BoolAst + ConstEval
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
end

lang CmpIntEval = CmpIntAst + ConstEval
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

lang CmpFloatEval = CmpFloatAst + ConstEval
  syn Const =
  | CEqf2 Float
  | CLtf2 Float

  sem delta (arg : Expr) =
  | CEqf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {val = CEqf2 f.val}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CEqf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {val = CBool {val = eqf f1 f2.val}}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLtf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {val = CLtf2 f.val}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLtf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {val = CBool {val = ltf f1 f2.val}}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
end

lang SymbEval = SymbAst + ConstEval
end

lang CmpSymbEval = CmpSymbAst + ConstEval
  syn Const =
  | CEqs2 Symb

  sem delta (arg : Expr) =
  | CEqs _ ->
    match arg with TmConst {val = CSymb s} then
      TmConst {val = CEqs2 s.val}
    else error "First argument in eqs is not a symbol"
  | CEqs2 s1 ->
    match arg with TmConst {val = CSymb s2} then
      TmConst {val = CBool {val = eqs s1 s2.val}}
    else error "Second argument in eqs is not a symbol"
end

-- TODO Remove constants no longer available in boot?
lang SeqOpEval = SeqOpAst + IntAst + BoolAst + ConstEval
  syn Const =
  | CGet2 [Expr]
  | CCons2 Expr
  | CSnoc2 [Expr]
  | CConcat2 [Expr]

  sem delta (arg : Expr) =
  | CGet _ ->
    match arg with TmSeq s then
      TmConst {val = CGet2 s.tms}
    else error "Not a get of a constant sequence"
  | CGet2 tms ->
    match arg with TmConst {val = CInt n} then
      get tms n.val
    else error "n in get is not a number"
  | CCons _ ->
    TmConst {val = CCons2 arg}
  | CCons2 tm ->
    match arg with TmSeq s then
      TmSeq {tms = cons tm s.tms}
    else error "Not a cons of a constant sequence"
  | CSnoc _ ->
    match arg with TmSeq s then
      TmConst {val = CSnoc2 s.tms}
    else error "Not a snoc of a constant sequence"
  | CSnoc2 tms ->
    TmSeq {tms = snoc tms arg}
  | CConcat _ ->
    match arg with TmSeq s then
      TmConst {val = CConcat2 s.tms}
    else error "Not a concat of a constant sequence"
  | CConcat2 tms ->
    match arg with TmSeq s then
      TmSeq {tms = concat tms s.tms}
    else error "Not a concat of a constant sequence"
  | CLength _ ->
    match arg with TmSeq s then
      TmConst {val = CInt {val = (length s.tms)}}
    else error "Not length of a constant sequence"
  | CHead _ ->
    match arg with TmSeq s then
      head s.tms
    else error "Not head of a constant sequence"
  | CTail _ ->
    match arg with TmSeq s then
      TmSeq {tms = tail s.tms}
    else error "Not tail of a constant sequence"
  | CNull _ ->
    match arg with TmSeq s then
      if null s.tms
      then TmConst {val = CBool {val = true}}
      else TmConst {val = CBool {val = false}}
    else error "Not null of a constant sequence"
  | CReverse _ ->
    match arg with TmSeq s then
      TmSeq {tms = reverse s.tms}
    else error "Not reverse of a constant sequence"
end

--------------
-- PATTERNS --
--------------

lang VarPatEval = VarPat
  sem tryMatch (env : Env) (t : Expr) =
  | PVar v -> Some (cons (v.ident, t) env)
end

lang SeqTotPatEval = SeqTotPat
  -- TODO
end

lang SeqEdgPatEval = SeqEdgPat
  -- TODO
end

lang RecordPatEval = RecordAst + RecordPat
  sem tryMatch (env : Env) (t : Expr) =
  | PRecord r ->
    match t with TmRecord {bindings = bs} then
      recursive let recurse = lam env. lam pbs.
        match pbs with [(k,p)] ++ pbs then
          match assocLookup {eq = eqstr} k bs with Some v then
            match tryMatch env v p with Some env then
              recurse env pbs
            else None ()
          else None ()
        else match pbs with [] then Some env
        else never
      in
      recurse env r.bindings
    else None ()
end

lang DataPatEval = DataAst + DataPat
  sem tryMatch (env : Env) (t : Expr) =
  | PCon x -> -- INCONSISTENCY: this won't follow renames in the constructor, but the ml interpreter will
    match t with TmConApp cn then
      let constructor = cn.ident in
      let subexpr = cn.body in
      if eqstr x.ident constructor
        then tryMatch env subexpr x.subpat
        else None ()
    else None ()
end

lang IntPatEval = IntAst + IntPat
  sem tryMatch (env : Env) (t : Expr) =
  | PInt i ->
    match t with TmConst c then
      match c.val with CInt i2 then
        if eqi i.val i2.val then Some env else None ()
      else None ()
    else None ()
end

lang CharPatEval = CharAst + ConstEval
end

lang BoolPatEval = BoolAst + BoolPat
  sem tryMatch (env : Env) (t : Expr) =
  | PBool b ->
    let xnor = lam x. lam y. or (and x y) (and (not x) (not y)) in
    match t with TmConst c then
      match c.val with CBool b2 then
        if xnor b.val b2.val then Some env else None ()
      else None ()
    else None ()
end

lang AndPatEval = AndPat
  -- TODO
end

lang OrPatEval = OrPat
  -- TODO
end

lang NotPatEval = NotPat
  -- TODO
end

-------------------------
-- MEXPR EVAL FRAGMENT --
-------------------------

lang MExprEval =

  -- Terms
  VarEval + AppEval + FunEval + FixEval + RecordEval + RecLetsEval + ConstEval + DataEval + MatchEval + UtestEval + SeqEval + NeverEval

  -- Constants
  + ArithIntEval + ArithFloatEval + BoolEval + CmpIntEval + CmpFloatEval + SymbEval + CmpSymbEval + SeqOpEval

  -- Patterns
  + VarPatEval + SeqTotPatEval + SeqEdgPatEval + RecordPatEval + DataPatEval + IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval

  sem eq (e1 : Expr) =
  | TmConst c2 -> constExprEq c2.val e1
  | TmConApp d2 -> dataEq d2.ident d2.body e1
  | TmSeq s -> seqEq s.tms e1
  | TmRecord t -> recordEq t.bindings e1

  sem constExprEq (c1 : Const) =
  | TmConst c2 -> constEq c1 c2.val
  | _ -> false

  sem constEq (c1 : Const) =
  | CInt n2 -> intEq n2.val c1
  | CBool b2 -> boolEq b2.val c1
  | CChar chr2 -> charEq chr2.val c1

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
  | TmConApp d2 ->
    let k2 = d2.ident in
    let v2 = d2.body in
    and (eqstr k1 k2) (eq v1 v2)
  | _ -> false

  sem recordEq (bindings1 : AssocMap) = -- AssocMap String Expr
  | TmRecord t ->
    and (eqi (length bindings1) (length t.bindings))
        (all (lam e1. any (lam e2. and (eqstr e1.0 e2.0)
                                       (eq e1.1 e2.1))
                          (bindings1))
             (t.bindings))
  | _ -> false

  sem seqEq (seq1 : [Expr]) =
  | TmSeq s ->
    and (eqi (length seq1) (length s.tms))
        (all (lam b.b) (zipWith eq seq1 s.tms))
  | _ -> false
end


-----------
-- TESTS --
-----------

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
                 body = tupleproj_ 0 (var_"t")}
in
let appIdUnit = TmApp {lhs = id,
                       rhs = unit_}
in
let appBump3 = TmApp {lhs = bump,
                      rhs = TmConst {val = CInt {val = 3}}} in
let appFst = TmApp {lhs = fst,
                    rhs = tuple_ [TmApp {lhs = TmConst {val = CNot ()},
                                                 rhs = TmConst {val = CBool {val = false}}},
                                          TmApp {lhs = TmApp {lhs = TmConst {val = CAddi ()},
                                                              rhs = TmConst {val = CInt {val = 1}}},
                                                 rhs = TmConst {val = CInt {val = 2}}}]}
in
utest eval {env = []} appIdUnit with unit_ in
utest eval {env = []} appBump3 with TmConst {val = CInt {val = 4}} in
utest eval {env = []} appFst with TmConst {val = CBool {val = true}} in

let dataDecl = TmConDef {
  ident = "Foo",
  tpe = None(),
  inexpr = TmMatch {
    target = TmConApp {
      ident = "Foo",
      body = tuple_ [unit_, unit_]
    },
    pat = PCon {
      ident = "Foo",
      subpat = PVar {ident = "u"}
    },
    thn = tupleproj_ 0 (var_ "u"),
    els = id
  }
} in

utest eval {env = []} dataDecl with unit_ in

-- Commented out to not clutter the test suite
-- let utest_test1 = TmUtest (TmConst (CInt 1), TmConst (CInt 1), unit_) in
-- let utest_test2 =
--   TmUtest (tuple_ [TmConst (CInt 1),
--                     TmApp (TmApp (TmConst CAddi, TmConst (CInt 1)), TmConst (CInt 2))]
--           ,tuple_ [TmConst (CInt 1), TmConst (CInt 3)], unit_)
-- in
-- let utest_test3 =
--   TmConDef ("Foo",
--     TmUtest (TmApp (TmVar "Foo", unit_), TmApp (TmVar "Foo", unit_), unit_))
-- in
-- utest eval {env = []} utest_test1 with unit_ in
-- utest eval {env = []} utest_test2 with unit_ in
-- utest eval {env = []} utest_test3 with unit_ in

-- Implementing an interpreter
let num = lam n.
  TmConApp {ident = "Num", body = TmConst {val = CInt {val = n}}}
in
let one = num 1 in -- Num 1
let two = num 2 in -- Num 2
let three = num 3 in -- Num 3
let add = lam n1. lam n2.
  TmConApp {ident = "Add", body = tuple_ [n1, n2]}
in
let addOneTwo = add one two in -- Add (Num 1, Num 2)
let num_case = lam arg. lam els. -- match arg with Num n then Num n else els
    TmMatch {target = arg,
             pat = PCon {ident = "Num",
                         subpat = PVar {ident = "n"}},
             thn = TmConApp {ident = "Num", body = TmVar {ident = "n"}},
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
let result = TmConApp {
               ident = "Num",
               body = TmApp {lhs = TmApp {lhs = TmConst {val = CAddi ()},
                                              rhs = TmVar {ident = "n1"}},
                                 rhs = TmVar {ident = "n2"}}}
in
let matchInner = TmMatch {target = TmApp {lhs = TmVar {ident = "eval"},
                                          rhs = TmVar {ident = "e2"}},
                          pat = PCon {ident = "Num",
                                      subpat = PVar {ident = "n2"}},
                          thn = result,
                          els = unit_}
in
let matchOuter = TmMatch {target = TmApp {lhs = TmVar {ident = "eval"},
                                          rhs = TmVar {ident = "e1"}},
                          pat = PCon {ident = "Num",
                                      subpat = PVar {ident = "n1"}},
                          thn = matchInner,
                          els = unit_}
in
let deconstruct = lam t. TmLet {ident = "e1",
                                tpe = None (),
                                body = tupleproj_ 0 t,
                                inexpr = TmLet {ident = "e2",
                                                tpe = None (),
                                                body = tupleproj_ 1 t,
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
                                               body = num_case (TmVar {ident = "e"}) (addCase (TmVar {ident = "e"}) unit_)}}}
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

utest eval {env = []} evalAdd1 with TmConApp {ident = "Num", body = TmConst {val = CInt {val = 3}}} in
utest eval {env = []} evalAdd2 with TmConApp {ident = "Num", body = TmConst {val = CInt {val = 6}}} in

let evalUTestIntInUnit = TmUtest {
    test = TmConst {val = CInt {val = 3}},
    expected = TmConst {val = CInt {val = 3}},
    next = unit_}
in

utest eval {env = []} evalUTestIntInUnit with unit_ in

let oddEven = lam bdy.
  let odd = {ident = "odd",
             tpe = None (),
             body = ulam_ "x"
                    (if_ (eqi_ (var_ "x") (int_ 1))
                      true_
                      (if_ (lti_ (var_ "x") (int_ 1))
                        false_
                        (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))}
  in
  let even = {ident = "even",
              tpe = None (),
              body = ulam_ "x"
                     (if_ (eqi_ (var_ "x") (int_ 0))
                       true_
                       (if_ (lti_ (var_ "x") (int_ 0))
                         false_
                         (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))}
  in
  TmRecLets {bindings = [odd, even],
             inexpr = bdy}
in
utest eval {env = []} (oddEven (app_ (var_ "odd") (int_ 4))) with TmConst {val = CBool {val = false}} in
utest eval {env = []} (oddEven (app_ (var_ "odd") (int_ 3))) with TmConst {val = CBool {val = true}} in
utest eval {env = []} (oddEven (app_ (var_ "even") (int_ 4))) with TmConst {val = CBool {val = true}} in
utest eval {env = []} (oddEven (app_ (var_ "even") (int_ 3))) with TmConst {val = CBool {val = false}} in

let num = lam x. TmConApp { ident = "Num", body = x } in
-- lam arg. match arg with Add (Num n1, Num n2) then
--   Num (addi n1 n2)
-- else ()
let addEvalNested = ulam_ "arg"
  (match_ (var_ "arg") (ptuple_ [(pcon_ "Num" (pvar_ "n1")), (pcon_ "Num" (pvar_ "n2"))])
    (num (addi_ (var_ "n1") (var_ "n2")))
    (unit_)) in

utest eval {env = []} (wrapInDecls (app_ addEvalNested (tuple_ [num (int_ 1), num (int_ 2)]))) with TmConApp {ident = "Num", body = int_ 3} in


let recordProj = TmLet {ident = "myrec",
                        tpe = None (),
                        body = record_add_bindings [("a", int_ 10),("b", int_ 37),("c", int_ 23)] record_empty,
                        inexpr = recordproj_ "b" (var_ "myrec")} in

let recordUpdate = TmLet {ident = "myrec",
                          tpe = None (),
                          body = record_add_bindings [("a", int_ 10),("b", int_ 37),("c", int_ 23)] record_empty,
                          inexpr =
                            recordproj_ "c"
                              (recordupdate_ "c" (int_ 11) (var_ "myrec"))} in

let recordUpdate2 = TmLet {ident = "myrec",
                           tpe = None (),
                           body = record_add_bindings [("a", int_ 10),("b", int_ 37),("c", int_ 23)] record_empty,
                           inexpr =
                             recordproj_ "a"
                               (recordupdate_ "a" (int_ 1729) (var_ "myrec"))} in

utest eval {env = []} recordProj with TmConst {val = CInt {val = 37}} in
utest eval {env = []} recordUpdate with TmConst {val = CInt {val = 11}} in
utest eval {env = []} recordUpdate2 with TmConst {val = CInt {val = 1729}} in

let recordUpdateNonValue =
  (recordupdate_ "a" (addi_ (int_ 1729) (int_ 1)) (record_ [("a", int_ 10)])) in
utest eval {env = []} recordUpdateNonValue with record_ [("a", int_ 1730)] in

let evalUTestRecordInUnit = TmUtest {
    test = record_add_bindings [("a", int_ 10), ("b", int_ 13)] record_empty,
    expected = record_add_bindings [("b", int_ 13), ("a", int_ 10)] record_empty,
    next = unit_}
in
utest eval {env = []} evalUTestRecordInUnit with unit_ in

utest eval {env = []} (addf_ (float_ 1.) (float_ 2.)) with float_ 3. in
utest eval {env = []} (subf_ (float_ 1.) (float_ 2.)) with float_ (negf 1.) in
utest eval {env = []} (mulf_ (float_ 1.) (float_ 2.)) with float_ 2. in
utest eval {env = []} (divf_ (float_ 1.) (float_ 2.)) with float_ 0.5 in
utest eval {env = []} (negf_ (float_ 1.)) with float_ (negf 1.) in

utest eval {env = []} (app_ id (int_ 1)) with int_ 1 in

utest eval {env = []} (app_ (ulam_ "x" (app_ (var_ "x") (int_ 1))) id)
with int_ 1 in

utest eval {env = []}
           (appSeq_ (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))))
                   [int_ 1, int_ 2])
with int_ 3 in

utest eval {env = []}
           (appSeq_ (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (int_ 1))))
                   [int_ 1, int_ 2])
with int_ 2 in

utest eval {env = []}
           (appSeq_ (ulam_ "x" (ulam_ "x" (addi_ (var_ "x") (int_ 1))))
                   [int_ 1, int_ 2])
with int_ 3 in

-- Builtin sequence functions
-- get [1,2,3] 1 -> 2
let getAst = TmApp {lhs = TmApp {lhs = TmConst {val = CGet ()},
                                  rhs = TmSeq {tms = [int_ 1, int_ 2, int_ 3]}},
                     rhs = int_ 1} in
utest eval {env = []} getAst with int_ 2 in

-- cons 1 [2, 3] -> [1,2,3]
let consAst = TmApp {lhs = TmApp {lhs = TmConst {val = CCons ()},
                                  rhs = int_ 1},
                     rhs = TmSeq {tms = [int_ 2, int_ 3]}} in
utest eval {env = []} consAst with TmSeq {tms = [int_ 1, int_ 2, int_ 3]} in

-- snoc [2, 3] 1 -> [2,3,1]
let snocAst = TmApp {lhs = TmApp {lhs = TmConst {val = CSnoc ()},
                                  rhs = TmSeq {tms = [int_ 2, int_ 3]}},
                     rhs = int_ 1} in
utest eval {env = []} snocAst with TmSeq {tms = [int_ 2, int_ 3, int_ 1]} in

-- concat [1,2,3] [4,5,6] -> [1,2,3,4,5,6]
let concatAst = TmApp {lhs = TmApp {lhs = TmConst {val = CConcat ()},
                                    rhs = TmSeq {tms = [int_ 1, int_ 2, int_ 3]}},
                       rhs = TmSeq {tms = [int_ 4, int_ 5, int_ 6]}} in
utest eval {env = []} concatAst with TmSeq {tms = [int_ 1, int_ 2, int_ 3, int_ 4, int_ 5, int_ 6]} in

-- length [1, 2, 3] = 3
let lengthAst = TmApp {lhs = TmConst {val = CLength ()},
                       rhs = TmSeq {tms = [int_ 1, int_ 2, int_ 3]}} in
utest eval {env = []} lengthAst with int_ 3 in

-- tail [1, 2, 3] = [2, 3]
let tailAst = TmApp {lhs = TmConst {val = CTail ()},
                     rhs = TmSeq {tms = [int_ 1, int_ 2, int_ 3]}} in
utest eval {env = []} tailAst with TmSeq {tms = [int_ 2, int_ 3]} in

-- head [1, 2, 3] = 1
let headAst = TmApp {lhs = TmConst {val = CHead ()},
                     rhs = TmSeq {tms = [int_ 1, int_ 2, int_ 3]}} in
utest eval {env = []} headAst with int_ 1 in

-- null [1, 2, 3] = false
let nullAst = TmApp {lhs = TmConst {val = CNull ()},
                     rhs = TmSeq {tms = [int_ 1, int_ 2, int_ 3]}} in
utest eval {env = []} nullAst with false_ in

-- null [] = true
let nullAst = TmApp {lhs = TmConst {val = CNull ()},
                     rhs = TmSeq {tms = []}} in
utest eval {env = []} nullAst with true_ in

-- reverse [1, 2, 3] = [3, 2, 1]
let reverseAst = TmApp {lhs = TmConst {val = CReverse ()},
                        rhs = TmSeq {tms = [int_ 1, int_ 2, int_ 3]}} in
utest eval {env = []} reverseAst with TmSeq {tms = [int_ 3, int_ 2, int_ 1]} in


-- Unit tests for CmpFloatEval
utest eval {env = []} (eqf_ (float_ 1.0) (float_ 1.0)) with true_ in
utest eval {env = []} (eqf_ (float_ 1.0) (float_ 0.0)) with false_ in
utest eval {env = []} (ltf_ (float_ 2.0) (float_ 1.0)) with false_ in
utest eval {env = []} (ltf_ (float_ 1.0) (float_ 1.0)) with false_ in
utest eval {env = []} (ltf_ (float_ 0.0) (float_ 1.0)) with true_ in

-- Unit tests for SymbEval and CmpSymbEval
utest eval {env = []} (eqs_ (symb_ (gensym ())) (symb_ (gensym ()))) with false_ in
utest eval {env = []} (bind_ (let_ "s" (None ()) (symb_ (gensym ()))) (eqs_ (var_ "s") (var_ "s"))) with true_ in

()
