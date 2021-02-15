-- Interpreters for the various fragments of MExpr.

-- TODO(?,?): Add types

include "string.mc"
include "char.mc"
include "assoc.mc"
include "name.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"

----------------------------
-- EVALUATION ENVIRONMENT --
----------------------------

type Symbol = Int

type Env = AssocMap Name Expr

let _eqn =
  lam n1. lam n2.
    if and (nameHasSym n1) (nameHasSym n2) then
      nameEqSym n1 n2
    else
      error "Found name without symbol in eval. Did you run symbolize?"

let _evalLookup = assocLookup {eq = _eqn}
let _evalInsert = assocInsert {eq = _eqn}

-------------
-- HELPERS --
-------------
-- Dynamic versions of recordproj_ and tupleproj_ in ast.mc. Usable on the fly
-- during evaluation (generates a fresh symbol for the internally matched
-- variable).

let drecordproj_ = use MExprAst in
  lam key. lam r.
  nrecordproj_ (nameSym "x") key r

let dtupleproj_ = use MExprAst in
  lam i. lam t.
  drecordproj_ (int2string i) t

-- Converts a sequence of characters to a string
let _seqOfCharToString = use MExprAst in
  lam tms.
    let f = lam c.
      match c with TmConst {val = CChar c} then
        c.val
      else error "Not a character"
    in
    map f tms

-----------
-- TERMS --
-----------

lang VarEval = VarAst + IdentifierPrettyPrint
  sem eval (ctx : {env : Env}) =
  | TmVar {ident = ident} ->
    match _evalLookup ident ctx.env with Some t then
      eval ctx t
    else
      error (concat "Unknown variable: " (pprintVarString ident))
end

lang AppEval = AppAst
  sem apply (ctx : {env : Env}) (arg : Expr) =
  | _ -> error "Bad application"

  sem eval (ctx : {env : Env}) =
  | TmApp t -> apply ctx (eval ctx t.rhs) (eval ctx t.lhs)
end

lang FunEval = LamAst + VarEval + AppEval
  syn Expr =
  | TmClos {ident : Name, body : Expr, env : Env}

  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmClos t -> eval {ctx with env = _evalInsert t.ident arg t.env} t.body

  sem eval (ctx : {env : Env}) =
  | TmLam t -> TmClos {ident = t.ident, body = t.body, env = ctx.env}
  | TmClos t -> TmClos t
end

lang LetEval = LetAst + VarEval
  sem eval (ctx : {env : Env}) =
  | TmLet t ->
    eval {ctx with env = _evalInsert t.ident (eval ctx t.body) ctx.env}
      t.inexpr
end

-- Fixpoint operator is only needed for eval. Hence, it is not in ast.mc
lang FixAst = LamAst
  syn Expr =
  | TmFix ()
end

lang FixEval = FixAst + FunEval
  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmFix _ ->
    match arg with TmClos clos then
      let ident = clos.ident in
      let body = clos.body in
      let env =
        _evalInsert ident (TmApp {lhs = TmFix (), rhs = TmClos clos}) clos.env in
      eval {ctx with env = env} body
    else
      error "Not fixing a function"

  sem eval (ctx : {env : Env}) =
  | TmFix _ -> TmFix ()
 end

lang RecordEval = RecordAst
  sem eval (ctx : {env : Env}) =
  | TmRecord t ->
    let bs = assocMap {eq=eqString} (eval ctx) t.bindings in
    TmRecord {t with bindings = bs}
  | TmRecordUpdate u ->
    match eval ctx u.rec with TmRecord t then
      if assocMem {eq = eqString} u.key t.bindings then
        TmRecord {t with bindings = assocInsert {eq = eqString}
                                u.key (eval ctx u.value) t.bindings}
      else error "Key does not exist in record"
    else error "Not updating a record"
end

lang RecLetsEval =
  RecLetsAst + VarEval + FixAst + FixEval + RecordEval + LetEval +
  UnknownTypeAst

  sem eval (ctx : {env : Env}) =
  | TmRecLets t ->
    let foldli = lam f. lam init. lam seq.
      (foldl (lam acc. lam x. (addi acc.0 1, f acc.0 acc.1 x)) (0, init) seq).1
    in
    utest foldli (lam i. lam acc. lam x. concat (concat acc (int2string i)) x)
                 ""
                 ["a", "b", "c"]
    with "0a1b2c" in
    let eta_name = nameSym "eta" in
    let eta_var = TmVar {ident = eta_name} in
    let unpack_from = lam var. lam body.
      foldli
        (lam i. lam bodyacc. lam binding.
          TmLet {ident = binding.ident,
                 tyBody = TyUnknown {},
                 body = TmLam {ident = eta_name,
                               ty = TyUnknown {},
                               body = TmApp {lhs = dtupleproj_ i var,
                                             rhs = eta_var}},
                 inexpr = bodyacc,
                 ty = TyUnknown {}}
        )
        body
        t.bindings in
    let lst_name = nameSym "lst" in
    let lst_var = TmVar {ident = lst_name} in
    let func_tuple = tuple_ (map (lam x. x.body) t.bindings) in
    let unfixed_tuple = TmLam {ident = lst_name,
                               ty = TyUnknown {},
                               body = unpack_from lst_var func_tuple} in
    eval {ctx with env =
            _evalInsert lst_name (TmApp {lhs = TmFix (), rhs = unfixed_tuple})
            ctx.env}
         (unpack_from lst_var t.inexpr)
end

lang ConstEval = ConstAst + SysAst + SeqAst + UnknownTypeAst
  sem delta (arg : Expr) =

  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmConst c -> delta arg c.val

  sem eval (ctx : {env : Env}) =
  | TmConst {val = CArgv {}} ->
    TmSeq {tms = map str_ argv, ty = TyUnknown {}}
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

lang UtestEval = Eq + UtestAst
  sem eq (e1 : Expr) =
  | _ -> error "Equality not defined for expression"

  sem eval (ctx : {env : Env}) =
  | TmUtest t ->
    let v1 = eval ctx t.test in
    let v2 = eval ctx t.expected in
    let _ = if eqExpr v1 v2 then print "Test passed\n" else print "Test failed\n" in
    eval ctx t.next
end

lang SeqEval = SeqAst
  sem eval (ctx : {env : Env}) =
  | TmSeq s ->
    let vs = map (eval ctx) s.tms in
    TmSeq {s with tms = vs}
end

lang NeverEval = NeverAst
  --TODO(?,?)
end

lang RefEval = RefAst
  sem eval (ctx : {env : Env}) =
  | TmRef r -> TmRef r
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
  | CDivi2 Int
  | CModi2 Int

  sem delta (arg : Expr) =
  | CAddi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CAddi2 n}
    else error "Not adding an integer"
  | CAddi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = addi n1 n2}}
    else error "Not adding an integer"
  | CSubi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSubi2 n}
    else error "Not substracting an integer"
  | CSubi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = subi n1 n2}}
    else error "Not substracting an integer"
  | CMuli _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CMuli2 n}
    else error "Not multiplying an integer"
  | CMuli2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = muli n1 n2}}
    else error "Not multiplying an integer"
  | CDivi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CDivi2 n}
    else error "Not dividing number"
  | CDivi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = divi n1 n2}}
    else error "Not dividing with number"
  | CModi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CModi2 n}
    else error "Not taking modulo of number"
  | CModi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = modi n1 n2}}
    else error "Not taking modulo with number"
  | CNegi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CInt {val = negi n}}
    else error "Not negating a number"
end

lang ShiftIntEval = ShiftIntAst + ConstEval
  syn Const =
  | CSlli2 Int
  | CSrli2 Int
  | CSrai2 Int

  sem delta (arg : Expr) =
  | CSlli _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSlli2 n}
    else error "Not shifting a constant integer"
  | CSlli2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = slli n1 n2}}
    else error "Not shifting by a constant integer"
  | CSrli _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSrli2 n}
    else error "Not shifting a constant integer"
  | CSrli2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = srli n1 n2}}
    else error "Not shifting by a constant integer"
  | CSrai _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSrai2 n}
    else error "Not shifting a constant integer"
  | CSrai2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = srai n1 n2}}
    else error "Not shifting by a constant integer"
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
        TmConst {c with val = CAddf2 f.val}
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
  | CAddf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = addf f1 f2.val}}
      else error "Not adding a numeric constant"
    else error "Not adding a constant"
  | CSubf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CSubf2 f.val}
      else error "Not subtracting a numeric constant"
    else error "Not subtracting a constant"
  | CSubf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = subf f1 f2.val}}
      else error "Not subtracting a numeric constant"
    else error "Not subtracting a constant"
  | CMulf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CMulf2 f.val}
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
  | CMulf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = mulf f1 f2.val}}
      else error "Not multiplying a numeric constant"
    else error "Not multiplying a constant"
  | CDivf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CDivf2 f.val}
      else error "Not dividing a numeric constant"
    else error "Not dividing a constant"
  | CDivf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = divf f1 f2.val}}
      else error "Not dividing a numeric constant"
    else error "Not dividing a constant"
  | CNegf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CFloat {val = negf f.val}}
      else error "Not negating a numeric constant"
    else error "Not negating a constant"
end

lang FloatIntConversionEval = FloatIntConversionAst
  sem delta (arg : Expr) =
  | CFloorfi _ ->
    match arg with TmConst (t & {val = CFloat {val = r}}) then
      TmConst {t with val = CInt {val = floorfi r}}
    else error "Not flooring a float"
  | CCeilfi _ ->
    match arg with TmConst (t & {val = CFloat {val = r}}) then
      TmConst {t with val = CInt {val = ceilfi r}}
    else error "Not ceiling a float"
  | CRoundfi _ ->
    match arg with TmConst (t & {val = CFloat {val = r}}) then
      TmConst {t with val = CInt {val = roundfi r}}
    else error "Not rounding a float"
  | CInt2float _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CFloat {val = int2float n}}
    else error "Not converting a integer"
end

lang CmpIntEval = CmpIntAst + ConstEval
  syn Const =
  | CEqi2 Int
  | CNeqi2 Int
  | CLti2 Int
  | CGti2 Int
  | CLeqi2 Int
  | CGeqi2 Int

  sem delta (arg : Expr) =
  | CEqi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CEqi2 n}
    else error "Not comparing an integer constant"
  | CEqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = eqi n1 n2}}
    else error "Not comparing an integer constant"
  | CNeqi _ ->
    match arg with TmConst (t & {val = CInt {val = n1}}) then
      TmConst {t with val = CNeqi2 n1}
    else error "Not comparing an integer constant"
  | CNeqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = neqi n1 n2}}
    else error "Not comparing an integer constant"
  | CLti _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CLti2 n}
    else error "Not comparing an integer constant"
  | CLti2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = lti n1 n2}}
    else error "Not comparing an integer constant"
  | CGti _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CGti2 n}
    else error "Not comparing an integer constant"
  | CGti2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = gti n1 n2}}
    else error "Not comparing an integer constant"
  | CLeqi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CLeqi2 n}
    else error "Not comparing an integer constant"
  | CLeqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = leqi n1 n2}}
    else error "Not comparing an integer constant"
  | CGeqi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CGeqi2 n}
    else error "Not comparing an integer constant"
  | CGeqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = geqi n1 n2}}
    else error "Not comparing an integer constant"
end

lang CmpCharEval = CmpCharAst + ConstEval
  syn Const =
  | CEqc2 Char

  sem delta (arg : Expr) =
  | CEqc _ ->
    match arg with TmConst (t & {val = CChar {val = c}}) then
      TmConst {t with val = CEqc2 c}
    else error "Not comparing a character constant"
  | CEqc2 c1 ->
    match arg with TmConst (t & {val = CChar {val = c2}}) then
      TmConst {t with val = CBool {val = eqc c1 c2}}
    else error "Not comparing a character constant"
end

lang IntCharConversionEval = IntCharConversionAst + ConstEval
  sem delta (arg : Expr) =
  | CInt2Char _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CChar {val = int2char n}}
    else error "Not int2char of an integer constant"
  | CChar2Int _ ->
    match arg with TmConst (t & {val = CChar {val = c}}) then
      TmConst {t with val = CInt {val = char2int c}}
    else error "Not char2int of a character constant"
end

lang CmpFloatEval = CmpFloatAst + ConstEval
  syn Const =
  | CEqf2 Float
  | CLtf2 Float
  | CLeqf2 Float
  | CGtf2 Float
  | CGeqf2 Float
  | CNeqf2 Float

  sem delta (arg : Expr) =
  | CEqf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CEqf2 f.val}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CEqf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CBool {val = eqf f1 f2.val}}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLtf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CLtf2 f.val}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLtf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CBool {val = ltf f1 f2.val}}
      else error "Not comparing a numeric constant"
    else error "Not comparing a constant"
  | CLeqf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CLeqf2 f1}
    else error "Not comparing a floating-point constant"
  | CLeqf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = leqf f1 f2}}
    else error "Not comparing a floating-point constant"
  | CGtf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CGtf2 f1}
    else error "Not comparing a floating-point constant"
  | CGtf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = gtf f1 f2}}
    else error "Not comparing a floating-point constant"
  | CGeqf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CGeqf2 f1}
    else error "Not comparing a floating-point constant"
  | CGeqf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = geqf f1 f2}}
    else error "Not comparing a floating-point constant"
  | CNeqf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CNeqf2 f1}
    else error "Not comparing a floating-point constant"
  | CNeqf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = neqf f1 f2}}
    else error "Not comparing a floating-point constant"
end

lang SymbEval = SymbAst + IntAst + RecordAst + ConstEval
  sem delta (arg : Expr) =
  | CGensym _ ->
    match arg with TmRecord {bindings = []} then
      TmConst {val = CSymb {val = gensym ()}, ty = TyUnknown {}}
    else error "Argument in gensym is not unit"
  | CSym2hash _ ->
    match arg with TmConst (t & {val = CSymb s}) then
      TmConst {t with val = CInt {val = sym2hash s.val}}
    else error "Argument in sym2hash is not a symbol"
end

lang CmpSymbEval = CmpSymbAst + ConstEval
  syn Const =
  | CEqsym2 Symb

  sem delta (arg : Expr) =
  | CEqsym _ ->
    match arg with TmConst (t & {val = CSymb s}) then
      TmConst {t with val = CEqsym2 s.val}
    else error "First argument in eqsym is not a symbol"
  | CEqsym2 s1 ->
    match arg with TmConst (t & {val = CSymb s2}) then
      TmConst {t with val = CBool {val = eqsym s1 s2.val}}
    else error "Second argument in eqsym is not a symbol"
end

lang SeqOpEval = SeqOpAst + IntAst + BoolAst + ConstEval
  syn Const =
  | CGet2 [Expr]
  | CSet2 [Expr]
  | CSet3 ([Expr], Int)
  | CCons2 Expr
  | CSnoc2 [Expr]
  | CConcat2 [Expr]
  | CSplitAt2 [Expr]
  | CMakeSeq2 Int

  sem delta (arg : Expr) =
  | CGet _ ->
    match arg with TmSeq s then
      TmConst {val = CGet2 s.tms, ty = TyUnknown {}}
    else error "Not a get of a constant sequence"
  | CGet2 tms ->
    match arg with TmConst {val = CInt {val = n}} then
      get tms n
    else error "n in get is not a number"
  | CSet _ ->
    match arg with TmSeq s then
      TmConst {val = CSet2 s.tms, ty = TyUnknown {}}
    else error "Not a set of a constant sequence"
  | CSet2 tms ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CSet3 (tms, n)}
    else error "n in set is not a number"
  | CSet3 (tms,n) ->
    TmSeq {tms = set tms n arg, ty = TyUnknown {}}
  | CCons _ ->
    TmConst {val = CCons2 arg, ty = TyUnknown {}}
  | CCons2 tm ->
    match arg with TmSeq s then
      TmSeq {s with tms = cons tm s.tms}
    else error "Not a cons of a constant sequence"
  | CSnoc _ ->
    match arg with TmSeq s then
      TmConst {val = CSnoc2 s.tms, ty = TyUnknown {}}
    else error "Not a snoc of a constant sequence"
  | CSnoc2 tms ->
    TmSeq {tms = snoc tms arg, ty = TyUnknown {}}
  | CConcat _ ->
    match arg with TmSeq s then
      TmConst {val = CConcat2 s.tms, ty = TyUnknown {}}
    else error "Not a concat of a constant sequence"
  | CConcat2 tms ->
    match arg with TmSeq s then
      TmSeq {tms = concat tms s.tms, ty = TyUnknown {}}
    else error "Not a concat of a constant sequence"
  | CLength _ ->
    match arg with TmSeq s then
      TmConst {val = CInt {val = length s.tms}, ty = TyUnknown {}}
    else error "Not length of a constant sequence"
  | CReverse _ ->
    match arg with TmSeq s then
      TmSeq {tms = reverse s.tms, ty = TyUnknown {}}
    else error "Not reverse of a constant sequence"
  | CSplitAt _ ->
    match arg with TmSeq s then
      TmConst {val = CSplitAt2 s.tms, ty = TyUnknown {}}
    else error "Not splitAt of a constant sequence"
  | CSplitAt2 tms ->
    match arg with TmConst {val = CInt {val = n}} then
      let t = splitAt tms n in
      tuple_ [seq_ t.0, seq_ t.1]
    else error "n in splitAt is not a number"
  | CMakeSeq _ ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CMakeSeq2 n, ty = TyUnknown {}}
    else error "n in makeSeq is not a number"
  | CMakeSeq2 n ->
    TmSeq {tms = makeSeq n arg, ty = TyUnknown {}}
end

lang FloatStringConversionEval = FloatStringConversionAst
  sem delta (arg : Expr) =
  | CString2float _ ->
    match arg with TmSeq {tms = tms} then
      let s = _seqOfCharToString tms in
      float_ (string2float s)
    else error "Not converting a sequence"
end

lang FileOpEval = FileOpAst + SeqAst + BoolAst + CharAst + UnknownTypeAst
  syn Const =
  | CFileWrite2 string

  sem delta (arg : Expr) =
  | CFileRead _ ->
    match arg with TmSeq s then
      let f = _seqOfCharToString s.tms in
      str_ (readFile f)
    else error "f in readFile not a sequence"
  | CFileWrite _ ->
    match arg with TmSeq s then
      let f = _seqOfCharToString s.tms in
      TmConst {val = CFileWrite2 f, ty = TyUnknown {}}
    else error "f in writeFile not a sequence"
  | CFileWrite2 f ->
    match arg with TmSeq s then
      let d = _seqOfCharToString s.tms in
      let _ = writeFile f d in
      unit_
    else error "d in writeFile not a sequence"
  | CFileExists _ ->
    match arg with TmSeq s then
      let f = _seqOfCharToString s.tms in
      TmConst {val = CBool {val = fileExists f}, ty = TyUnknown {}}
    else error "f in fileExists not a sequence"
  | CFileDelete _ ->
    match arg with TmSeq s then
      let f = _seqOfCharToString s.tms in
      let _ = deleteFile f in
      unit_
    else error "f in deleteFile not a sequence"
end

lang IOEval = IOAst + SeqAst + UnknownTypeAst
  sem delta (arg : Expr) =
  | CPrintString _ ->
    match arg with TmSeq s then
      let s = _seqOfCharToString s.tms in
      let _ = print s in
      unit_
    else error "string to print is not a string"
  | CReadLine _ ->
    let s = readLine () in
    TmSeq {tms = map char_ s, ty = TyUnknown {}}
end

lang RandomNumberGeneratorEval = RandomNumberGeneratorAst + IntAst
  syn Const =
  | CRandIntU2 Int

  sem delta (arg : Expr) =
  | CRandIntU _ ->
    match arg with TmConst c then
      match c.val with CInt lo then
        TmConst {c with val = CRandIntU2 lo.val}
      else error "lo in randIntU not a constant integer"
    else error "lo in randIntU not a constant"
  | CRandIntU2 lo ->
    match arg with TmConst c then
      match c.val with CInt hi then
        TmConst {c with val = CInt {val = randIntU lo hi.val}}
      else error "hi in randIntU not a constant integer"
    else error "hi in randIntU not a constant"
  | CRandSetSeed _ ->
    match arg with TmConst c then
      match c.val with CInt {val = s} then
        TmConst {c with val = CInt {val = randSetSeed s}}
      else error "s in randSetSeed not a constant integer"
    else error "s in randSetSeed not a constant"
end

lang SysEval = SysAst + SeqAst + IntAst + CharAst
  sem delta (arg : Expr) =
  | CError _ ->
    match arg with TmSeq s then
      error (_seqOfCharToString s.tms)
    else
      error "s in error not a sequence"
  | CExit _ ->
    match arg with TmConst {val = CInt {val = n}} then
      exit n
    else
      error "n in exit not an integer"
end

lang TimeEval = TimeAst + IntAst
  sem delta (arg : Expr) =
  | CSleepMs _ ->
    match arg with TmConst {val = CInt {val = n}} then
      let _ = sleepMs n in
      unit_
    else error "n in wallTimeMs not a constant integer"
  | CWallTimeMs _ ->
    float_ (wallTimeMs ())
end

lang RefOpEval = RefOpAst + IntAst
  syn Const =
  | CModRef2 Ref

  sem delta (arg : Expr) =
  | CRef _ -> TmRef {ref = ref arg}
  | CModRef _ ->
    match arg with TmRef {ref = r} then
      TmConst {val = CModRef2 r}
    else error "first argument of modref not a reference"
  | CModRef2 r ->
    let _ = modref r arg in
    unit_
  | CDeRef _ ->
    match arg with TmRef {ref = r} then
      deref r
    else error "not a deref of a reference"
end


--------------
-- PATTERNS --
--------------

lang NamedPatEval = NamedPat
  sem tryMatch (env : Env) (t : Expr) =
  | PNamed {ident = PName name} -> Some (_evalInsert name t env)
  | PNamed {ident = PWildcard ()} -> Some env
end

lang SeqTotPatEval = SeqTotPat + SeqAst
  sem tryMatch (env : Env) (t : Expr) =
  | PSeqTot {pats = pats} ->
    match t with TmSeq {tms = tms} then
      if eqi (length tms) (length pats) then
        optionFoldlM (lam env. lam pair. tryMatch env pair.0 pair.1) env
          (zipWith (lam a. lam b. (a, b)) tms pats)
      else None ()
    else None ()
end

lang SeqEdgePatEval = SeqEdgePat + SeqAst
  sem tryMatch (env : Env) (t : Expr) =
  | PSeqEdge {prefix = pre, middle = middle, postfix = post} ->
    match t with TmSeq {tms = tms} then
      if geqi (length tms) (addi (length pre) (length post)) then
        match splitAt tms (length pre) with (preTm, tms) then
        match splitAt tms (subi (length tms) (length post)) with (tms, postTm) then
        let pair = lam a. lam b. (a, b) in
        let paired = zipWith pair (concat preTm postTm) (concat pre post) in
        let env = optionFoldlM (lam env. lam pair. tryMatch env pair.0 pair.1) env paired in
        match middle with PName name then
          optionMap (_evalInsert name (seq_ tms)) env
        else match middle with PWildcard () then
          env
        else never else never else never
      else None ()
    else None ()
end

lang RecordPatEval = RecordAst + RecordPat
  sem tryMatch (env : Env) (t : Expr) =
  | PRecord r ->
    match t with TmRecord {bindings = bs} then
      assocFoldlM {eq = eqString}
        (lam env. lam k. lam p.
          match assocLookup {eq = eqString} k bs with Some v then
            tryMatch env v p
          else None ())
        env
        r.bindings
    else None ()
end

lang DataPatEval = DataAst + DataPat
  sem tryMatch (env : Env) (t : Expr) =
  | PCon {ident = ident, subpat = subpat} ->
    match t with TmConApp cn then
      let constructor = cn.ident in
      let subexpr = cn.body in
      if _eqn ident constructor
        then tryMatch env subexpr subpat
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

lang CharPatEval = CharAst + CharPat
  sem tryMatch (env : Env) (t : Expr) =
  | PChar ch ->
    match t with TmConst c then
      match c.val with CChar ch2 then
        if eqChar ch.val ch2.val then Some env else None ()
      else None ()
    else None ()
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
  sem tryMatch (env : Env) (t : Expr) =
  | PAnd {lpat = l, rpat = r} ->
    optionBind (tryMatch env t l) (lam env. tryMatch env t r)
end

lang OrPatEval = OrPat
  sem tryMatch (env : Env) (t : Expr) =
  | POr {lpat = l, rpat = r} ->
    optionOrElse (lam _. tryMatch env t r) (tryMatch env t l)
end

lang NotPatEval = NotPat
  sem tryMatch (env : Env) (t : Expr) =
  | PNot {subpat = p} ->
    let res = tryMatch env t p in
    match res with None _ then Some env else
    match res with Some _ then None () else never
end

-------------------------
-- MEXPR EVAL FRAGMENT --
-------------------------

lang MExprEval =

  -- Symbolize is required before eval, and MExprEq is used below when testing.
  MExprSym + MExprEq

  -- Terms
  + VarEval + AppEval + FunEval + FixEval + RecordEval + RecLetsEval +
  ConstEval + DataEval + MatchEval + UtestEval + SeqEval + NeverEval + RefEval

  -- Constants
  + ArithIntEval + ShiftIntEval + ArithFloatEval + CmpIntEval + CmpFloatEval +
  SymbEval + CmpSymbEval + SeqOpEval + FileOpEval + IOEval + SysEval +
  RandomNumberGeneratorEval + FloatIntConversionEval + CmpCharEval +
  IntCharConversionEval + FloatStringConversionEval + TimeEval + RefOpEval

  -- Patterns
  + NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval

  -- Pretty Printing of Identifiers
  + MExprIdentifierPrettyPrint
end


-----------
-- TESTS --
-----------

mexpr

use MExprEval in

-- Evaluation shorthand used in tests below
let eval =
  lam t. eval {env = assocEmpty} (symbolize t) in

let id = ulam_ "x" (var_ "x") in
let bump = ulam_ "x" (addi_ (var_ "x") (int_ 1)) in
let fst = ulam_ "t" (tupleproj_ 0 (var_ "t")) in
let appIdUnit = app_ id unit_ in
let appBump3 = app_ bump (int_ 3) in
let appFst = app_ fst (tuple_ [not_ false_, addi_ (int_ 1) (int_ 2)]) in
utest eval appIdUnit with unit_ in
utest eval appBump3 with (int_ 4) in
utest eval appFst with true_ in

let dataDecl =
  bind_ (ucondef_ "Foo")
    (match_ (conapp_ "Foo" (tuple_ [unit_, unit_]))
      (pcon_ "Foo" (pvar_ "u"))
      (tupleproj_ 0 (var_ "u"))
      id) in

utest eval dataDecl with unit_ in

-- Commented out to not clutter the test suite
-- let utest_test1 = utest_ (int_ 1) (int_ 2) unit_ in
-- let utest_test2 =
--   utest_ (tuple_ [int_ 1, addi_ (int_ 1) (int_ 2)]) (int_ 1, int_ 3) unit_ in
-- let utest_test3 =
--   bind_ (ucondef_ "Foo")
--     (utest_ (conapp_ "Foo" unit_) (conapp_ "Foo" unit_) unit_) in
-- utest eval utest_test1 with unit_ in
-- utest eval utest_test2 with unit_ in
-- utest eval utest_test3 with unit_ in

-- Implementing an interpreter
let num = lam n.  conapp_ "Num" (int_ n) in
let one = num 1 in -- Num 1
let two = num 2 in -- Num 2
let three = num 3 in -- Num 3
let add = lam n1. lam n2.  conapp_ "Add" (tuple_ [n1, n2]) in
let addOneTwo = add one two in -- Add (Num 1, Num 2)
let num_case = lam arg. lam els. -- match arg with Num n then Num n else els
  match_ arg (pcon_ "Num" (pvar_ "n")) (conapp_ "Num" (var_ "n")) els in

-- match arg with Add t then
--   let e1 = t.0 in
--   let e2 = t.1 in
--   match eval e1 with Num n1 then
--     match eval e2 with Num n2 then
--       Num (addi n1 n2)
--     else repl()
--   else ()
-- else els

let result = conapp_ "Num" (addi_ (var_ "n1") (var_ "n2")) in

let matchInner =
  match_ (app_ (var_ "eval") (var_ "e2")) (pcon_ "Num" (pvar_ "n2"))
    result unit_ in

let matchOuter =
  match_ (app_ (var_ "eval") (var_ "e1")) (pcon_ "Num" (pvar_ "n1"))
    matchInner unit_ in

let deconstruct = lam t.
  bindall_
    [(ulet_ "e1" (tupleproj_ 0 t)), (ulet_ "e2" (tupleproj_ 1 t)), matchOuter] in

let addCase = lam arg. lam els.
  match_ arg (pcon_ "Add" (pvar_ "t")) (deconstruct (var_ "t")) els in

 -- fix (lam eval. lam e. match e with then ... else ())
let evalFn =
  ureclet_ "eval" (ulam_ "e" (num_case (var_ "e") (addCase (var_ "e") unit_))) in

-- con Num in con Add in let eval = ... in t
let wrapInDecls = lam t.
  bindall_ [ucondef_ "Num", ucondef_ "Add", evalFn, t] in

let evalAdd1 = wrapInDecls (app_ (var_ "eval") addOneTwo) in
let addOneTwoThree = add (add one two) three in
let evalAdd2 = wrapInDecls (app_ (var_ "eval") addOneTwoThree) in

let srl = bind_
  (ureclet_ "test" (ulam_ "x"
     (if_ (eqi_ (var_ "x") (int_ 0))
       true_
       (app_ (var_ "test") (subi_ (var_ "x") (int_ 1))))))
  (app_ (var_ "test") (int_ 3)) in

utest eval srl with true_ in

utest eval evalAdd1 with conapp_ "Num" (int_ 3) using eqExpr in
utest eval evalAdd2 with conapp_ "Num" (int_ 6) using eqExpr in

-- Commented out to declutter test suite output
-- let evalUTestIntInUnit = utest_ (int_ 3) (int_ 3) unit_ in
-- utest eval evalUTestIntInUnit with unit_ in

let oddEven = lam bdy.
  bind_
    (ureclets_
       [("odd",
         ulam_ "x"
           (if_ (eqi_ (var_ "x") (int_ 1))
              true_
              (if_ (lti_ (var_ "x") (int_ 1))
                 false_
                 (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))),

        ("even",
         ulam_ "x"
           (if_ (eqi_ (var_ "x") (int_ 0))
              true_
              (if_ (lti_ (var_ "x") (int_ 0))
                 false_
                 (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1))))))])
    bdy
in

utest eval (oddEven (app_ (var_ "odd") (int_ 4))) with false_ in
utest eval (oddEven (app_ (var_ "odd") (int_ 3))) with true_ in
utest eval (oddEven (app_ (var_ "even") (int_ 4))) with true_ in
utest eval (oddEven (app_ (var_ "even") (int_ 3))) with false_ in

let num = lam x. conapp_ "Num" x in
-- lam arg. match arg with Add (Num n1, Num n2) then
--   Num (addi n1 n2)
-- else ()
let addEvalNested = ulam_ "arg"
  (match_ (var_ "arg") (ptuple_ [(pcon_ "Num" (pvar_ "n1")), (pcon_ "Num" (pvar_ "n2"))])
    (num (addi_ (var_ "n1") (var_ "n2")))
    (unit_)) in


utest eval (wrapInDecls (app_ addEvalNested (tuple_ [num (int_ 1), num (int_ 2)])))
with conapp_ "Num" (int_ 3)
using eqExpr in

let recordProj =
  bind_ (ulet_ "myrec" (record_ [("a", int_ 10),("b", int_ 37),("c", int_ 23)]))
    (recordproj_ "b" (var_ "myrec")) in

let recordUpdate =
  bind_ (ulet_ "myrec" (record_ [("a", int_ 10),("b", int_ 37),("c", int_ 23)]))
    (recordproj_ "c" (recordupdate_ (var_ "myrec") "c" (int_ 11))) in

let recordUpdate2 =
  bind_ (ulet_ "myrec" (record_ [("a", int_ 10),("b", int_ 37),("c", int_ 23)]))
    (recordproj_ "a" (recordupdate_ (var_ "myrec") "a" (int_ 1729))) in

utest eval recordProj with (int_ 37) in
utest eval recordUpdate with (int_ 11) in
utest eval recordUpdate2 with (int_ 1729) in


let recordUpdateNonValue =
  (recordupdate_ (record_ [("a", int_ 10)]) "a" (addi_ (int_ 1729) (int_ 1))) in
utest eval recordUpdateNonValue with record_ [("a", int_ 1730)] in


-- Commented out to not clutter the test suite
-- let evalUTestRecordInUnit =
--   utest_
--     (record_add_bindings [("a", int_ 10), ("b", int_ 13)] record_empty)
--     (record_add_bindings [("b", int_ 13), ("a", int_ 10)] record_empty)
--     unit_
-- in
-- utest eval evalUTestRecordInUnit with unit_ in

utest eval (addf_ (float_ 1.) (float_ 2.)) with float_ 3. in
utest eval (subf_ (float_ 1.) (float_ 2.)) with float_ (negf 1.) in
utest eval (mulf_ (float_ 1.) (float_ 2.)) with float_ 2. in
utest eval (divf_ (float_ 1.) (float_ 2.)) with float_ 0.5 in
utest eval (negf_ (float_ 1.)) with float_ (negf 1.) in

utest eval (app_ id (int_ 1)) with int_ 1 in

utest eval (app_ (ulam_ "x" (app_ (var_ "x") (int_ 1))) id)
with int_ 1 in

utest eval (appSeq_ (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))))
                   [int_ 1, int_ 2])
with int_ 3 in

utest eval (appSeq_ (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (int_ 1))))
                   [int_ 1, int_ 2])
with int_ 2 in

utest eval (appSeq_ (ulam_ "x" (ulam_ "x" (addi_ (var_ "x") (int_ 1))))
                   [int_ 1, int_ 2])
with int_ 3 in

-- Builtin sequence functions
-- get [1,2,3] 1 -> 2
let getAst = get_ (seq_ [int_ 1, int_ 2, int_ 3]) (int_ 1) in
utest eval getAst with int_ 2 in

-- set [1,2] 0 3 -> [3,2]
let setAst = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
utest eval setAst with seq_ [int_ 3, int_ 2] in

-- cons 1 [2, 3] -> [1,2,3]
let consAst = cons_ (int_ 1) (seq_ [int_ 2, int_ 3]) in
utest eval consAst with seq_ [int_ 1, int_ 2, int_ 3] in

-- snoc [2, 3] 1 -> [2,3,1]
let snocAst = snoc_ (seq_ [int_ 2, int_ 3]) (int_ 1) in
utest eval snocAst with seq_ [int_ 2, int_ 3, int_ 1] in

-- concat [1,2,3] [4,5,6] -> [1,2,3,4,5,6]
let concatAst = concat_
                  (seq_ [int_ 1, int_ 2, int_ 3])
                  (seq_ [int_ 4, int_ 5, int_ 6]) in
utest eval concatAst
with seq_ [int_ 1, int_ 2, int_ 3, int_ 4, int_ 5, int_ 6] in

-- length [1, 2, 3] -> 3
let lengthAst = length_ (seq_ [int_ 1, int_ 2, int_ 3]) in
utest eval lengthAst with int_ 3 in

-- reverse [1, 2, 3] -> [3, 2, 1]
let reverseAst = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
utest eval reverseAst with seq_ [int_ 3, int_ 2, int_ 1] in

-- splitAt [1,4,2,3] 2 -> ([1,4],[2,3])
let splitAtAst = splitat_ (seq_ [int_ 1, int_ 4, int_ 2, int_ 3]) (int_ 2) in
utest eval splitAtAst
with tuple_ [seq_ [int_ 1, int_ 4], seq_ [int_ 2, int_ 3]] in

-- makeSeq 3 42 -> [42, 42, 42]
let makeSeqAst = makeseq_ (int_ 3) (int_ 42) in
utest eval makeSeqAst with seq_ [int_ 42, int_ 42, int_ 42] in

-- Unit tests for CmpFloatEval
utest eval (eqf_ (float_ 2.0) (float_ 1.0)) with false_ in
utest eval (eqf_ (float_ 1.0) (float_ 1.0)) with true_ in
utest eval (eqf_ (float_ 0.0) (float_ 1.0)) with false_ in
utest eval (ltf_ (float_ 2.0) (float_ 1.0)) with false_ in
utest eval (ltf_ (float_ 1.0) (float_ 1.0)) with false_ in
utest eval (ltf_ (float_ 0.0) (float_ 1.0)) with true_ in
utest eval (leqf_ (float_ 2.0) (float_ 1.0)) with false_ in
utest eval (leqf_ (float_ 1.0) (float_ 1.0)) with true_ in
utest eval (leqf_ (float_ 0.0) (float_ 1.0)) with true_ in
utest eval (gtf_ (float_ 2.0) (float_ 1.0)) with true_ in
utest eval (gtf_ (float_ 1.0) (float_ 1.0)) with false_ in
utest eval (gtf_ (float_ 0.0) (float_ 1.0)) with false_ in
utest eval (geqf_ (float_ 2.0) (float_ 1.0)) with true_ in
utest eval (geqf_ (float_ 1.0) (float_ 1.0)) with true_ in
utest eval (geqf_ (float_ 0.0) (float_ 1.0)) with false_ in
utest eval (neqf_ (float_ 2.0) (float_ 1.0)) with true_ in
utest eval (neqf_ (float_ 1.0) (float_ 1.0)) with false_ in
utest eval (neqf_ (float_ 0.0) (float_ 1.0)) with true_ in

-- Unit tests for symbols

-- gensym
let s1 = eval (gensym_ unit_) in
let s2 = eval (gensym_ unit_) in
utest s1 with s1 in
utest s2 with s2 in

-- eqsym
utest eval (eqsym_ s1 s1) with true_ in
utest eval (eqsym_ s1 s2) with false_ in
utest eval (eqsym_ s2 s1) with false_ in
utest eval (bind_ (ulet_ "s" s1) (eqsym_ (var_ "s") (var_ "s")))
with true_ in

-- sym2hash
utest eval (eqi_ (sym2hash_ s1) (sym2hash_ s1)) with true_ in
utest eval (eqi_ (sym2hash_ s2) (sym2hash_ s1)) with false_ in
utest eval (eqi_ (sym2hash_ s1) (sym2hash_ s2)) with false_ in

-- Unit tests for file operations
let f = str_ "test_file_ops" in
let d = str_ "$&!@" in
utest eval (fileExists_ f) with false_ in
utest eval (writeFile_ f d) with unit_ in
utest eval (fileExists_ f) with true_ in
utest eval (readFile_ f) with d in
utest eval (deleteFile_ f) with unit_ in
utest eval (fileExists_ f) with false_ in

-- Test error
-- let _ = eval (error_ (str_ "test error message")) in

-- Test exit
-- let _ = eval (exit_ (int_ 1)) in

-- Test argv
-- utest eval argv_ with seq_ [str_ "mi"] in

utest eval (match_
  (tuple_ [true_, true_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with true_ in

utest eval (match_
  (tuple_ [true_, false_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with false_ in

utest eval (match_
  (tuple_ [false_, true_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with false_ in

utest eval (match_
  (tuple_ [false_, false_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with false_ in

utest eval (match_
  (int_ 1)
  (por_ (pand_ (pint_ 1) (pvar_ "x")) (pand_ (pint_ 2) (pvar_ "x")))
  (var_ "x")
  (int_ 42))
with int_ 1 in

utest eval (match_
  (int_ 2)
  (por_ (pand_ (pint_ 1) (pvar_ "x")) (pand_ (pint_ 2) (pvar_ "x")))
  (var_ "x")
  (int_ 42))
with int_ 2 in

utest eval (match_
  (int_ 3)
  (por_ (pand_ (pint_ 1) (pvar_ "x")) (pand_ (pint_ 2) (pvar_ "x")))
  (var_ "x")
  (int_ 42))
with int_ 42 in

utest eval (match_
  true_
  (pnot_ ptrue_)
  true_
  false_)
with false_ in

utest eval (match_
  false_
  (pnot_ ptrue_)
  true_
  false_)
with true_ in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3, int_ 4, int_ 5])
  (pseqedge_ [pvar_ "a"] "b" [pvar_ "c", pvar_ "d"])
  (tuple_ [var_ "a", var_ "b", var_ "c", var_ "d"])
  false_)
with tuple_ [int_ 1, seq_ [int_ 2, int_ 3], int_ 4, int_ 5] in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3])
  (pseqedge_ [pvar_ "a"] "b" [pvar_ "c", pvar_ "d"])
  (tuple_ [var_ "a", var_ "b", var_ "c", var_ "d"])
  false_)
with tuple_ [int_ 1, seq_ [], int_ 2, int_ 3] in

utest eval (match_
  (seq_ [int_ 1, int_ 2])
  (pseqedge_ [pvar_ "a"] "b" [pvar_ "c", pvar_ "d"])
  (tuple_ [var_ "a", var_ "b", var_ "c", var_ "d"])
  false_)
with false_ in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3])
  (pseqtot_ [pvar_ "a", pvar_ "b", pvar_ "c"])
  (tuple_ [var_ "a", var_ "b", var_ "c"])
  false_)
with tuple_ [int_ 1, int_ 2, int_ 3] in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
  (pseqtot_ [pvar_ "a", pvar_ "b", pvar_ "c"])
  (tuple_ [var_ "a", var_ "b", var_ "c"])
  false_)
with false_ in

utest eval (match_
  (seq_ [int_ 1, int_ 2])
  (pseqtot_ [pvar_ "a", pvar_ "b", pvar_ "c"])
  (tuple_ [var_ "a", var_ "b", var_ "c"])
  false_)
with false_ in

utest eval (match_
  (tuple_ [int_ 1, int_ 2])
  (pand_ (pvar_ "a") (ptuple_ [pvar_ "b", pint_ 2]))
  (tuple_ [var_ "a", var_ "b"])
  (tuple_ [tuple_ [int_ 70, int_ 72], int_ 71]))
with tuple_ [tuple_ [int_ 1, int_ 2], int_ 1] in

-- I/O operations
-- utest eval (printString_ (str_ "Hello World")) with unit_ in
-- utest eval (printString_ (readLine_ unit_)) with unit_ in

-- Random number generation
utest eval (bind_ (ulet_ "_" (randSetSeed_ (int_ 42)))
                  (randIntU_ (int_ 1) (int_ 10)))
                  with [1, 2, 3, 4, 5, 6, 7, 8, 9] using
  lam r. lam seq.
    match r with TmConst {val = CInt {val = n}} then
      any (eqi n) seq
    else false
in

utest eval (randIntU_ (int_ 0) (int_ 3)) with [0, 1, 2] using
  lam r. lam seq.
    match r with TmConst {val = CInt {val = n}} then
      any (eqi n) seq
    else false
in

-- Time operations
let t = eval (wallTimeMs_ unit_) in
utest eval (or_ (leqf_ t (float_ 0.0)) (geqf_ t (float_ 0.0))) with true_ in
-- utest eval (sleepMs_ (int_ 1000)) with unit_ in

-- Integer arithmetics
utest eval (addi_ (int_ 4) (int_ 2)) with int_ 6 in
utest eval (subi_ (int_ 4) (int_ 2)) with int_ 2 in
utest eval (muli_ (int_ 4) (int_ 2)) with int_ 8 in
utest eval (divi_ (int_ 4) (int_ 2)) with int_ 2 in
utest eval (divi_ (int_ 4) (int_ 3)) with int_ 1 in
utest eval (modi_ (int_ 4) (int_ 2)) with int_ 0 in
utest eval (modi_ (int_ 4) (int_ 3)) with int_ 1 in
utest eval (addi_ (int_ 4) (negi_ (int_ 2))) with int_ 2 in

-- Float arithmetics
utest eval (addf_ (float_ 4.) (float_ 2.)) with float_ 6. in
utest eval (subf_ (float_ 4.) (float_ 2.)) with float_ 2. in
utest eval (mulf_ (float_ 4.) (float_ 2.)) with float_ 8. in
utest eval (divf_ (float_ 4.) (float_ 2.)) with float_ 2. in
utest eval (addf_ (float_ 4.) (negf_ (float_ 2.))) with float_ 2. in

-- Integer shifting
utest eval (slli_ (int_ 1) (int_ 2)) with int_ 4 in
utest eval (slli_ (int_ 2) (int_ 5)) with int_ 64 in
utest eval (slli_ (negi_ (int_ 1)) (int_ 1)) with eval (negi_ (int_ 2)) in
utest eval (srli_ (int_ 4) (int_ 2)) with int_ 1 in
utest eval (srli_ (int_ 64) (int_ 5)) with int_ 2 in
utest eval (srli_ (negi_ (int_ 2)) (int_ 1)) with int_ 4611686018427387903 in -- NOTE(larshum, 2020-12-07): Assumes 63-bit integers (used in 64-bit OCaml).
utest eval (srai_ (int_ 4) (int_ 2)) with int_ 1 in
utest eval (srai_ (int_ 64) (int_ 5)) with int_ 2 in
utest eval (srai_ (negi_ (int_ 2)) (int_ 1)) with eval (negi_ (int_ 1)) in

-- Integer comparison
utest eval (eqi_ (int_ 2) (int_ 2)) with true_ in
utest eval (eqi_ (negi_ (int_ 2)) (int_ 2)) with false_ in
utest eval (neqi_ (negi_ (int_ 2)) (int_ 2)) with true_ in
utest eval (neqi_ (int_ 5) (int_ 5)) with false_ in
utest eval (lti_ (int_ 1) (int_ 3)) with true_ in
utest eval (lti_ (int_ 1) (int_ 1)) with false_ in
utest eval (gti_ (int_ 3) (int_ 0)) with true_ in
utest eval (gti_ (int_ 1) (int_ 1)) with false_ in
utest eval (leqi_ (int_ 4) (int_ 9)) with true_ in
utest eval (leqi_ (int_ 1) (int_ 1)) with true_ in
utest eval (leqi_ (int_ 2) (int_ 1)) with false_ in
utest eval (geqi_ (int_ 23) (int_ 22)) with true_ in
utest eval (geqi_ (int_ 1) (int_ 1)) with true_ in
utest eval (geqi_ (int_ 0) (int_ 1)) with false_ in

-- Integer-Float conversion
utest eval (floorfi_ (float_ 1.5)) with int_ 1 in
utest eval (ceilfi_ (float_ 1.5)) with int_ 2 in
utest eval (roundfi_ (float_ 1.5)) with int_ 2 in
utest eval (roundfi_ (float_ 1.49)) with int_ 1 in
utest eval (int2float_ (int_ 1)) with float_ 1. in

-- Char comparison
utest eval (eqc_ (char_ 'a') (char_ 'a')) with true_ in
utest eval (eqc_ (char_ '\n') (char_ '\n')) with true_ in
utest eval (eqc_ (char_ 'X') (char_ 'x')) with false_ in

-- Integer-Char conversion
utest eval (int2char_ (int_ 65)) with char_ 'A' in
utest eval (char2int_ (char_ '\t')) with int_ 9 in

-- String-Float conversion
utest eval (string2float_ (str_ "1.5")) with float_ 1.5 in

-- References
let p = bindall_ [ulet_ "r1" (ref_ (int_ 1)),
                  ulet_ "r2" (ref_ (float_ 2.)),
                  ulet_ "r3" (var_ "r1"),
                  ulet_ "r4"
                    (ref_ (ulam_ "x" (concat_ (str_ "Hello ") (var_ "x"))))]
in
utest eval (bind_ p (modref_ (var_ "r1") (int_ 2))) with unit_ in
utest
  eval (bind_ p
    (tuple_ [deref_ (var_ "r1"),
             deref_ (var_ "r2"),
             deref_ (var_ "r3"),
             app_ (deref_ (var_ "r4")) (str_ "test")]))
with tuple_ [int_ 1, float_ 2., int_ 1, str_ "Hello test"] in

utest
  eval (bind_ p (bindall_
    [ulet_ "_" (modref_ (var_ "r1") (int_ 3)),
     ulet_ "_" (modref_ (var_ "r2") (float_ 3.14)),
     ulet_ "_" (modref_ (var_ "r3") (int_ 4)),
     tuple_ [deref_ (var_ "r1"), deref_ (var_ "r2"), deref_ (var_ "r3")]]))
with tuple_ [int_ 4, float_ 3.14, int_ 4] in

()
