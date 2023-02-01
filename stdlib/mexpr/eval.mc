-- Interpreters for the various fragments of MExpr.

include "string.mc"
include "char.mc"
include "name.mc"
include "list.mc"

include "info.mc"
include "error.mc"
include "ast.mc"
include "ast-builder.mc"
include "symbolize.mc"
include "eq.mc"
include "pprint.mc"

----------------------------
-- EVALUATION ENVIRONMENT --
----------------------------

type Env = List (Name, Expr)

let evalEnvEmpty = listEmpty

let evalEnvLookup = lam id. lam env.
  let p = lam entry. nameEqSymUnsafe id entry.0 in
  match listFind p env with Some (_, e) then Some e else None ()

let evalEnvInsert = lam id. lam e. lam env. listCons (id, e) env

------------------------
-- EVALUATION CONTEXT --
------------------------

type EvalCtx = { env : Env }

let evalCtxEmpty = { env = evalEnvEmpty }

-------------
-- HELPERS --
-------------

-- Converts a sequence of characters to a string
let _evalSeqOfCharsToString = use MExprAst in
  lam info. lam tms.
    let f = lam c.
      match c with TmConst {val = CChar c} then
        c.val
      else errorSingle [info] "Not a character"
    in
    map f tms

let _evalStringToSeqOfChars = map char_

-----------
-- TERMS --
-----------

lang Eval
  sem eval : EvalCtx -> Expr -> Expr
end

lang VarEval = Eval + VarAst + AppAst
  sem eval ctx =
  | TmVar r ->
    match evalEnvLookup r.ident ctx.env with Some t then t
    else
      errorSingle [r.info] (concat "Unknown variable: " (pprintVarString (nameGetStr r.ident)))
end

lang AppEval = Eval + AppAst
  sem apply : EvalCtx -> Info -> Expr -> Expr -> Expr
  sem apply ctx info arg =
  | _ -> errorSingle [info] "Bad application"

  sem eval ctx =
  | TmApp r -> apply ctx r.info (eval ctx r.rhs) (eval ctx r.lhs)
end

lang LamEval = Eval + LamAst + VarEval + AppEval
  type Lazy a = () -> a

  syn Expr =
  | TmClos {ident : Name, body : Expr, env : Lazy Env}

  sem apply ctx info arg =
  | TmClos t -> eval {ctx with env = evalEnvInsert t.ident arg (t.env ())} t.body

  sem eval ctx =
  | TmLam t -> TmClos {ident = t.ident, body = t.body, env = lam. ctx.env}
  | TmClos t -> TmClos t
end

lang LetEval = Eval + LetAst + VarEval
  sem eval ctx =
  | TmLet t ->
    eval {ctx with env = evalEnvInsert t.ident (eval ctx t.body) ctx.env}
      t.inexpr
end

lang RecordEval = Eval + RecordAst
  sem eval ctx =
  | TmRecord t ->
    let bs = mapMap (eval ctx) t.bindings in
    TmRecord {t with bindings = bs}
  | TmRecordUpdate u ->
    match eval ctx u.rec with TmRecord t then
      if mapMem u.key t.bindings then
        TmRecord
          {t with bindings = mapInsert u.key (eval ctx u.value) t.bindings}
      else errorSingle [u.info] "Key does not exist in record"
    else errorSingle [u.info] "Not updating a record"
end

lang RecLetsEval =
  Eval + RecLetsAst + VarEval + RecordEval + LetEval + LamEval +
  UnknownTypeAst

  sem eval ctx =
  | TmRecLets t ->
    recursive let envPrime : Lazy Env = lam.
      let wraplambda = lam v.
        match v with TmLam t then
          TmClos {ident = t.ident, body = t.body, env = envPrime}
        else errorSingle [infoTm v] "Right-hand side of recursive let must be a lambda"
      in
      foldl
        (lam env. lam bind.
          evalEnvInsert bind.ident (wraplambda bind.body) env)
        ctx.env t.bindings
    in
    eval {ctx with env = envPrime ()} t.inexpr
end

lang ConstEval = Eval + ConstAst + SysAst + SeqAst + UnknownTypeAst
  sem delta : Info -> Expr -> Const -> Expr

  sem apply ctx info arg =
  | TmConst c -> delta info arg c.val

  sem eval ctx =
  | TmConst {val = CArgv {}} ->
    TmSeq {tms = map str_ argv, ty = tyunknown_, info = NoInfo()}
  | TmConst c -> TmConst c
end

lang TypeEval = Eval + TypeAst
  sem eval ctx =
  | TmType t -> eval ctx t.inexpr
end

lang DataEval = Eval + DataAst + AppEval
  sem eval ctx =
  | TmConDef t -> eval ctx t.inexpr
  | TmConApp t -> TmConApp {t with body = eval ctx t.body}
end

lang MatchEval = Eval + MatchAst
  sem eval ctx =
  | TmMatch t ->
    match tryMatch ctx.env (eval ctx t.target) t.pat with Some newEnv then
      eval {ctx with env = newEnv} t.thn
    else eval ctx t.els

  sem tryMatch (env : Env) (t : Expr) =
  | _ -> None ()
end

lang UtestEval = Eval + Eq + AppEval + UtestAst + BoolAst
  sem eq (e1 : Expr) =
  | _ -> errorSingle [infoTm e1] "Equality not defined for expression"

  sem eval ctx =
  | TmUtest r ->
    let v1 = eval ctx r.test in
    let v2 = eval ctx r.expected in
    let tusing = optionMap (eval ctx) r.tusing in
    let result = match tusing with Some tusing then
      match apply ctx r.info v2 (apply ctx r.info v1 tusing)
      with TmConst {val = CBool {val = b}} then b
      else errorSingle [r.info] "Invalid utest equivalence function"
    else
      eqExpr v1 v2 in
    (if result then print "Test passed\n" else print "Test failed\n");
    eval ctx r.next
end

lang SeqEval = Eval + SeqAst
  sem eval ctx =
  | TmSeq s ->
    let vs = map (eval ctx) s.tms in
    TmSeq {s with tms = vs}
end

lang NeverEval = Eval + NeverAst
  sem eval ctx =
  | TmNever t ->
    errorSingle [t.info] (join [ "Reached a never term, which should be "
            , "impossible in a well-typed program."])
end

-- TODO (oerikss, 2020-03-26): Eventually, this should be a rank 0 tensor.
lang RefEval = Eval
  syn Expr =
  | TmRef {ref : Ref Expr}

  sem eval ctx =
  | TmRef r -> TmRef r
end

type T
con TInt : Tensor[Int] -> T
con TFloat : Tensor[Float] -> T
con TExpr : Tensor[Expr] -> T

lang TensorEval = Eval
  syn Expr =
  | TmTensor { val : T }

  sem eval ctx =
  | TmTensor t -> TmTensor t
end

lang ExtEval = Eval + ExtAst
  sem eval ctx =
  | TmExt r -> eval ctx r.inexpr -- nop
end

---------------
-- CONSTANTS --
---------------
-- All constants in boot have not been implemented. Missing ones can be added
-- as needed.

lang UnsafeCoerceEval = UnsafeCoerceAst + ConstEval
  sem delta info arg =
  | CUnsafeCoerce _ -> arg
end

lang ArithIntEval = ArithIntAst + ConstEval
  syn Const =
  | CAddi2 Int
  | CSubi2 Int
  | CMuli2 Int
  | CDivi2 Int
  | CModi2 Int

  sem constArity =
  | CAddi2 _ -> 1
  | CSubi2 _ -> 1
  | CMuli2 _ -> 1
  | CDivi2 _ -> 1
  | CModi2 _ -> 1

  sem delta info arg =
  | CAddi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CAddi2 n}
    else errorSingle [info] "Not adding an integer"
  | CAddi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = addi n1 n2}}
    else errorSingle [info] "Not adding an integer"
  | CSubi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSubi2 n}
    else errorSingle [info] "Not subtracting an integer"
  | CSubi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = subi n1 n2}}
    else errorSingle [info] "Not subtracting an integer"
  | CMuli _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CMuli2 n}
    else errorSingle [info] "Not multiplying an integer"
  | CMuli2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = muli n1 n2}}
    else errorSingle [info] "Not multiplying an integer"
  | CDivi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CDivi2 n}
    else errorSingle [info] "Not dividing number"
  | CDivi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = divi n1 n2}}
    else errorSingle [info] "Not dividing with number"
  | CModi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CModi2 n}
    else errorSingle [info] "Not taking modulo of number"
  | CModi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = modi n1 n2}}
    else errorSingle [info] "Not taking modulo with number"
  | CNegi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CInt {val = negi n}}
    else errorSingle [info] "Not negating a number"
end

lang ShiftIntEval = ShiftIntAst + ConstEval
  syn Const =
  | CSlli2 Int
  | CSrli2 Int
  | CSrai2 Int

  sem constArity =
  | CSlli2 _ -> 1
  | CSrli2 _ -> 1
  | CSrai2 _ -> 1

  sem delta info arg =
  | CSlli _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSlli2 n}
    else errorSingle [info] "Not shifting a constant integer"
  | CSlli2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = slli n1 n2}}
    else errorSingle [info] "Not shifting by a constant integer"
  | CSrli _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSrli2 n}
    else errorSingle [info] "Not shifting a constant integer"
  | CSrli2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = srli n1 n2}}
    else errorSingle [info] "Not shifting by a constant integer"
  | CSrai _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CSrai2 n}
    else errorSingle [info] "Not shifting a constant integer"
  | CSrai2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CInt {val = srai n1 n2}}
    else errorSingle [info] "Not shifting by a constant integer"
end

lang ArithFloatEval = ArithFloatAst + ConstEval
  syn Const =
  | CAddf2 Float
  | CSubf2 Float
  | CMulf2 Float
  | CDivf2 Float

  sem constArity =
  | CAddf2 _ -> 1
  | CSubf2 _ -> 1
  | CMulf2 _ -> 1
  | CDivf2 _ -> 1

  sem delta info arg =
  | CAddf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CAddf2 f.val}
      else errorSingle [info] "Not adding a numeric constant"
    else errorSingle [info] "Not adding a constant"
  | CAddf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = addf f1 f2.val}}
      else errorSingle [info] "Not adding a numeric constant"
    else errorSingle [info] "Not adding a constant"
  | CSubf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CSubf2 f.val}
      else errorSingle [info] "Not subtracting a numeric constant"
    else errorSingle [info] "Not subtracting a constant"
  | CSubf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = subf f1 f2.val}}
      else errorSingle [info] "Not subtracting a numeric constant"
    else errorSingle [info] "Not subtracting a constant"
  | CMulf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CMulf2 f.val}
      else errorSingle [info] "Not multiplying a numeric constant"
    else errorSingle [info] "Not multiplying a constant"
  | CMulf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = mulf f1 f2.val}}
      else errorSingle [info] "Not multiplying a numeric constant"
    else errorSingle [info] "Not multiplying a constant"
  | CDivf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CDivf2 f.val}
      else errorSingle [info] "Not dividing a numeric constant"
    else errorSingle [info] "Not dividing a constant"
  | CDivf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CFloat {val = divf f1 f2.val}}
      else errorSingle [info] "Not dividing a numeric constant"
    else errorSingle [info] "Not dividing a constant"
  | CNegf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CFloat {val = negf f.val}}
      else errorSingle [info] "Not negating a numeric constant"
    else errorSingle [info] "Not negating a constant"
end

lang FloatIntConversionEval = FloatIntConversionAst
  sem delta info arg =
  | CFloorfi _ ->
    match arg with TmConst (t & {val = CFloat {val = r}}) then
      TmConst {t with val = CInt {val = floorfi r}}
    else errorSingle [info] "Not flooring a float"
  | CCeilfi _ ->
    match arg with TmConst (t & {val = CFloat {val = r}}) then
      TmConst {t with val = CInt {val = ceilfi r}}
    else errorSingle [info] "Not ceiling a float"
  | CRoundfi _ ->
    match arg with TmConst (t & {val = CFloat {val = r}}) then
      TmConst {t with val = CInt {val = roundfi r}}
    else errorSingle [info] "Not rounding a float"
  | CInt2float _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CFloat {val = int2float n}}
    else errorSingle [info] "Not converting a integer"
end

lang CmpIntEval = CmpIntAst + ConstEval
  syn Const =
  | CEqi2 Int
  | CNeqi2 Int
  | CLti2 Int
  | CGti2 Int
  | CLeqi2 Int
  | CGeqi2 Int

  sem constArity =
  | CEqi2 _ -> 1
  | CNeqi2 _ -> 1
  | CLti2 _ -> 1
  | CGti2 _ -> 1
  | CLeqi2 _ -> 1
  | CGeqi2 _ -> 1

  sem delta info arg =
  | CEqi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CEqi2 n}
    else errorSingle [info] "Not comparing an integer constant"
  | CEqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = eqi n1 n2}}
    else errorSingle [info] "Not comparing an integer constant"
  | CNeqi _ ->
    match arg with TmConst (t & {val = CInt {val = n1}}) then
      TmConst {t with val = CNeqi2 n1}
    else errorSingle [info] "Not comparing an integer constant"
  | CNeqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = neqi n1 n2}}
    else errorSingle [info] "Not comparing an integer constant"
  | CLti _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CLti2 n}
    else errorSingle [info] "Not comparing an integer constant"
  | CLti2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = lti n1 n2}}
    else errorSingle [info] "Not comparing an integer constant"
  | CGti _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CGti2 n}
    else errorSingle [info] "Not comparing an integer constant"
  | CGti2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = gti n1 n2}}
    else errorSingle [info] "Not comparing an integer constant"
  | CLeqi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CLeqi2 n}
    else errorSingle [info] "Not comparing an integer constant"
  | CLeqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = leqi n1 n2}}
    else errorSingle [info] "Not comparing an integer constant"
  | CGeqi _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CGeqi2 n}
    else errorSingle [info] "Not comparing an integer constant"
  | CGeqi2 n1 ->
    match arg with TmConst (t & {val = CInt {val = n2}}) then
      TmConst {t with val = CBool {val = geqi n1 n2}}
    else errorSingle [info] "Not comparing an integer constant"
end

lang CmpCharEval = CmpCharAst + ConstEval
  syn Const =
  | CEqc2 Char

  sem constArity =
  | CEqc2 _ -> 1

  sem delta info arg =
  | CEqc _ ->
    match arg with TmConst (t & {val = CChar {val = c}}) then
      TmConst {t with val = CEqc2 c}
    else errorSingle [info] "Not comparing a character constant"
  | CEqc2 c1 ->
    match arg with TmConst (t & {val = CChar {val = c2}}) then
      TmConst {t with val = CBool {val = eqc c1 c2}}
    else errorSingle [info] "Not comparing a character constant"
end

lang IntCharConversionEval = IntCharConversionAst + ConstEval
  sem delta info arg =
  | CInt2Char _ ->
    match arg with TmConst (t & {val = CInt {val = n}}) then
      TmConst {t with val = CChar {val = int2char n}}
    else errorSingle [info] "Not int2char of an integer constant"
  | CChar2Int _ ->
    match arg with TmConst (t & {val = CChar {val = c}}) then
      TmConst {t with val = CInt {val = char2int c}}
    else errorSingle [info] "Not char2int of a character constant"
end

lang CmpFloatEval = CmpFloatAst + ConstEval
  syn Const =
  | CEqf2 Float
  | CLtf2 Float
  | CLeqf2 Float
  | CGtf2 Float
  | CGeqf2 Float
  | CNeqf2 Float

  sem constArity =
  | CEqf2 _ -> 1
  | CLtf2 _ -> 1
  | CLeqf2 _ -> 1
  | CGtf2 _ -> 1
  | CGeqf2 _ -> 1
  | CNeqf2 _ -> 1

  sem delta info arg =
  | CEqf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CEqf2 f.val}
      else errorSingle [info] "Not comparing a numeric constant"
    else errorSingle [info] "Not comparing a constant"
  | CEqf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CBool {val = eqf f1 f2.val}}
      else errorSingle [info] "Not comparing a numeric constant"
    else errorSingle [info] "Not comparing a constant"
  | CLtf _ ->
    match arg with TmConst c then
      match c.val with CFloat f then
        TmConst {c with val = CLtf2 f.val}
      else errorSingle [info] "Not comparing a numeric constant"
    else errorSingle [info] "Not comparing a constant"
  | CLtf2 f1 ->
    match arg with TmConst c then
      match c.val with CFloat f2 then
        TmConst {c with val = CBool {val = ltf f1 f2.val}}
      else errorSingle [info] "Not comparing a numeric constant"
    else errorSingle [info] "Not comparing a constant"
  | CLeqf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CLeqf2 f1}
    else errorSingle [info] "Not comparing a floating-point constant"
  | CLeqf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = leqf f1 f2}}
    else errorSingle [info] "Not comparing a floating-point constant"
  | CGtf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CGtf2 f1}
    else errorSingle [info] "Not comparing a floating-point constant"
  | CGtf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = gtf f1 f2}}
    else errorSingle [info] "Not comparing a floating-point constant"
  | CGeqf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CGeqf2 f1}
    else errorSingle [info] "Not comparing a floating-point constant"
  | CGeqf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = geqf f1 f2}}
    else errorSingle [info] "Not comparing a floating-point constant"
  | CNeqf _ ->
    match arg with TmConst (t & {val = CFloat {val = f1}}) then
      TmConst {t with val = CNeqf2 f1}
    else errorSingle [info] "Not comparing a floating-point constant"
  | CNeqf2 f1 ->
    match arg with TmConst (t & {val = CFloat {val = f2}}) then
      TmConst {t with val = CBool {val = neqf f1 f2}}
    else errorSingle [info] "Not comparing a floating-point constant"
end

lang SymbEval = SymbAst + IntAst + RecordAst + ConstEval
  sem delta info arg =
  | CGensym _ ->
    match arg with TmRecord {bindings = bindings} then
      if mapIsEmpty bindings then
        TmConst {val = CSymb {val = gensym ()}, ty = tyunknown_, info = NoInfo()}
      else errorSingle [info] "Argument in gensym is not unit"
    else errorSingle [info] "Argument in gensym is not unit"
  | CSym2hash _ ->
    match arg with TmConst (t & {val = CSymb s}) then
      TmConst {t with val = CInt {val = sym2hash s.val}}
    else errorSingle [info] "Argument in sym2hash is not a symbol"
end

lang CmpSymbEval = CmpSymbAst + ConstEval
  syn Const =
  | CEqsym2 Symbol

  sem constArity =
  | CEqsym2 _ -> 1

  sem delta info arg =
  | CEqsym _ ->
    match arg with TmConst (t & {val = CSymb s}) then
      TmConst {t with val = CEqsym2 s.val}
    else errorSingle [info] "First argument in eqsym is not a symbol"
  | CEqsym2 s1 ->
    match arg with TmConst (t & {val = CSymb s2}) then
      TmConst {t with val = CBool {val = eqsym s1 s2.val}}
    else errorSingle [info] "Second argument in eqsym is not a symbol"
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
  | CCreate2 Int
  | CCreateList2 Int
  | CCreateRope2 Int
  | CSubsequence2 [Expr]
  | CSubsequence3 ([Expr], Int)
  | CMap2 Expr
  | CMapi2 Expr
  | CIter2 Expr
  | CIteri2 Expr
  | CFoldl2 Expr
  | CFoldl3 (Expr, Expr)
  | CFoldr2 Expr
  | CFoldr3 (Expr, Expr)

  sem constArity =
  | CGet2 _ -> 1
  | CSet2 _ -> 2
  | CSet3 _ -> 3
  | CCons2 _ -> 1
  | CSnoc2 _ -> 1
  | CConcat2 _ -> 1
  | CSplitAt2 _ -> 1
  | CCreate2 _ -> 1
  | CCreateList2 _ -> 1
  | CCreateRope2 _ -> 1
  | CSubsequence2 _ -> 2
  | CSubsequence3 _ -> 1
  | CMap2 _ -> 1
  | CMapi2 _ -> 1
  | CIter2 _ -> 1
  | CIteri2 _ -> 1
  | CFoldl2 _ -> 2
  | CFoldl3 _ -> 1
  | CFoldr2 _ -> 2
  | CFoldr3 _ -> 1

  sem delta info arg =
  | CHead _ ->
    match arg with TmSeq {tms = tms} then
      head tms
    else errorSingle [info] "Not head of a sequence"
  | CTail _ ->
    match arg with TmSeq s then
      TmSeq {s with tms = tail s.tms}
    else errorSingle [info] "Not tail of a sequence"
  | CNull _ ->
    match arg with TmSeq {tms = tms} then
      TmConst {val = CBool {val = null tms}, ty = tyunknown_, info = NoInfo ()}
    else errorSingle [info] "Not null of a sequence"
  | CMap _ ->
    TmConst {val = CMap2 arg, ty = tyunknown_, info = NoInfo ()}
  | CMap2 f ->
    match arg with TmSeq s then
      let f = lam x. apply evalCtxEmpty info x f in
      TmSeq {s with tms = map f s.tms}
    else errorSingle [info] "Second argument to map not a sequence"
  | CMapi _ ->
    TmConst {val = CMapi2 arg, ty = tyunknown_, info = NoInfo ()}
  | CMapi2 f ->
    match arg with TmSeq s then
      let f = lam i. lam x.
        apply evalCtxEmpty info x
          (apply evalCtxEmpty info (int_ i) f) in
      TmSeq {s with tms = mapi f s.tms}
    else errorSingle [info] "Second argument to mapi not a sequence"
  | CIter _ ->
    TmConst {val = CIter2 arg, ty = tyunknown_, info = NoInfo ()}
  | CIter2 f ->
    match arg with TmSeq s then
      let f = lam x. apply evalCtxEmpty info x f; () in
      iter f s.tms;
      uunit_
    else errorSingle [info] "Second argument to iter not a sequence"
  | CIteri _ ->
    TmConst {val = CIteri2 arg, ty = tyunknown_, info = NoInfo ()}
  | CIteri2 f ->
    match arg with TmSeq s then
      let f = lam i. lam x.
        apply evalCtxEmpty info x
          (apply evalCtxEmpty info (int_ i) f); () in
      iteri f s.tms;
      uunit_
    else errorSingle [info] "Second argument to iteri not a sequence"
  | CFoldl _ ->
    TmConst {val = CFoldl2 arg, ty = tyunknown_, info = NoInfo ()}
  | CFoldl2 f ->
    TmConst {val = CFoldl3 (f, arg), ty = tyunknown_, info = NoInfo ()}
  | CFoldl3 (f, acc) ->
    match arg with TmSeq s then
      let f = lam acc. lam x.
        apply evalCtxEmpty info x
          (apply evalCtxEmpty info acc f) in
      foldl f acc s.tms
    else errorSingle [info] "Third argument to foldl not a sequence"
  | CFoldr _ ->
    TmConst {val = CFoldr2 arg, ty = tyunknown_, info = NoInfo ()}
  | CFoldr2 f ->
    TmConst {val = CFoldr3 (f, arg), ty = tyunknown_, info = NoInfo ()}
  | CFoldr3 (f, acc) ->
    match arg with TmSeq s then
      let f = lam x. lam acc.
        apply evalCtxEmpty info acc
          (apply evalCtxEmpty info x f) in
      foldr f acc s.tms
    else errorSingle [info] "Third argument to foldr not a sequence"
  | CGet _ ->
    match arg with TmSeq s then
      TmConst {val = CGet2 s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not a get of a constant sequence"
  | CGet2 tms ->
    match arg with TmConst {val = CInt {val = n}} then
      get tms n
    else errorSingle [info] "n in get is not a number"
  | CSet _ ->
    match arg with TmSeq s then
      TmConst {val = CSet2 s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not a set of a constant sequence"
  | CSet2 tms ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CSet3 (tms, n), ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "n in set is not a number"
  | CSet3 (tms,n) ->
    TmSeq {tms = set tms n arg, ty = tyunknown_, info = NoInfo()}
  | CCons _ ->
    TmConst {val = CCons2 arg, ty = tyunknown_, info = NoInfo()}
  | CCons2 tm ->
    match arg with TmSeq s then
      TmSeq {s with tms = cons tm s.tms}
    else errorSingle [info] "Not a cons of a constant sequence"
  | CSnoc _ ->
    match arg with TmSeq s then
      TmConst {val = CSnoc2 s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not a snoc of a constant sequence"
  | CSnoc2 tms ->
    TmSeq {tms = snoc tms arg, ty = tyunknown_, info = NoInfo()}
  | CConcat _ ->
    match arg with TmSeq s then
      TmConst {val = CConcat2 s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not a concat of a constant sequence"
  | CConcat2 tms ->
    match arg with TmSeq s then
      TmSeq {tms = concat tms s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not a concat of a constant sequence"
  | CLength _ ->
    match arg with TmSeq s then
      TmConst {val = CInt {val = length s.tms}, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not length of a constant sequence"
  | CReverse _ ->
    match arg with TmSeq s then
      TmSeq {tms = reverse s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not reverse of a constant sequence"
  | CSplitAt _ ->
    match arg with TmSeq s then
      TmConst {val = CSplitAt2 s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not splitAt of a constant sequence"
  | CSplitAt2 tms ->
    match arg with TmConst {val = CInt {val = n}} then
      let t = splitAt tms n in
      utuple_ [seq_ t.0, seq_ t.1]
    else errorSingle [info] "n in splitAt is not a number"
  | CCreate _ ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CCreate2 n, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "n in create is not a number"
  | CCreate2 n ->
    let f = lam i. apply evalCtxEmpty info (int_ i) arg in
    TmSeq {tms = create n f, ty = tyunknown_, info = NoInfo()}
  | CCreateList _ ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CCreateList2 n, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "n in create is not a number"
  | CCreateList2 n ->
    let f = lam i. apply evalCtxEmpty info (int_ i) arg in
    TmSeq {tms = createList n f, ty = tyunknown_, info = NoInfo()}
  | CCreateRope _ ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CCreateRope2 n, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "n in create is not a number"
  | CCreateRope2 n ->
    let f = lam i. apply evalCtxEmpty info (int_ i) arg in
    TmSeq {tms = createRope n f, ty = tyunknown_, info = NoInfo()}
  | CIsList _ ->
    match arg with TmSeq s then
      TmConst {
        val = CBool {val = isList s.tms}, ty = tyunknown_, info = NoInfo()
      }
    else errorSingle [info] "Argument to isList is not a sequence"
  | CIsRope _ ->
    match arg with TmSeq s then
      TmConst {
        val = CBool {val = isRope s.tms}, ty = tyunknown_, info = NoInfo()
      }
    else errorSingle [info] "Argument to isRope is not a sequence"
  | CSubsequence _ ->
    match arg with TmSeq s then
      TmConst {val = CSubsequence2 s.tms, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Not subsequence of a constant sequence"
  | CSubsequence2 tms ->
    match arg with TmConst ({val = CInt {val = i}} & t) then
      TmConst {t with val = CSubsequence3 (tms, i)}
    else errorSingle [info] "Second argument to subsequence not a number"
  | CSubsequence3 (tms,offset) ->
    match arg with TmConst ({val = CInt {val = len}} & t) then
      TmSeq {tms = subsequence tms offset len, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "Third argument to subsequence not a number"
end

lang FloatStringConversionEval = FloatStringConversionAst + BoolAst
  sem delta info arg =
  | CStringIsFloat _ ->
    match arg with TmSeq {tms = tms} then
      let s = _evalSeqOfCharsToString info tms in
      TmConst {
        val = CBool { val = stringIsFloat s },
        ty = tyunknown_,
        info = NoInfo ()
      }
    else errorSingle [info] "First argument not a sequence"
  | CString2float _ ->
    match arg with TmSeq {tms = tms} then
      let s = _evalSeqOfCharsToString info tms in
      float_ (string2float s)
    else errorSingle [info] "Not converting a sequence"
  | CFloat2string _ ->
    match arg with TmConst {val = CFloat {val = f}} then
      let tms = _evalStringToSeqOfChars (float2string f) in
      seq_ tms
    else errorSingle [info] "Not converting a float"
end

lang FileOpEval = FileOpAst + SeqAst + BoolAst + CharAst + UnknownTypeAst
  syn Const =
  | CFileWrite2 String

  sem constArity =
  | CFileWrite2 _ -> 1

  sem delta info arg =
  | CFileRead _ ->
    match arg with TmSeq s then
      let f = _evalSeqOfCharsToString info s.tms in
      str_ (readFile f)
    else errorSingle [info] "f in readFile not a sequence"
  | CFileWrite _ ->
    match arg with TmSeq s then
      let f = _evalSeqOfCharsToString info s.tms in
      TmConst {val = CFileWrite2 f, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "f in writeFile not a sequence"
  | CFileWrite2 f ->
    match arg with TmSeq s then
      let d = _evalSeqOfCharsToString info s.tms in
      writeFile f d;
      uunit_
    else errorSingle [info] "d in writeFile not a sequence"
  | CFileExists _ ->
    match arg with TmSeq s then
      let f = _evalSeqOfCharsToString info s.tms in
      TmConst {
        val = CBool {val = fileExists f}, ty = tyunknown_, info = NoInfo()
      }
    else errorSingle [info] "f in fileExists not a sequence"
  | CFileDelete _ ->
    match arg with TmSeq s then
      let f = _evalSeqOfCharsToString info s.tms in
      deleteFile f;
      uunit_
    else errorSingle [info] "f in deleteFile not a sequence"
end

lang IOEval = IOAst + SeqAst + RecordAst + UnknownTypeAst
  sem delta info arg =
  | CPrint _ ->
    match arg with TmSeq s then
      let s = _evalSeqOfCharsToString info s.tms in
      print s;
      uunit_
    else errorSingle [info] "string to print is not a string"
  | CPrintError _ ->
    match arg with TmSeq s then
      let s = _evalSeqOfCharsToString info s.tms in
      printError s;
      uunit_
    else errorSingle [info] "string to print is not a string"
  | CDPrint _ -> uunit_
  | CFlushStdout _ ->
    match arg with TmRecord {bindings = bindings} then
      if mapIsEmpty bindings then
        flushStdout ();
        uunit_
      else errorSingle [info] "Argument to flushStdout is not unit"
    else errorSingle [info] "Argument to flushStdout is not unit"
  | CFlushStderr _ ->
    match arg with TmRecord {bindings = bindings} then
      if mapIsEmpty bindings then
        flushStderr ();
        uunit_
      else errorSingle [info] "Argument to flushStderr is not unit"
    else errorSingle [info] "Argument to flushStderr is not unit"
  | CReadLine _ ->
    match arg with TmRecord {bindings = bindings} then
      if mapIsEmpty bindings then
        let s = readLine () in
        TmSeq {tms = map char_ s, ty = tyunknown_, info = NoInfo()}
      else errorSingle [info] "Argument to readLine is not unit"
    else errorSingle [info] "Argument to readLine is not unit"
end

lang RandomNumberGeneratorEval = RandomNumberGeneratorAst + IntAst
  syn Const =
  | CRandIntU2 Int

  sem constArity =
  | CRandIntU2 _ -> 1

  sem delta info arg =
  | CRandIntU _ ->
    match arg with TmConst c then
      match c.val with CInt lo then
        TmConst {c with val = CRandIntU2 lo.val}
      else errorSingle [info] "lo in randIntU not a constant integer"
    else errorSingle [info] "lo in randIntU not a constant"
  | CRandIntU2 lo ->
    match arg with TmConst c then
      match c.val with CInt hi then
        TmConst {c with val = CInt {val = randIntU lo hi.val}}
      else errorSingle [info] "hi in randIntU not a constant integer"
    else errorSingle [info] "hi in randIntU not a constant"
  | CRandSetSeed _ ->
    match arg with TmConst {val = CInt {val = s}} then
      randSetSeed s;
      uunit_
    else errorSingle [info] "s in randSetSeed not a constant integer"
end

lang SysEval = SysAst + SeqAst + IntAst + CharAst
  sem delta info arg =
  | CError _ ->
    match arg with TmSeq s then
      errorSingle [info] (_evalSeqOfCharsToString info s.tms)
    else
      errorSingle [info] "s in error not a sequence"
  | CExit _ ->
    match arg with TmConst {val = CInt {val = n}} then
      exit n
    else
      errorSingle [info] "n in exit not an integer"
  | CCommand _ ->
    match arg with TmSeq s then
      TmConst {val = CInt {val = command (_evalSeqOfCharsToString info s.tms)},
               ty = tyunknown_, info = NoInfo ()}
    else
      errorSingle [info] "argument to command not a sequence"
end

lang TimeEval = TimeAst + IntAst
  sem delta info arg =
  | CSleepMs _ ->
    match arg with TmConst {val = CInt {val = n}} then
      sleepMs n;
      uunit_
    else errorSingle [info] "n in sleepMs not a constant integer"
  | CWallTimeMs _ ->
    float_ (wallTimeMs ())
end

lang RefOpEval = RefOpAst + RefEval + IntAst
  syn Const =
  | CModRef2 (Ref Expr)

  sem constArity =
  | CModRef2 _ -> 1

  sem delta info arg =
  | CRef _ -> TmRef {ref = ref arg}
  | CModRef _ ->
    match arg with TmRef {ref = r} then
      TmConst {val = CModRef2 r, ty = tyunknown_, info = NoInfo()}
    else errorSingle [info] "first argument of modref not a reference"
  | CModRef2 r ->
    modref r arg;
    uunit_
  | CDeRef _ ->
    match arg with TmRef {ref = r} then
      deref r
    else errorSingle [info] "not a deref of a reference"
end

lang ConTagEval = ConTagAst + DataAst + IntAst + IntTypeAst
  sem delta info arg =
  | CConstructorTag _ ->
    let zeroConst = lam.
      TmConst {val = CInt {val = 0}, ty = TyInt {info = NoInfo ()},
               info = NoInfo ()}
    in
    match arg with TmConApp {ident = id} then
      match nameGetSym id with Some sym then
        TmConst {val = CInt {val = sym2hash sym}, ty = TyInt {info = NoInfo ()},
                 info = NoInfo ()}
      else zeroConst ()
    else zeroConst ()
end

lang MapEval =
  MapAst + UnknownTypeAst + IntAst + IntTypeAst + BoolAst + BoolTypeAst +
  SeqAst + SeqTypeAst + RecordAst + RecordTypeAst + ConstEval

  syn Const =
  | CMapVal {cmp : Expr, val : Map Expr Expr}
  | CMapInsert2 Expr
  | CMapInsert3 (Expr, Expr)
  | CMapRemove2 Expr
  | CMapFindExn2 Expr
  | CMapFindOrElse2 Expr
  | CMapFindOrElse3 (Expr, Expr)
  | CMapFindApplyOrElse2 Expr
  | CMapFindApplyOrElse3 (Expr, Expr)
  | CMapFindApplyOrElse4 (Expr, Expr, Expr)
  | CMapMem2 Expr
  | CMapAny2 Expr
  | CMapMap2 Expr
  | CMapMapWithKey2 Expr
  | CMapFoldWithKey2 Expr
  | CMapFoldWithKey3 (Expr, Expr)
  | CMapChooseOrElse2 Expr
  | CMapEq2 Expr
  | CMapEq3 (Expr, Map Expr Expr)
  | CMapCmp2 Expr
  | CMapCmp3 (Expr, Map Expr Expr)

  sem constArity =
  | CMapVal _ -> 0
  | CMapInsert2 _ -> 2
  | CMapInsert3 _ -> 1
  | CMapRemove2 _ -> 1
  | CMapFindExn2 _ -> 1
  | CMapFindOrElse2 _ -> 2
  | CMapFindOrElse3 _ -> 1
  | CMapFindApplyOrElse2 _ -> 3
  | CMapFindApplyOrElse3 _ -> 2
  | CMapFindApplyOrElse4 _ -> 1
  | CMapMem2 _ -> 1
  | CMapAny2 _ -> 1
  | CMapMap2 _ -> 1
  | CMapMapWithKey2 _ -> 1
  | CMapFoldWithKey2 _ -> 2
  | CMapFoldWithKey3 _ -> 1
  | CMapChooseOrElse2 _ -> 1
  | CMapEq2 _ -> 2
  | CMapEq3 _ -> 1
  | CMapCmp2 _ -> 2
  | CMapCmp3 _ -> 1

  sem _bindToRecord =
  | (k, v) ->
    let labels = map stringToSid ["0", "1"] in
    let bindings = mapFromSeq cmpSID (zip labels [k, v]) in
    TmRecord {
      bindings = bindings,
      ty = TyRecord {
        fields = mapMap (lam. TyUnknown {info = NoInfo ()}) bindings,
        info = NoInfo ()},
      info = NoInfo ()}

  sem delta info arg =
  | CMapEmpty _ ->
    let cmp = lam x. lam y.
      let result =
        apply evalCtxEmpty info y
          (apply evalCtxEmpty info x arg) in
      match result with TmConst {val = CInt {val = i}} then i
      else
        errorSingle [info] "Comparison function of map did not return integer value"
    in
    TmConst {val = CMapVal {cmp = arg, val = mapEmpty cmp},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | CMapInsert _ ->
    TmConst {val = CMapInsert2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapInsert2 key ->
    TmConst {val = CMapInsert3 (key, arg), ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapInsert3 (key, value) ->
    match arg with TmConst ({val = CMapVal m} & t) then
      TmConst {t with val = CMapVal {m with val = mapInsert key value m.val}}
    else errorSingle [info] "Third argument of mapInsert not a map"
  | CMapRemove _ ->
    TmConst {val = CMapRemove2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapRemove2 key ->
    match arg with TmConst ({val = CMapVal m} & t) then
      TmConst {t with val = CMapVal {m with val = mapRemove key m.val}}
    else errorSingle [info] "Second argument of mapRemove not a map"
  | CMapFindExn _ ->
    TmConst {val = CMapFindExn2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapFindExn2 key ->
    match arg with TmConst {val = CMapVal {val = m}} then
      mapFindExn key m
    else errorSingle [info] "Second argument of mapFindExn not a map"
  | CMapFindOrElse _ ->
    TmConst {val = CMapFindOrElse2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapFindOrElse2 elseFn ->
    TmConst {val = CMapFindOrElse3 (elseFn, arg),
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | CMapFindOrElse3 (elseFn, key) ->
    match arg with TmConst {val = CMapVal {val = m}} then
      let elseFn = lam. apply evalCtxEmpty info unit_ elseFn in
      mapFindOrElse elseFn key m
    else errorSingle [info] "Third argument of mapFindOrElse not a map"
  | CMapFindApplyOrElse _ ->
    TmConst {val = CMapFindApplyOrElse2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapFindApplyOrElse2 fapply ->
    TmConst {val = CMapFindApplyOrElse3 (fapply, arg),
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | CMapFindApplyOrElse3 (fapply, felse) ->
    TmConst {val = CMapFindApplyOrElse4 (fapply, felse, arg),
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | CMapFindApplyOrElse4 (fapply, felse, key) ->
    match arg with TmConst {val = CMapVal {val = m}} then
      let fapply = lam v. apply evalCtxEmpty info v fapply in
      let felse = lam. apply evalCtxEmpty info unit_ felse in
      mapFindApplyOrElse fapply felse key m
    else errorSingle [info] "Fourth argument of findApplyOrElse not a map"
  | CMapBindings _ ->
    match arg with TmConst ({val = CMapVal m} & t) then
      TmSeq {tms = map _bindToRecord (mapBindings m.val),
             ty = TySeq {ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()},
             info = NoInfo ()}
    else errorSingle [info] "Argument of mapBindings not a map"
  | CMapChooseExn _ ->
    match arg with TmConst {val = CMapVal {val = m}} then
      _bindToRecord (mapChooseExn m)
    else errorSingle [info] "Argument of mapChooseExn not a map"
  | CMapChooseOrElse _ ->
    TmConst {val = CMapChooseOrElse2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapChooseOrElse2 elseFn ->
    match arg with TmConst {val = CMapVal {val = m}} then
      if gti (mapSize m) 0 then _bindToRecord (mapChooseExn m)
      else apply evalCtxEmpty info unit_ elseFn
    else errorSingle [info] "Second argument of mapChooseOrElse not a map"
  | CMapSize _ ->
    match arg with TmConst {val = CMapVal {val = m}} then
      TmConst {val = CInt {val = mapSize m}, ty = TyInt {info = NoInfo ()},
               info = NoInfo ()}
    else errorSingle [info] "Argument of mapSize not a map"
  | CMapMem _ ->
    TmConst {val = CMapMem2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapMem2 key ->
    match arg with TmConst {val = CMapVal {val = m}} then
      TmConst {val = CBool {val = mapMem key m}, ty = TyBool {info = NoInfo ()},
               info = NoInfo ()}
    else errorSingle [info] "Second argument of mapMem not a map"
  | CMapAny _ ->
    TmConst {val = CMapAny2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapAny2 pred ->
    match arg with TmConst {val = CMapVal {val = m}} then
      let pred = lam k. lam v.
        let result =
          apply evalCtxEmpty info v
            (apply evalCtxEmpty info k pred) in
        match result with TmConst {val = CBool {val = b}} then b
        else
          errorSingle [info] "Predicate of mapAny did not return boolean value"
      in
      TmConst {val = CBool {val = mapAny pred m},
               ty = TyBool {info = NoInfo ()}, info = NoInfo ()}
    else errorSingle [info] "Second argument of mapAny not a map"
  | CMapMap _ ->
    TmConst {val = CMapMap2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapMap2 f ->
    match arg with TmConst ({val = CMapVal m} & t) then
      let f = lam x. apply evalCtxEmpty info x f in
      TmConst {t with val = CMapVal {m with val = mapMap f m.val}}
    else errorSingle [info] "Second argument of mapMap not a map"
  | CMapMapWithKey _ ->
    TmConst {val = CMapMapWithKey2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapMapWithKey2 f ->
    match arg with TmConst ({val = CMapVal m} & t) then
      let f = lam k. lam v.
        apply evalCtxEmpty info v
          (apply evalCtxEmpty info k f) in
      TmConst {t with val = CMapVal {m with val = mapMapWithKey f m.val}}
    else errorSingle [info] "Second argument of mapMapWithKey not a map"
  | CMapFoldWithKey _ ->
    TmConst {val = CMapFoldWithKey2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapFoldWithKey2 f ->
    TmConst {val = CMapFoldWithKey3 (f, arg), ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapFoldWithKey3 (f, acc) ->
    match arg with TmConst ({val = CMapVal m} & t) then
      let f = lam acc. lam k. lam v.
        apply evalCtxEmpty info v
          (apply evalCtxEmpty info k
            (apply evalCtxEmpty info acc f)) in
      mapFoldWithKey f acc m.val
    else errorSingle [info] "Third argument of mapFoldWithKey not a map"
  | CMapEq _ ->
    TmConst {val = CMapEq2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapEq2 eq ->
    match arg with TmConst {val = CMapVal m1} then
      TmConst {val = CMapEq3 (eq, m1.val), ty = TyUnknown {info = NoInfo ()},
               info = NoInfo ()}
    else errorSingle [info] "Second argument of mapEq not a map"
  | CMapEq3 (eq, m1) ->
    match arg with TmConst {val = CMapVal m2} then
      let eq = lam v1. lam v2.
        let result =
          apply evalCtxEmpty info v2
            (apply evalCtxEmpty info v1 eq) in
        match result with TmConst {val = CBool {val = b}} then b
        else
          errorSingle [info] "Equality function of mapEq did not return boolean"
      in
      TmConst {val = CBool {val = mapEq eq m1 m2.val},
               ty = TyBool {info = NoInfo ()}, info = NoInfo ()}
    else errorSingle [info] "Third argument of mapEq not a map"
  | CMapCmp _ ->
    TmConst {val = CMapCmp2 arg, ty = TyUnknown {info = NoInfo ()},
             info = NoInfo ()}
  | CMapCmp2 cmp ->
    match arg with TmConst {val = CMapVal m1} then
      TmConst {val = CMapCmp3 (cmp, m1.val), ty = TyUnknown {info = NoInfo ()},
               info = NoInfo ()}
    else errorSingle [info] "Second argument of mapCmp not a map"
  | CMapCmp3 (cmp, m1) ->
    match arg with TmConst {val = CMapVal m2} then
      let cmp = lam v1. lam v2.
        let result =
          apply evalCtxEmpty info v2
            (apply evalCtxEmpty info v1 cmp) in
        match result with TmConst {val = CInt {val = i}} then i
        else
          errorSingle [info] "Comparison function of mapCmp did not return integer"
      in
      TmConst {val = CInt {val = mapCmp cmp m1 m2.val},
               ty = TyInt {info = NoInfo ()}, info = NoInfo ()}
    else errorSingle [info] "Third argument of mapCmp not a map"
  | CMapGetCmpFun _ ->
    match arg with TmConst {val = CMapVal {cmp = cmp}} then
      cmp
    else errorSingle [info] "Argument to mapGetCmpFun not a map"
end

lang TensorOpEval =
  TensorOpAst + SeqAst + IntAst + FloatAst + TensorEval + ConstEval + BoolAst

  syn Const =
  | CTensorCreateInt2 [Int]
  | CTensorCreateFloat2 [Int]
  | CTensorCreate2 [Int]
  | CTensorGetExn2 T
  | CTensorSetExn2 T
  | CTensorSetExn3 (T, [Int])
  | CTensorLinearGetExn2 T
  | CTensorLinearSetExn2 T
  | CTensorLinearSetExn3 (T, Int)
  | CTensorReshapeExn2 T
  | CTensorTransposeExn2 T
  | CTensorTransposeExn3 (T, Int)
  | CTensorSliceExn2 T
  | CTensorSubExn2 T
  | CTensorSubExn3 (T, Int)
  | CTensorIterSlice2 Expr
  | CTensorEq2 Expr
  | CTensorEq3 (Expr, T)
  | CTensorToString2 Expr

  sem constArity =
  | CTensorCreateInt2 _ -> 1
  | CTensorCreateFloat2 _ -> 1
  | CTensorCreate2 _ -> 1
  | CTensorGetExn2 _ -> 1
  | CTensorSetExn2 _ -> 2
  | CTensorSetExn3 _ -> 1
  | CTensorReshapeExn2 _ -> 1
  | CTensorTransposeExn2 _ -> 2
  | CTensorTransposeExn3 _ -> 1
  | CTensorSliceExn2 _ -> 1
  | CTensorSubExn2 _ -> 2
  | CTensorSubExn3 _ -> 1
  | CTensorIterSlice2 _ -> 1
  | CTensorEq2 _ -> 2
  | CTensorEq3 _ -> 1
  | CTensorToString2 _ -> 1

  sem _ofTmSeq (info : Info) =
  | TmSeq { tms = tms } ->
    map (lam tm. match tm with TmConst { val = CInt { val = n }} then n
                 else errorSingle [info] "Not an integer sequence")
        tms
  | tm -> dprint tm; errorSingle [info] "Not an integer sequence"

  sem _toTmSeq =
  | is ->
    let tms = map (lam i. int_ i) is in
    seq_ tms

  sem apply ctx info arg =
  | TmConst { val = CTensorCreateInt2 shape } ->
    let f = lam is.
      match apply ctx info (_toTmSeq is) arg
      with TmConst { val = CInt { val = n } } then n
      else errorSingle [info] "Expected integer from f in CTensorCreateInt"
    in
    TmTensor { val = TInt (tensorCreateCArrayInt shape f) }
  | TmConst { val = CTensorCreateFloat2 shape } ->
    let f = lam is.
      match apply ctx info (_toTmSeq is) arg
      with TmConst { val = CFloat { val = r } } then r
      else errorSingle [info] "Expected float from f in CTensorCreateFloat"
    in
    TmTensor { val = TFloat (tensorCreateCArrayFloat shape f) }
  | TmConst { val = CTensorCreate2 shape } ->
    let f = lam is. apply ctx info (_toTmSeq is) arg in
    TmTensor { val = TExpr (tensorCreateDense shape f) }
  | TmConst { val = CTensorIterSlice2 f } ->
    match arg with TmTensor { val = t } then

      let mkg = lam mkt. lam i. lam r.
        let res =
          apply ctx info (TmTensor { val = mkt r })  (apply ctx info (int_ i) f)
        in
        ()
      in

      match t with TInt t then
        let g = mkg (lam t. TInt t) in
        tensorIterSlice g t;
        uunit_
      else match t with TFloat t then
        let g = mkg (lam t. TFloat t) in
        tensorIterSlice g t;
        uunit_
      else match t with TExpr t then
        let g = mkg (lam t. TExpr t) in
        tensorIterSlice g t;
        uunit_
      else never
    else errorSingle [info] "Second argument to CTensorIterSlice not a tensor"
  | TmConst { val = CTensorEq3 (eq, t1) } ->
    match arg with TmTensor { val = t2 } then
    let mkeq
      : all a. all b.
        (a -> Expr) -> (b -> Expr) -> Tensor[a] -> Tensor[b] -> Bool =
      lam wrapx. lam wrapy. lam t1. lam t2.
      let eq = lam x. lam y.
        match apply ctx info (wrapy y) (apply ctx info (wrapx x) eq) with
          TmConst { val = CBool { val = b } }
        then b else errorSingle [info] "Invalid equality function"
      in
      tensorEq eq t1 t2
    in
    let result =
      match t1 with TInt t1 then
        match t2 with TInt t2 then mkeq int_ int_ t1 t2
        else match t2 with TFloat t2 then mkeq int_ float_ t1 t2
        else match t2 with TExpr t2 then mkeq int_ (lam x. x) t1 t2
        else never
      else match t1 with TFloat t1 then
        match t2 with TInt t2 then mkeq float_ int_ t1 t2
        else match t2 with TFloat t2 then mkeq float_ float_ t1 t2
        else match t2 with TExpr t2 then mkeq float_ (lam x. x) t1 t2
        else never
      else match t1 with TExpr t1 then
        match t2 with TInt t2 then mkeq (lam x. x) int_ t1 t2
        else match t2 with TFloat t2 then mkeq (lam x. x) float_ t1 t2
        else match t2 with TExpr t2 then mkeq (lam x. x) (lam x. x) t1 t2
        else never
      else never
    in
    bool_ result
    else errorSingle [info] "Third argument to CTensorEq not a tensor"
  | TmConst { val = CTensorToString2 el2str } ->
    match arg with TmTensor { val = t } then
      let el2str = lam x.
        match apply ctx info x el2str with TmSeq { tms = tms } then
          _evalSeqOfCharsToString info tms
        else errorSingle [info] "Invalid element to string function"
      in
      let str =
        match t with TInt t then tensor2string (lam x. el2str (int_ x)) t
        else match t with TFloat t then
          tensor2string (lam x. el2str (float_ x)) t
        else match t with TExpr t then tensor2string el2str t
        else never
      in
      seq_ (_evalStringToSeqOfChars str)
    else errorSingle [info] "Second argument to CTensorToString not a tensor"

  sem delta info arg =
  | CTensorCreateUninitInt _ ->
    TmTensor { val = TInt (tensorCreateUninitInt (_ofTmSeq info arg)) }
  | CTensorCreateUninitFloat _ ->
    TmTensor { val = TFloat (tensorCreateUninitFloat (_ofTmSeq info arg)) }
  | CTensorCreateInt _ ->
    let val = CTensorCreateInt2 (_ofTmSeq info arg) in
    uconst_ val
  | CTensorCreateFloat _ ->
    let val = CTensorCreateFloat2 (_ofTmSeq info arg) in
    uconst_ val
  | CTensorCreate _ ->
    let val = CTensorCreate2 (_ofTmSeq info arg) in
    uconst_ val
  | CTensorGetExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorGetExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorGetExn not a tensor"
  | CTensorGetExn2 t ->
    let is = _ofTmSeq info arg in
    match t with TInt t then
      let val = tensorGetExn t is in
      int_ val
    else match t with TFloat t then
      let val = tensorGetExn t is in
      float_ val
    else match t with TExpr t then
      let val = tensorGetExn t is in
      val
    else never
  | CTensorSetExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorSetExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorSetExn not a tensor"
  | CTensorSetExn2 t ->
    let is = _ofTmSeq info arg in
    let val = CTensorSetExn3 (t, is) in
    uconst_ val
  | CTensorSetExn3 (t, is) ->
    match (t, arg) with (TInt t, TmConst { val = CInt { val = v } }) then
      tensorSetExn t is v;
      uunit_
    else
    match (t, arg) with (TFloat t, TmConst { val = CFloat { val = v } }) then
      tensorSetExn t is v;
      uunit_
    else
    match (t, arg) with (TExpr t, v) then
      tensorSetExn t is v;
      uunit_
    else
      errorSingle [info] "Tensor and value type does not match in CTensorSetExn"
  | CTensorLinearGetExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorLinearGetExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorLinearGetExn not a tensor"
  | CTensorLinearGetExn2 t ->
    match arg with TmConst { val = CInt { val = i } } then
      match t with TInt t then
        let val = tensorLinearGetExn t i in
        int_ val
      else match t with TFloat t then
        let val = tensorLinearGetExn t i in
        float_ val
      else match t with TExpr t then
        let val = tensorLinearGetExn t i in
        val
      else never
    else
      errorSingle [info] "Second argument to CTensorLinearGetExn not an integer"
  | CTensorLinearSetExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorLinearSetExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorLinearSetExn not a tensor"
  | CTensorLinearSetExn2 t ->
    match arg with TmConst { val = CInt { val = i } } then
      let val = CTensorLinearSetExn3 (t, i) in
      uconst_ val
    else
      errorSingle [info] "Second argument to CTensorLinearSetExn not an integer"
  | CTensorLinearSetExn3 (t, i) ->
    match (t, arg) with (TInt t, TmConst { val = CInt { val = v } }) then
      tensorLinearSetExn t i v;
      uunit_
    else
    match (t, arg) with (TFloat t, TmConst { val = CFloat { val = v } }) then
      tensorLinearSetExn t i v;
      uunit_
    else
    match (t, arg) with (TExpr t, v) then
      tensorLinearSetExn t i v;
      uunit_
    else
      errorSingle [info] "Tensor and value type does not match in CTensorLinearSetExn"
  | CTensorRank _ ->
    match arg with TmTensor { val = t } then
      match t with TInt t then int_ (tensorRank t)
      else match t with TFloat t then int_ (tensorRank t)
      else match t with TExpr t then int_ (tensorRank t)
      else never
    else errorSingle [info] "First argument to CTensorRank not a tensor"
  | CTensorShape _ ->
    match arg with TmTensor { val = t } then
      match t with TInt t then _toTmSeq (tensorShape t)
      else match t with TFloat t then _toTmSeq (tensorShape t)
      else match t with TExpr t then _toTmSeq (tensorShape t)
      else never
    else errorSingle [info] "First argument to CTensorRank not a tensor"
  | CTensorReshapeExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorReshapeExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorReshapeExn not a tensor"
  | CTensorReshapeExn2 t ->
    let is = _ofTmSeq info arg in
    match t with TInt t then
      let view = tensorReshapeExn t is in
      TmTensor { val = TInt view }
    else match t with TFloat t then
      let view = tensorReshapeExn t is in
      TmTensor { val = TFloat view }
    else match t with TExpr t then
      let view = tensorReshapeExn t is in
      TmTensor { val = TExpr view }
    else never
  | CTensorCopy _ ->
    match arg with TmTensor { val = t } then
      match t with TInt t then
        let tt = tensorCopy t in
        TmTensor { val = TInt tt }
      else match t with TFloat t then
        let tt = tensorCopy t in
        TmTensor { val = TFloat tt }
      else match t with TExpr t then
        let tt = tensorCopy t in
        TmTensor { val = TExpr tt }
      else never
    else errorSingle [info] "First argument to CTensorCopy not a tensor"
  | CTensorTransposeExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorTransposeExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorTransposeExn not a tensor"
  | CTensorTransposeExn2 t ->
    match arg with TmConst { val = CInt { val = n } } then
      let val = CTensorTransposeExn3 (t, n) in
      uconst_ val
    else
      errorSingle [info] "Second argument to CTensorTransposeExn not an integer"
  | CTensorTransposeExn3 (t, n1) ->
    match arg with TmConst { val = CInt { val = n2 } } then
      match t with TInt t then
        let tt = tensorTransposeExn t n1 n2 in
        TmTensor { val = TInt tt }
      else match t with TFloat t then
        let tt = tensorTransposeExn t n1 n2 in
        TmTensor { val = TFloat tt }
      else match t with TExpr t then
        let tt = tensorTransposeExn t n1 n2 in
        TmTensor { val = TExpr tt }
      else never
    else
      errorSingle [info] "Second argument to CTensorTransposeExn not an integer"
  | CTensorSliceExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorSliceExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorSliceExn not a tensor"
  | CTensorSliceExn2 t ->
    let is = _ofTmSeq info arg in
    match t with TInt t then
      let view = tensorSliceExn t is in
      TmTensor { val = TInt view }
    else match t with TFloat t then
      let view = tensorSliceExn t is in
      TmTensor { val = TFloat view }
    else match t with TExpr t then
      let view = tensorSliceExn t is in
      TmTensor { val = TExpr view }
    else never
  | CTensorSubExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorSubExn2 t in
      uconst_ val
    else errorSingle [info] "First argument to CTensorSubExn not a tensor"
  | CTensorSubExn2 t ->
    match arg with TmConst { val = CInt { val = ofs }} then
      let val = CTensorSubExn3 (t, ofs) in
      uconst_ val
    else errorSingle [info] "Second argument to CTensorSubExn not an integer"
  | CTensorSubExn3 (t, ofs) ->
    match arg with TmConst { val = CInt { val = len }} then
      match t with TInt t then
        let view = tensorSubExn t ofs len in
        TmTensor { val = TInt view }
      else match t with TFloat t then
        let view = tensorSubExn t ofs len in
        TmTensor { val = TFloat view }
      else match t with TExpr t then
        let view = tensorSubExn t ofs len in
        TmTensor { val = TExpr view }
      else never
    else errorSingle [info] "Second argument to CTensorSubExn not an integer"
  | CTensorIterSlice _ ->
    let val = CTensorIterSlice2 arg in
    uconst_ val
  | CTensorEq _ ->
    let val = CTensorEq2 arg in
    uconst_ val
  | CTensorEq2 eq ->
    match arg with TmTensor { val = t } then
      let val = CTensorEq3 (eq, t) in
      uconst_ val
    else errorSingle [info] "Second argument to CTensorEq not a tensor"
  | CTensorToString _ ->
    let val = CTensorToString2 arg in
    uconst_ val
end

lang BootParserEval =
  BootParserAst + UnknownTypeAst + IntAst + IntTypeAst + FloatAst +
  FloatTypeAst + CharAst + CharTypeAst + SeqAst + SeqTypeAst + BoolAst +
  RecordAst

  syn Const =
  | CBootParserTree {val : BootParseTree}
  | CBootParserParseMExprString2 (Bool)
  | CBootParserParseMExprString3 (Bool, [String])
  | CBootParserParseMCoreFile2 (Bool, Bool, [String], Bool, Bool, Bool)
  | CBootParserParseMCoreFile3 ((Bool, Bool, [String], Bool, Bool, Bool), [String])
  | CBootParserGetTerm2 BootParseTree
  | CBootParserGetType2 BootParseTree
  | CBootParserGetString2 BootParseTree
  | CBootParserGetInt2 BootParseTree
  | CBootParserGetFloat2 BootParseTree
  | CBootParserGetListLength2 BootParseTree
  | CBootParserGetConst2 BootParseTree
  | CBootParserGetPat2 BootParseTree
  | CBootParserGetInfo2 BootParseTree

  sem constArity =
  | CBootParserTree _ -> 0
  | CBootParserParseMExprString2 _ -> 2
  | CBootParserParseMExprString3 _ -> 3
  | CBootParserParseMCoreFile2 _ -> 2
  | CBootParserParseMCoreFile3 _ -> 3
  | CBootParserGetTerm2 _ -> 1
  | CBootParserGetType2 _ -> 1
  | CBootParserGetString2 _ -> 1
  | CBootParserGetInt2 _ -> 1
  | CBootParserGetFloat2 _ -> 1
  | CBootParserGetListLength2 _ -> 1
  | CBootParserGetConst2 _ -> 1
  | CBootParserGetPat2 _ -> 1
  | CBootParserGetInfo2 _ -> 1

  sem delta info arg =
  | CBootParserParseMExprString _ ->
    match arg with TmRecord {bindings = bs} then
      match
        map (lam b. mapLookup b bs) (map stringToSid ["0"])
      with [
        Some (TmConst { val = CBool { val = allowFree } })
      ]
      then
        TmConst {val = CBootParserParseMExprString2 ( allowFree ),
                 ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
      else
        errorSingle [info] "First argument to bootParserParseMExprString incorrect record"
    else
      errorSingle [info] "First argument to bootParserParseMExprString not a record"
  | CBootParserParseMExprString2 options ->
    match arg with TmSeq {tms = seq} then
      let keywords =
        map
          (lam keyword.
            match keyword with TmSeq {tms = s} then
              _evalSeqOfCharsToString info s
            else
              errorSingle [info] (join [
                  "Keyword of first argument passed to ",
                  "bootParserParseMExprString not a sequence"
                ]))
          seq in
      TmConst {val = CBootParserParseMExprString3 (options,keywords),
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserParseMExprString not a sequence"
  | CBootParserParseMExprString3 (options, keywords) ->
    match arg with TmSeq {tms = seq} then
      let t =
        bootParserParseMExprString (options,) keywords (_evalSeqOfCharsToString info seq)
      in
      TmConst {val = CBootParserTree {val = t},
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserParseMExprString not a sequence"
  | CBootParserParseMCoreFile _ ->
    match arg with TmRecord {bindings = bs} then
      match
        map (lam b. mapLookup b bs) (map stringToSid ["0", "1", "2", "3", "4", "5"])
      with [
        Some (TmConst { val = CBool { val = keepUtests } }),
        Some (TmConst { val = CBool { val = pruneExternalUtests } }),
        Some (TmSeq { tms = externalsExclude }),
        Some (TmConst { val = CBool { val = warn } }),
        Some (TmConst { val = CBool { val = eliminateDeadCode } }),
        Some (TmConst { val = CBool { val = allowFree } })
      ]
      then
        let externalsExclude =
          map
            (lam x.
              match x with TmSeq {tms = s} then
                _evalSeqOfCharsToString info s
              else
                errorSingle [info] (join [
                    "External identifier of first argument passed to ",
                    "bootParserParseMCoreFile not a sequence"
                  ]))
            externalsExclude
        in
        TmConst {val = CBootParserParseMCoreFile2 (
                  keepUtests,
                  pruneExternalUtests,
                  externalsExclude,
                  warn,
                  eliminateDeadCode,
                  allowFree ),
                 ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
      else
        errorSingle [info] "First argument to bootParserParseMCoreFile incorrect record"
    else
      errorSingle [info] "First argument to bootParserParseMCoreFile not a record"
  | CBootParserParseMCoreFile2 pruneArg ->
    match arg with TmSeq {tms = keywords} then
      let keywords =
        map
          (lam keyword.
            match keyword with TmSeq {tms = s} then
              _evalSeqOfCharsToString info s
            else
              errorSingle [info] (join [
                  "Keyword of third argument passed to ",
                  "bootParserParseMCoreFile not a sequence"
                ]))
          keywords
      in
      TmConst {val = CBootParserParseMCoreFile3 (pruneArg, keywords),
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Third argument to bootParserParseMCoreFile not a sequence"
  | CBootParserParseMCoreFile3 (pruneArg, keywords) ->
    match arg with TmSeq {tms = filename} then
      let filename = _evalSeqOfCharsToString info filename in
      let t = bootParserParseMCoreFile pruneArg keywords filename in
      TmConst {val = CBootParserTree {val = t},
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserParseMCoreFile not a sequence"
  | CBootParserGetId _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CInt {val = bootParserGetId ptree},
               ty = TyInt {info = NoInfo ()}, info = NoInfo ()}
    else errorSingle [info] "Argument to bootParserGetId not a parse tree"
  | CBootParserGetTerm _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetTerm2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetTerm not a parse tree"
  | CBootParserGetTerm2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CBootParserTree {val = bootParserGetTerm ptree n},
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetTerm not an integer"
  | CBootParserGetType _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetType2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetType not a parse tree"
  | CBootParserGetType2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CBootParserTree {val = bootParserGetType ptree n},
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetType not an integer"
  | CBootParserGetString _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetString2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetString not a parse tree"
  | CBootParserGetString2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      let str =
        map
          (lam c. TmConst {val = CChar {val = c},
                           ty = TyChar {info = NoInfo ()}, info = NoInfo ()})
          (bootParserGetString ptree n) in
      TmSeq {tms = str, ty = TySeq {ty = TyChar {info = NoInfo ()},
                                    info = NoInfo ()},
             info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetString not an integer"
  | CBootParserGetInt _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetInt2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetInt not a parse tree"
  | CBootParserGetInt2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CInt {val = bootParserGetInt ptree n},
               ty = TyInt {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetInt not an integer"
  | CBootParserGetFloat _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetFloat2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetFloat not a parse tree"
  | CBootParserGetFloat2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CFloat {val = bootParserGetFloat ptree n},
               ty = TyFloat {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetFloat not an integer"
  | CBootParserGetListLength _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetListLength2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetListLength not a parse tree"
  | CBootParserGetListLength2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CInt {val = bootParserGetListLength ptree n},
               ty = TyInt {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetListLength not an integer"
  | CBootParserGetConst _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetConst2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetConst not a parse tree"
  | CBootParserGetConst2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CBootParserTree {val = bootParserGetConst ptree n},
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetConst not an integer"
  | CBootParserGetPat _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetPat2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetPat not a parse tree"
  | CBootParserGetPat2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CBootParserTree {val = bootParserGetPat ptree n},
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetPat not an integer"
  | CBootParserGetInfo _ ->
    match arg with TmConst {val = CBootParserTree {val = ptree}} then
      TmConst {val = CBootParserGetInfo2 ptree,
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "First argument to bootParserGetInfo not a parse tree"
  | CBootParserGetInfo2 ptree ->
    match arg with TmConst {val = CInt {val = n}} then
      TmConst {val = CBootParserTree {val = bootParserGetInfo ptree n},
               ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
    else
      errorSingle [info] "Second argument to bootParserGetInfo not an integer"
end

--------------
-- PATTERNS --
--------------

lang NamedPatEval = NamedPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatNamed {ident = PName name} -> Some (evalEnvInsert name t env)
  | PatNamed {ident = PWildcard ()} -> Some env
end

lang SeqTotPatEval = SeqTotPat + SeqAst
  sem tryMatch (env : Env) (t : Expr) =
  | PatSeqTot {pats = pats} ->
    match t with TmSeq {tms = tms} then
      if eqi (length tms) (length pats) then
        optionFoldlM
          (lam env. lam pair : (Expr,Pat). tryMatch env pair.0 pair.1)
          env
          (zipWith (lam a. lam b. (a, b)) tms pats)
      else None ()
    else None ()
end

lang SeqEdgePatEval = SeqEdgePat + SeqAst
  sem tryMatch (env : Env) (t : Expr) =
  | PatSeqEdge {prefix = pre, middle = middle, postfix = post} ->
    match t with TmSeq {tms = tms} then
      if geqi (length tms) (addi (length pre) (length post)) then
        match splitAt tms (length pre) with (preTm, tms) then
        match splitAt tms (subi (length tms) (length post)) with (tms, postTm)
        then
        let pair = lam a. lam b. (a, b) in
        let paired = zipWith pair (concat preTm postTm) (concat pre post) in
        let env =
          optionFoldlM
            (lam env. lam pair : (Expr,Pat). tryMatch env pair.0 pair.1)
            env
            paired
        in
        match middle with PName name then
          optionMap (evalEnvInsert name (seq_ tms)) env
        else match middle with PWildcard () then
          env
        else never else never else never
      else None ()
    else None ()
end

lang RecordPatEval = RecordAst + RecordPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatRecord r ->
    match t with TmRecord {bindings = bs} then
      mapFoldlOption
        (lam env. lam k. lam p.
          match mapLookup k bs with Some v then
            tryMatch env v p
          else None ())
        env
        r.bindings
    else None ()
end

lang DataPatEval = DataAst + DataPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatCon {ident = ident, subpat = subpat, info = info} ->
    match t with TmConApp cn then
      if nameEqSymUnsafe ident cn.ident then
        tryMatch env cn.body subpat
      else None ()
    else None ()
end

lang IntPatEval = IntAst + IntPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatInt i ->
    match t with TmConst c then
      match c.val with CInt i2 then
        if eqi i.val i2.val then Some env else None ()
      else None ()
    else None ()
end

lang CharPatEval = CharAst + CharPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatChar ch ->
    match t with TmConst c then
      match c.val with CChar ch2 then
        if eqChar ch.val ch2.val then Some env else None ()
      else None ()
    else None ()
end

lang BoolPatEval = BoolAst + BoolPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatBool b ->
    let xnor = lam x. lam y. or (and x y) (and (not x) (not y)) in
    match t with TmConst c then
      match c.val with CBool b2 then
        if xnor b.val b2.val then Some env else None ()
      else None ()
    else None ()
end

lang AndPatEval = AndPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatAnd {lpat = l, rpat = r} ->
    optionBind (tryMatch env t l) (lam env. tryMatch env t r)
end

lang OrPatEval = OrPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatOr {lpat = l, rpat = r} ->
    optionOrElse (lam. tryMatch env t r) (tryMatch env t l)
end

lang NotPatEval = NotPat
  sem tryMatch (env : Env) (t : Expr) =
  | PatNot {subpat = p} ->
    let res = tryMatch env t p in
    match res with None _ then Some env else
    match res with Some _ then None () else never
end

-------------------------
-- MEXPR EVAL FRAGMENT --
-------------------------

lang MExprEval =

  -- Terms
  VarEval + AppEval + LamEval + RecordEval + RecLetsEval +
  ConstEval + TypeEval + DataEval + MatchEval + UtestEval + SeqEval +
  NeverEval + RefEval + ExtEval

  -- Constants
  + ArithIntEval + ShiftIntEval + ArithFloatEval + CmpIntEval + CmpFloatEval +
  SymbEval + CmpSymbEval + SeqOpEval + FileOpEval + IOEval + SysEval +
  RandomNumberGeneratorEval + FloatIntConversionEval + CmpCharEval +
  IntCharConversionEval + FloatStringConversionEval + TimeEval + RefOpEval +
  ConTagEval + MapEval + TensorOpEval + BootParserEval + UnsafeCoerceEval

  -- Patterns
  + NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval

  -- Pretty Printing
  + MExprPrettyPrint
end


-----------
-- TESTS --
-----------

lang TestLang = MExprEval + MExprPrettyPrint + MExprEq + MExprSym
end

mexpr

use TestLang in

-- Evaluation shorthand used in tests below
let evalNoSymbolize : Expr -> Expr =
  lam t : Expr. eval evalCtxEmpty t in

let eval : Expr -> Expr =
  lam t : Expr. evalNoSymbolize (symbolize t) in

-- Redefine eqExpr annotated with types
let eqExpr : Expr -> Expr -> Bool =
  lam l. lam r. eqExpr l r in

let id = ulam_ "x" (var_ "x") in
let bump = ulam_ "x" (addi_ (var_ "x") (int_ 1)) in
let fst = ulam_ "t" (tupleproj_ 0 (var_ "t")) in
let appIdUnit = app_ id uunit_ in
let appBump3 = app_ bump (int_ 3) in
let appFst = app_ fst (utuple_ [not_ false_, addi_ (int_ 1) (int_ 2)]) in
utest eval appIdUnit with uunit_ using eqExpr in
utest eval appBump3 with int_ 4 using eqExpr in
utest eval appFst with true_ using eqExpr in

let dataDecl =
  bind_ (ucondef_ "Foo")
    (match_ (conapp_ "Foo" (utuple_ [uunit_, uunit_]))
      (pcon_ "Foo" (pvar_ "u"))
      (tupleproj_ 0 (var_ "u"))
      id) in

utest eval dataDecl with uunit_ using eqExpr in

-- Commented out to not clutter the test suite
-- let utest_test1 = utest_ (int_ 1) (int_ 2) uunit_ in
-- let utest_test2 =
--   utest_ (utuple_ [int_ 1, addi_ (int_ 1) (int_ 2)]) (int_ 1, int_ 3) uunit_ in
-- let utest_test3 =
--   bind_ (ucondef_ "Foo")
--     (utest_ (conapp_ "Foo" uunit_) (conapp_ "Foo" uunit_) uunit_) in
-- utest eval utest_test1 with uunit_ in
-- utest eval utest_test2 with uunit_ in
-- utest eval utest_test3 with uunit_ in

-- Implementing an interpreter
let num = lam n.  conapp_ "Num" (int_ n) in
let one = num 1 in -- Num 1
let two = num 2 in -- Num 2
let three = num 3 in -- Num 3
let add = lam n1. lam n2.  conapp_ "Add" (utuple_ [n1, n2]) in
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
    result uunit_ in

let matchOuter =
  match_ (app_ (var_ "eval") (var_ "e1")) (pcon_ "Num" (pvar_ "n1"))
    matchInner uunit_ in

let deconstruct = lam t.
  bindall_
    [(ulet_ "e1" (tupleproj_ 0 t)), (ulet_ "e2" (tupleproj_ 1 t)), matchOuter]
in

let addCase = lam arg. lam els.
  match_ arg (pcon_ "Add" (pvar_ "t")) (deconstruct (var_ "t")) els in

 -- fix (lam eval. lam e. match e with then ... else ())
let evalFn =
  ureclet_ "eval" (ulam_ "e" (num_case (var_ "e") (addCase (var_ "e") uunit_)))
in

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

utest eval srl with true_ using eqExpr in

utest eval evalAdd1 with conapp_ "Num" (int_ 3) using eqExpr in
utest eval evalAdd2 with conapp_ "Num" (int_ 6) using eqExpr in

-- Commented out to declutter test suite output
-- let evalUTestIntInUnit = utest_ (int_ 3) (int_ 3) uunit_ in
-- utest eval evalUTestIntInUnit with uunit_ in

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

utest eval (oddEven (app_ (var_ "odd") (int_ 4))) with false_ using eqExpr in
utest eval (oddEven (app_ (var_ "odd") (int_ 3))) with true_ using eqExpr in
utest eval (oddEven (app_ (var_ "even") (int_ 4))) with true_ using eqExpr in
utest eval (oddEven (app_ (var_ "even") (int_ 3))) with false_ using eqExpr in

let num = lam x. conapp_ "Num" x in
-- lam arg. match arg with Add (Num n1, Num n2) then
--   Num (addi n1 n2)
-- else ()
let addEvalNested = ulam_ "arg"
  (match_ (var_ "arg")
    (ptuple_ [(pcon_ "Num" (pvar_ "n1")), (pcon_ "Num" (pvar_ "n2"))])
    (num (addi_ (var_ "n1") (var_ "n2")))
    (uunit_)) in


utest
  eval (wrapInDecls (app_ addEvalNested (utuple_ [num (int_ 1), num (int_ 2)])))
with conapp_ "Num" (int_ 3)
using eqExpr in

let recordProj =
  bind_ (ulet_ "myrec" (urecord_ [("a", int_ 10),("b", int_ 37),("c", int_ 23)]))
    (recordproj_ "b" (var_ "myrec")) in

let recordUpdate =
  bind_ (ulet_ "myrec" (urecord_ [("a", int_ 10),("b", int_ 37),("c", int_ 23)]))
    (recordproj_ "c" (recordupdate_ (var_ "myrec") "c" (int_ 11))) in

let recordUpdate2 =
  bind_ (ulet_ "myrec" (urecord_ [("a", int_ 10),("b", int_ 37),("c", int_ 23)]))
    (recordproj_ "a" (recordupdate_ (var_ "myrec") "a" (int_ 1729))) in

utest eval recordProj with int_ 37 using eqExpr in
utest eval recordUpdate with int_ 11 using eqExpr in
utest eval recordUpdate2 with int_ 1729 using eqExpr in


let recordUpdateNonValue =
  (recordupdate_ (urecord_ [("a", int_ 10)]) "a" (addi_ (int_ 1729) (int_ 1))) in
utest eval recordUpdateNonValue with urecord_ [("a", int_ 1730)] using eqExpr in


-- Commented out to not clutter the test suite
-- let evalUTestRecordInUnit =
--   utest_
--     (record_add_bindings [("a", int_ 10), ("b", int_ 13)] urecord_empty)
--     (record_add_bindings [("b", int_ 13), ("a", int_ 10)] urecord_empty)
--     uunit_
-- in
-- utest eval evalUTestRecordInUnit with uunit_ in

utest eval (addf_ (float_ 1.) (float_ 2.)) with float_ 3. using eqExpr in
utest eval (subf_ (float_ 1.) (float_ 2.)) with float_ (negf 1.) using eqExpr in
utest eval (mulf_ (float_ 1.) (float_ 2.)) with float_ 2. using eqExpr in
utest eval (divf_ (float_ 1.) (float_ 2.)) with float_ 0.5 using eqExpr in
utest eval (negf_ (float_ 1.)) with float_ (negf 1.) using eqExpr in

utest eval (app_ id (int_ 1)) with int_ 1 using eqExpr in

utest eval (app_ (ulam_ "x" (app_ (var_ "x") (int_ 1))) id)
with int_ 1 using eqExpr in

utest eval (appSeq_ (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))))
                   [int_ 1, int_ 2])
with int_ 3 using eqExpr in

utest eval (appSeq_ (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (int_ 1))))
                   [int_ 1, int_ 2])
with int_ 2 using eqExpr in

utest eval (appSeq_ (ulam_ "x" (ulam_ "x" (addi_ (var_ "x") (int_ 1))))
                   [int_ 1, int_ 2])
with int_ 3 using eqExpr in

-- Builtin sequence functions
-- get [1,2,3] 1 -> 2
let getAst = get_ (seq_ [int_ 1, int_ 2, int_ 3]) (int_ 1) in
utest eval getAst with int_ 2 using eqExpr in

-- set [1,2] 0 3 -> [3,2]
let setAst = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
utest eval setAst with seq_ [int_ 3, int_ 2] using eqExpr in

-- cons 1 [2, 3] -> [1,2,3]
let consAst = cons_ (int_ 1) (seq_ [int_ 2, int_ 3]) in
utest eval consAst with seq_ [int_ 1, int_ 2, int_ 3] using eqExpr in

-- snoc [2, 3] 1 -> [2,3,1]
let snocAst = snoc_ (seq_ [int_ 2, int_ 3]) (int_ 1) in
utest eval snocAst with seq_ [int_ 2, int_ 3, int_ 1] using eqExpr in

-- concat [1,2,3] [4,5,6] -> [1,2,3,4,5,6]
let concatAst = concat_
                  (seq_ [int_ 1, int_ 2, int_ 3])
                  (seq_ [int_ 4, int_ 5, int_ 6]) in
utest eval concatAst
with seq_ [int_ 1, int_ 2, int_ 3, int_ 4, int_ 5, int_ 6] using eqExpr in

-- length [1, 2, 3] -> 3
let lengthAst = length_ (seq_ [int_ 1, int_ 2, int_ 3]) in
utest eval lengthAst with int_ 3 using eqExpr in

-- reverse [1, 2, 3] -> [3, 2, 1]
let reverseAst = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
utest eval reverseAst with seq_ [int_ 3, int_ 2, int_ 1] using eqExpr in

-- splitAt [1,4,2,3] 2 -> ([1,4],[2,3])
let splitAtAst = splitat_ (seq_ [int_ 1, int_ 4, int_ 2, int_ 3]) (int_ 2) in
utest eval splitAtAst
with utuple_ [seq_ [int_ 1, int_ 4], seq_ [int_ 2, int_ 3]]
using eqExpr in

-- create 3 (lam. 42) -> [42, 42, 42]
let createAst = create_ (int_ 3) (ulam_ "_" (int_ 42)) in
utest eval createAst with seq_ [int_ 42, int_ 42, int_ 42] using eqExpr in

-- create 3 (lam i. i) -> [0, 1, 2]
let i = nameSym "i" in
let createAst2 = create_ (int_ 3) (nulam_ i (nvar_ i)) in
utest eval createAst2 with seq_ [int_ 0, int_ 1, int_ 2] using eqExpr in

-- test createRope, createList, isRope, isList
let i = nameSym "i" in
let createList1 = createList_ (int_ 3) (nulam_ i (nvar_ i)) in
let createRope1 = createRope_ (int_ 3) (nulam_ i (nvar_ i)) in
utest eval (isList_ createList1) with true_ using eqExpr in
utest eval (isList_ createRope1) with false_ using eqExpr in
utest eval (isRope_ createRope1) with true_ using eqExpr in
utest eval (isRope_ createList1) with false_ using eqExpr in

-- subsequence [3,5,8,6] 2 4 -> [8,6]
let subseqAst =
  subsequence_ (seq_ [int_ 3, int_ 5, int_ 8, int_ 6]) (int_ 2) (int_ 4)
in
utest eval subseqAst with seq_ [int_ 8, int_ 6] using eqExpr in

-- head [1,2,3] -> 1
utest
  eval (head_ (seq_ [int_ 1, int_ 2, int_ 3]))
with int_ 1 using eqExpr in

-- tail [1,2,3] -> [2,3]
utest
  eval (tail_ (seq_ [int_ 1, int_ 2, int_ 3]))
with seq_ [int_ 2, int_ 3] using eqExpr in

-- map (lam x. addi x 1) [3,4,8,9,20] -> [4,5,9,10,21]
utest
  let x = nameSym "x" in
  let mapAst =
    map_ (nulam_ x (addi_ (nvar_ x) (int_ 1)))
         (seq_ [int_ 3, int_ 4, int_ 8, int_ 9, int_ 20]) in
  eval mapAst
with seq_ [int_ 4, int_ 5, int_ 9, int_ 10, int_ 21]
using eqExpr in

-- mapi (lam x. addi x i) [3,4,8,9,20] -> [3,5,10,12,24]
utest
  let x = nameSym "x" in
  let i = nameSym "i" in
  let mapiAst =
    mapi_ (nulam_ i (nulam_ x (addi_ (nvar_ x) (nvar_ i))))
          (seq_ [int_ 3, int_ 4, int_ 8, int_ 9, int_ 20]) in
  eval mapiAst
with seq_ [int_ 3, int_ 5, int_ 10, int_ 12, int_ 24]
using eqExpr in

-- iter (lam x. addi x 1) [1,2,3] -> ()
utest
  let x = nameSym "x" in
  let iterAst =
    iter_ (nulam_ x (addi_ (nvar_ x) (int_ 1))) (seq_ [int_ 1, int_ 2, int_ 3])
  in
  eval iterAst
with uunit_ using eqExpr in

-- iter (lam x. modref r (addi x (deref r))) [1,2,3,4]
utest
  let x = nameSym "x" in
  let r = nameSym "r" in
  let iterAst = bindall_
  [ nulet_ r (ref_ (int_ 0))
  , ulet_ ""
    (iter_ (nulam_ x (modref_ (nvar_ r) (addi_ (nvar_ x) (deref_ (nvar_ r)))))
           (seq_ [int_ 1, int_ 2, int_ 3, int_ 4]))
  , deref_ (nvar_ r)
  ] in
  eval iterAst
with int_ 10 using eqExpr in

-- iteri (lam i. lam x. addi x i) [1,2,3] -> ()
utest
  let x = nameSym "x" in
  let i = nameSym "i" in
  let iterAst =
    iteri_
      (nulam_ i (nulam_ x (addi_ (nvar_ x) (int_ 1))))
      (seq_ [int_ 1, int_ 2, int_ 3])
  in
  eval iterAst
with uunit_ using eqExpr in

-- iteri (lam i. lam x. modref r (addi i (addi x (deref r)))) [1,2,3,4]
utest
  let x = nameSym "x" in
  let r = nameSym "r" in
  let iteriAst = bindall_
  [ nulet_ r (ref_ (int_ 0))
  , ulet_ ""
    (iteri_ (nulam_ i (nulam_ x (modref_ (nvar_ r)
              (addi_ (nvar_ i) (addi_ (nvar_ x) (deref_ (nvar_ r)))))))
            (seq_ [int_ 1, int_ 2, int_ 3, int_ 4]))
  , deref_ (nvar_ r)
  ] in
  eval iteriAst
with int_ 16 using eqExpr in

-- foldl addi 0 [1,2,3] -> 6
utest
  let foldlAst =
    foldl_ (ulam_ "a" (ulam_ "x" (addi_ (var_ "a") (var_ "x"))))
    (int_ 0) (seq_ [int_ 1, int_ 2, int_ 3]) in
  eval foldlAst
with int_ 6 using eqExpr in

-- foldr cons [] [1,2,3] -> [1,2,3]
utest
  let foldrAst =
    foldr_ (ulam_ "x" (ulam_ "a" (cons_ (var_ "x") (var_ "a"))))
    (seq_ []) (seq_ [int_ 1, int_ 2, int_ 3]) in
  eval foldrAst
with seq_ [int_ 1, int_ 2, int_ 3] using eqExpr in

-- Unit tests for CmpFloatEval
utest eval (eqf_ (float_ 2.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (eqf_ (float_ 1.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (eqf_ (float_ 0.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (ltf_ (float_ 2.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (ltf_ (float_ 1.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (ltf_ (float_ 0.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (leqf_ (float_ 2.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (leqf_ (float_ 1.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (leqf_ (float_ 0.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (gtf_ (float_ 2.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (gtf_ (float_ 1.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (gtf_ (float_ 0.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (geqf_ (float_ 2.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (geqf_ (float_ 1.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (geqf_ (float_ 0.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (neqf_ (float_ 2.0) (float_ 1.0)) with true_ using eqExpr in
utest eval (neqf_ (float_ 1.0) (float_ 1.0)) with false_ using eqExpr in
utest eval (neqf_ (float_ 0.0) (float_ 1.0)) with true_ using eqExpr in

-- Unit tests for symbols

-- gensym
let s1 = eval (gensym_ uunit_) in
let s2 = eval (gensym_ uunit_) in
utest s1 with s1 using eqExpr in
utest s2 with s2 using eqExpr in

-- eqsym
utest eval (eqsym_ s1 s1) with true_ using eqExpr in
utest eval (eqsym_ s1 s2) with false_ using eqExpr in
utest eval (eqsym_ s2 s1) with false_ using eqExpr in
utest eval (bind_ (ulet_ "s" s1) (eqsym_ (var_ "s") (var_ "s")))
with true_ using eqExpr in

-- sym2hash
utest eval (eqi_ (sym2hash_ s1) (sym2hash_ s1)) with true_ using eqExpr in
utest eval (eqi_ (sym2hash_ s2) (sym2hash_ s1)) with false_ using eqExpr in
utest eval (eqi_ (sym2hash_ s1) (sym2hash_ s2)) with false_ using eqExpr in

-- Unit tests for file operations
let f = str_ "test_file_ops" in
let d = str_ "$&!@" in
utest eval (fileExists_ f) with false_ using eqExpr in
utest eval (writeFile_ f d) with uunit_ using eqExpr in
utest eval (fileExists_ f) with true_ using eqExpr in
utest eval (readFile_ f) with d using eqExpr in
utest eval (deleteFile_ f) with uunit_ using eqExpr in
utest eval (fileExists_ f) with false_ using eqExpr in

-- Test error
-- let _ = eval (error_ (str_ "test error message")) in

-- Test exit
-- let _ = eval (exit_ (int_ 1)) in

-- Test argv
-- utest eval argv_ with seq_ [str_ "mi"] in

-- Test command
utest
  if false then eval (command_ (str_ "echo \"Hello world\""))
  else int_ 0
with int_ 0
using eqExpr in

utest eval (match_
  (utuple_ [true_, true_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with true_
using eqExpr in

utest eval (match_
  (utuple_ [true_, false_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with false_
using eqExpr in

utest eval (match_
  (utuple_ [false_, true_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with false_
using eqExpr in

utest eval (match_
  (utuple_ [false_, false_])
  (pand_ (ptuple_ [ptrue_, pvarw_]) (ptuple_ [pvarw_, ptrue_]))
  true_
  false_)
with false_
using eqExpr in

utest eval (match_
  (int_ 1)
  (por_ (pand_ (pint_ 1) (pvar_ "x")) (pand_ (pint_ 2) (pvar_ "x")))
  (var_ "x")
  (int_ 42))
with int_ 1
using eqExpr in

utest eval (match_
  (int_ 2)
  (por_ (pand_ (pint_ 1) (pvar_ "x")) (pand_ (pint_ 2) (pvar_ "x")))
  (var_ "x")
  (int_ 42))
with int_ 2
using eqExpr in

utest eval (match_
  (int_ 3)
  (por_ (pand_ (pint_ 1) (pvar_ "x")) (pand_ (pint_ 2) (pvar_ "x")))
  (var_ "x")
  (int_ 42))
with int_ 42
using eqExpr in

utest eval (match_
  true_
  (pnot_ ptrue_)
  true_
  false_)
with false_
using eqExpr in

utest eval (match_
  false_
  (pnot_ ptrue_)
  true_
  false_)
with true_
using eqExpr in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3, int_ 4, int_ 5])
  (pseqedge_ [pvar_ "a"] "b" [pvar_ "c", pvar_ "d"])
  (utuple_ [var_ "a", var_ "b", var_ "c", var_ "d"])
  false_)
with utuple_ [int_ 1, seq_ [int_ 2, int_ 3], int_ 4, int_ 5]
using eqExpr in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3])
  (pseqedge_ [pvar_ "a"] "b" [pvar_ "c", pvar_ "d"])
  (utuple_ [var_ "a", var_ "b", var_ "c", var_ "d"])
  false_)
with utuple_ [int_ 1, seq_ [], int_ 2, int_ 3]
using eqExpr in

utest eval (match_
  (seq_ [int_ 1, int_ 2])
  (pseqedge_ [pvar_ "a"] "b" [pvar_ "c", pvar_ "d"])
  (utuple_ [var_ "a", var_ "b", var_ "c", var_ "d"])
  false_)
with false_
using eqExpr in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3])
  (pseqtot_ [pvar_ "a", pvar_ "b", pvar_ "c"])
  (utuple_ [var_ "a", var_ "b", var_ "c"])
  false_)
with utuple_ [int_ 1, int_ 2, int_ 3]
using eqExpr in

utest eval (match_
  (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
  (pseqtot_ [pvar_ "a", pvar_ "b", pvar_ "c"])
  (utuple_ [var_ "a", var_ "b", var_ "c"])
  false_)
with false_
using eqExpr in

utest eval (match_
  (seq_ [int_ 1, int_ 2])
  (pseqtot_ [pvar_ "a", pvar_ "b", pvar_ "c"])
  (utuple_ [var_ "a", var_ "b", var_ "c"])
  false_)
with false_
using eqExpr in

utest eval (match_
  (utuple_ [int_ 1, int_ 2])
  (pand_ (pvar_ "a") (ptuple_ [pvar_ "b", pint_ 2]))
  (utuple_ [var_ "a", var_ "b"])
  (utuple_ [utuple_ [int_ 70, int_ 72], int_ 71]))
with utuple_ [utuple_ [int_ 1, int_ 2], int_ 1]
using eqExpr in

-- I/O operations
-- utest eval (print_ (str_ "Hello World")) with uunit_ using eqExpr in
-- utest eval (print_ (readLine_ uunit_)) with uunit_ using eqExpr in
-- utest eval
--   (semi_ (semi_ (print_ (str_ "Hello World"))
--                 (flushStdout_ uunit_))
--          (sleepMs_ (int_ 5000)))
-- with uunit_ using eqExpr in

-- Random number generation
let isIntInSeq = lam r : Expr. lam seq : [Int].
  match r with TmConst {val = CInt {val = n}} then
    any (eqi n) seq
  else false
in

utest eval (bind_ (ulet_ "_" (randSetSeed_ (int_ 42)))
                  (randIntU_ (int_ 1) (int_ 10)))
                  with [1, 2, 3, 4, 5, 6, 7, 8, 9] using isIntInSeq in

utest eval (randIntU_ (int_ 0) (int_ 3)) with [0, 1, 2] using isIntInSeq in

-- Time operations
let t = eval (wallTimeMs_ uunit_) in
utest eval (or_ (leqf_ t (float_ 0.0)) (geqf_ t (float_ 0.0)))
with true_ using eqExpr in
-- utest eval (sleepMs_ (int_ 1000)) with uunit_ in

-- Integer arithmetics
utest eval (addi_ (int_ 4) (int_ 2)) with int_ 6 using eqExpr in
utest eval (subi_ (int_ 4) (int_ 2)) with int_ 2 using eqExpr in
utest eval (muli_ (int_ 4) (int_ 2)) with int_ 8 using eqExpr in
utest eval (divi_ (int_ 4) (int_ 2)) with int_ 2 using eqExpr in
utest eval (divi_ (int_ 4) (int_ 3)) with int_ 1 using eqExpr in
utest eval (modi_ (int_ 4) (int_ 2)) with int_ 0 using eqExpr in
utest eval (modi_ (int_ 4) (int_ 3)) with int_ 1 using eqExpr in
utest eval (addi_ (int_ 4) (negi_ (int_ 2))) with int_ 2 using eqExpr in

-- Float arithmetics
utest eval (addf_ (float_ 4.) (float_ 2.)) with float_ 6. using eqExpr in
utest eval (subf_ (float_ 4.) (float_ 2.)) with float_ 2. using eqExpr in
utest eval (mulf_ (float_ 4.) (float_ 2.)) with float_ 8. using eqExpr in
utest eval (divf_ (float_ 4.) (float_ 2.)) with float_ 2. using eqExpr in
utest eval (addf_ (float_ 4.) (negf_ (float_ 2.))) with float_ 2. using eqExpr in

-- Integer shifting
utest eval (slli_ (int_ 1) (int_ 2)) with int_ 4 using eqExpr in
utest eval (slli_ (int_ 2) (int_ 5)) with int_ 64 using eqExpr in
utest eval (slli_ (negi_ (int_ 1)) (int_ 1))
with eval (negi_ (int_ 2)) using eqExpr in

utest eval (srli_ (int_ 4) (int_ 2)) with int_ 1 using eqExpr in
utest eval (srli_ (int_ 64) (int_ 5)) with int_ 2 using eqExpr in
utest eval (srli_ (negi_ (int_ 2)) (int_ 1))
with int_ 4611686018427387903 using eqExpr in -- NOTE(larshum, 2020-12-07): Assumes 63-bit integers (used in 64-bit OCaml).

utest eval (srai_ (int_ 4) (int_ 2)) with int_ 1 using eqExpr in
utest eval (srai_ (int_ 64) (int_ 5)) with int_ 2 using eqExpr in
utest eval (srai_ (negi_ (int_ 2)) (int_ 1)) with eval (negi_ (int_ 1)) using eqExpr in

-- Integer comparison
utest eval (eqi_ (int_ 2) (int_ 2)) with true_ using eqExpr in
utest eval (eqi_ (negi_ (int_ 2)) (int_ 2)) with false_ using eqExpr in
utest eval (neqi_ (negi_ (int_ 2)) (int_ 2)) with true_ using eqExpr in
utest eval (neqi_ (int_ 5) (int_ 5)) with false_ using eqExpr in
utest eval (lti_ (int_ 1) (int_ 3)) with true_ using eqExpr in
utest eval (lti_ (int_ 1) (int_ 1)) with false_ using eqExpr in
utest eval (gti_ (int_ 3) (int_ 0)) with true_ using eqExpr in
utest eval (gti_ (int_ 1) (int_ 1)) with false_ using eqExpr in
utest eval (leqi_ (int_ 4) (int_ 9)) with true_ using eqExpr in
utest eval (leqi_ (int_ 1) (int_ 1)) with true_ using eqExpr in
utest eval (leqi_ (int_ 2) (int_ 1)) with false_ using eqExpr in
utest eval (geqi_ (int_ 23) (int_ 22)) with true_ using eqExpr in
utest eval (geqi_ (int_ 1) (int_ 1)) with true_ using eqExpr in
utest eval (geqi_ (int_ 0) (int_ 1)) with false_ using eqExpr in

-- Integer-Float conversion
utest eval (floorfi_ (float_ 1.5)) with int_ 1 using eqExpr in
utest eval (ceilfi_ (float_ 1.5)) with int_ 2 using eqExpr in
utest eval (roundfi_ (float_ 1.5)) with int_ 2 using eqExpr in
utest eval (roundfi_ (float_ 1.49)) with int_ 1 using eqExpr in
utest eval (int2float_ (int_ 1)) with float_ 1. using eqExpr in

-- Char comparison
utest eval (eqc_ (char_ 'a') (char_ 'a')) with true_ using eqExpr in
utest eval (eqc_ (char_ '\n') (char_ '\n')) with true_ using eqExpr in
utest eval (eqc_ (char_ 'X') (char_ 'x')) with false_ using eqExpr in

-- Integer-Char conversion
utest eval (int2char_ (int_ 65)) with char_ 'A' using eqExpr in
utest eval (char2int_ (char_ '\t')) with int_ 9 using eqExpr in

-- String-Float conversion
utest eval (string2float_ (str_ "1.5")) with float_ 1.5 using eqExpr in
utest eval (float2string_ (float_ 1.5)) with str_ "1.5" using eqExpr in

-- References
let p = bindall_ [ulet_ "r1" (ref_ (int_ 1)),
                  ulet_ "r2" (ref_ (float_ 2.)),
                  ulet_ "r3" (var_ "r1"),
                  ulet_ "r4"
                    (ref_ (ulam_ "x" (concat_ (str_ "Hello ") (var_ "x"))))]
in
utest eval (bind_ p (modref_ (var_ "r1") (int_ 2))) with uunit_ using eqExpr in
utest
  eval (bind_ p
    (utuple_ [deref_ (var_ "r1"),
             deref_ (var_ "r2"),
             deref_ (var_ "r3"),
             app_ (deref_ (var_ "r4")) (str_ "test")]))
with utuple_ [int_ 1, float_ 2., int_ 1, str_ "Hello test"]
using eqExpr in

utest
  eval (bind_ p (bindall_
    [ulet_ "_" (modref_ (var_ "r1") (int_ 3)),
     ulet_ "_" (modref_ (var_ "r2") (float_ 3.14)),
     ulet_ "_" (modref_ (var_ "r3") (int_ 4)),
     utuple_ [deref_ (var_ "r1"), deref_ (var_ "r2"), deref_ (var_ "r3")]]))
with utuple_ [int_ 4, float_ 3.14, int_ 4]
using eqExpr in

-- Maps

let m1 = mapEmpty_ (uconst_ (CSubi ())) in
utest eval (mapBindings_ m1) with seq_ [] using eqExpr in

let m2 = mapInsert_ (int_ 0) (int_ 1) m1 in
let m3 = mapInsert_ (int_ 1) (int_ 4) m2 in
utest eval (mapBindings_ m2) with seq_ [utuple_ [int_ 0, int_ 1]] using eqExpr in
utest eval (mapBindings_ m3)
with seq_ [utuple_ [int_ 0, int_ 1], utuple_ [int_ 1, int_ 4]] using eqExpr in

let m4 = mapRemove_ (int_ 0) m3 in
let m5 = mapRemove_ (int_ 2) m3 in
utest eval (mapBindings_ m4) with seq_ [utuple_ [int_ 1, int_ 4]] using eqExpr in
utest eval (mapBindings_ m5)
with seq_ [utuple_ [int_ 0, int_ 1], utuple_ [int_ 1, int_ 4]] using eqExpr in

utest eval (mapFindExn_ (int_ 0) m2) with int_ 1 using eqExpr in

let elsef = ulam_ "" (int_ 2) in
utest eval (mapFindOrElse_ elsef (int_ 0) m1) with int_ 2 using eqExpr in
utest eval (mapFindOrElse_ elsef (int_ 0) m2) with int_ 1 using eqExpr in

let applyf = ulam_ "k" (addi_ (var_ "k") (int_ 3)) in
utest eval (mapFindApplyOrElse_ applyf elsef (int_ 0) m1)
with int_ 2 using eqExpr in

utest eval (mapFindApplyOrElse_ applyf elsef (int_ 0) m2)
with int_ 4 using eqExpr in

utest eval (mapSize_ m1) with int_ 0 using eqExpr in
utest eval (mapSize_ m2) with int_ 1 using eqExpr in
utest eval (mapSize_ m3) with int_ 2 using eqExpr in
utest eval (mapSize_ m4) with int_ 1 using eqExpr in
utest eval (mapSize_ m5) with int_ 2 using eqExpr in

utest eval (mapMem_ (int_ 0) m3) with true_ using eqExpr in
utest eval (mapMem_ (int_ 0) m4) with false_ using eqExpr in
utest eval (mapMem_ (int_ 2) m3) with false_ using eqExpr in

let p = ulam_ "k" (ulam_ "v" (eqi_ (addi_ (var_ "k") (var_ "v")) (int_ 5))) in
utest eval (mapAny_ p m2) with false_ using eqExpr in
utest eval (mapAny_ p m3) with true_ using eqExpr in

let mapf = ulam_ "v" (addi_ (var_ "v") (int_ 1)) in
utest eval (mapBindings_ (mapMap_ mapf m3))
with seq_ [utuple_ [int_ 0, int_ 2], utuple_ [int_ 1, int_ 5]] using eqExpr in
utest eval (mapBindings_ (mapMap_ mapf m4))
with seq_ [utuple_ [int_ 1, int_ 5]] using eqExpr in

let mapkv = ulam_ "k" (ulam_ "v" (addi_ (var_ "k") (var_ "v"))) in
utest eval (mapBindings_ (mapMapWithKey_ mapkv m3))
with seq_ [utuple_ [int_ 0, int_ 1], utuple_ [int_ 1, int_ 5]] using eqExpr in
utest eval (mapBindings_ (mapMapWithKey_ mapkv m1)) with seq_ [] using eqExpr in

let foldf = ulam_ "acc" (ulam_ "k" (ulam_ "v" (
  addi_ (var_ "acc") (addi_ (var_ "k") (var_ "v"))))) in
utest eval (mapFoldWithKey_ foldf (int_ 0) m1) with int_ 0 using eqExpr in
utest eval (mapFoldWithKey_ foldf (int_ 0) m3) with int_ 6 using eqExpr in

let eqf = ulam_ "v1" (ulam_ "v2" (eqi_ (var_ "v1") (var_ "v2"))) in
utest eval (mapEq_ eqf m1 m2) with false_ using eqExpr in
utest eval (mapEq_ eqf m3 m4) with false_ using eqExpr in
utest eval (mapEq_ eqf m3 m5) with true_ using eqExpr in

let cmpf = ulam_ "v1" (ulam_ "v2" (subi_ (var_ "v1") (var_ "v2"))) in
utest eval (neqi_ (mapCmp_ cmpf m1 m2) (int_ 0)) with true_ using eqExpr in
utest eval (neqi_ (mapCmp_ cmpf m3 m4) (int_ 0)) with true_ using eqExpr in
utest eval (mapCmp_ cmpf m3 m5) with int_ 0 using eqExpr in

utest eval (mapGetCmpFun_ m1) with uconst_ (CSubi ()) using eqExpr in

-- Tensors
let testTensors = lam tcreate_. lam v : (Expr, Expr, Expr).
  let t0 = eval (tcreate_ (seq_ []) (ulam_ "x" v.0)) in
  let t1 = eval (tcreate_ (seq_ [int_ 4]) (ulam_ "x" v.0)) in
  let t2 = eval (tcreate_ (seq_ [int_ 4]) (ulam_ "x" v.1)) in

  let evaln = evalNoSymbolize in

  utest evaln (utensorGetExn_ t0 (seq_ [])) with v.0 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 0])) with v.0 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 1])) with v.0 using eqExpr in

  utest evaln (utensorSetExn_ t0 (seq_ []) v.1) with uunit_ using eqExpr in
  utest evaln (utensorSetExn_ t1 (seq_ [int_ 0]) v.1) with uunit_ using eqExpr in
  utest evaln (utensorSetExn_ t1 (seq_ [int_ 1]) v.2) with uunit_ using eqExpr in

  utest evaln (utensorGetExn_ t0 (seq_ [])) with v.1 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 0])) with v.1 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 1])) with v.2 using eqExpr in

  utest evaln (utensorRank_ t0) with int_ 0 using eqExpr in
  utest evaln (utensorRank_ t1) with int_ 1 using eqExpr in

  utest evaln (utensorShape_ t0) with seq_ [] using eqExpr in
  utest evaln (utensorShape_ t1) with seq_ [int_ 4] using eqExpr in

  utest evaln (utensorShape_ (utensorReshapeExn_ t0 (seq_ [int_ 1])))
  with seq_ [int_ 1] using eqExpr in

  utest evaln (utensorShape_ (utensorReshapeExn_ t1 (seq_ [int_ 2, int_ 2])))
  with seq_ [int_ 2, int_ 2] using eqExpr in

  utest evaln (utensorRank_ (utensorSliceExn_ t1 (seq_ [int_ 0])))
  with int_ 0 using eqExpr in

  utest evaln (utensorShape_ (utensorSliceExn_ t1 (seq_ [int_ 0])))
  with seq_ [] using eqExpr in

  utest evaln (utensorRank_ (utensorSubExn_ t1 (int_ 0) (int_ 2)))
  with int_ 1 using eqExpr in

  utest evaln (utensorShape_ (utensorSubExn_ t1 (int_ 0) (int_ 2)))
  with seq_ [int_ 2] using eqExpr in

  -- utest evaln (utensorEq_ eqExpr t0 t0) with true_ using eqExpr in

  ()
in

let t3 = eval (tensorCreateInt_ (seq_ [int_ 3]) (ulam_ "x" (int_ 0))) in
let f = eval (ulam_ "i"
                (ulam_ "x"
                   (utensorSetExn_ (var_ "x") (seq_ []) (var_ "i"))))
in

let evaln = evalNoSymbolize in

utest evaln (utensorIterSlice_ f t3) with uunit_ using eqExpr in
utest evaln (utensorGetExn_ t3 (seq_ [int_ 0])) with int_ 0 using eqExpr in
utest evaln (utensorGetExn_ t3 (seq_ [int_ 1])) with int_ 1 using eqExpr in
utest evaln (utensorGetExn_ t3 (seq_ [int_ 2])) with int_ 2 using eqExpr in

testTensors tensorCreateInt_ (int_ 0, int_ 1, int_ 2);
testTensors utensorCreate_ (seq_ [int_ 0], seq_ [int_ 1], seq_ [int_ 2]);

()
