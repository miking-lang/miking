-- Interpreters for the various fragments of MExpr.

include "string.mc"
include "char.mc"
include "name.mc"
include "list.mc"
include "tensor.mc"
include "map.mc"

include "info.mc"
include "error.mc"
include "ast.mc"
include "ast-builder.mc"
include "symbolize.mc"
include "eq.mc"
include "pprint.mc"
include "const-arity.mc"


-------------
-- HELPERS --
-------------

-- Converts a sequence of characters to a string
let _evalSeqOfCharsToString = use MExprAst in
  lam info. lam tms.
    let f = lam c.
      match c with TmConst {val = CChar c} then
        c.val
      else errorSingle [info] "Expected a seqence of characters"
    in
    map f tms

let _evalStringToSeqOfChars = map char_


--------------------
-- EVAL INTERFACE --
--------------------

lang Eval = Ast
  type EvalEnv = List (Name, Expr)
  sem evalEnvEmpty : () -> EvalEnv
  sem evalEnvEmpty =| _ -> listEmpty

  sem evalEnvLookup : Name -> EvalEnv -> Option Expr
  sem evalEnvLookup id =| env ->
    let p = lam entry. nameEqSymUnsafe id entry.0 in
    match listFind p env with Some (_, e) then Some e else None ()

  sem evalEnvInsert : Name -> Expr -> EvalEnv -> EvalEnv
  sem evalEnvInsert id e =| env -> listCons (id, e) env

  sem evalEnvAll : ((Name, Expr) -> Bool) -> EvalEnv -> Bool
  sem evalEnvAll p =| env -> listAll p env

  sem evalEnvFilter : ((Name, Expr) -> Bool) -> EvalEnv -> EvalEnv
  sem evalEnvFilter p =| env -> listFilter p env

  sem evalEnvConcat : EvalEnv -> EvalEnv -> EvalEnv
  sem evalEnvConcat lhs =| rhs -> listConcat lhs rhs

  sem evalEnvIsEmpty : EvalEnv -> Bool
  sem evalEnvIsEmpty =| env -> listNil env

  type EvalCtx = { env : EvalEnv }
  sem evalCtxEmpty : () -> EvalCtx
  sem evalCtxEmpty =| _ -> { env = evalEnvEmpty () }

  sem eval : EvalCtx -> Expr -> Expr
  sem eval ctx =| _ ->
    error "Unsupported Expr in eval!"
end

-----------
-- TERMS --
-----------

lang VarEval = Eval + VarAst
  sem eval ctx =
  | TmVar r ->
    match evalEnvLookup r.ident ctx.env with Some t then t
    else
      errorSingle [r.info]
        (concat "Unknown variable: " (pprintVarString (nameGetStr r.ident)))
end

lang AppEval = Eval + AppAst
  sem apply : EvalCtx -> Info -> (Expr, Expr) -> Expr
  sem apply ctx info =
  | (_, _) -> errorSingle [info] "Bad application"

  sem eval ctx =
  | TmApp r -> apply ctx r.info (eval ctx r.lhs, eval ctx r.rhs)
end

lang ClosAst = Ast + Eval + PrettyPrint + Eq
  type Lazy a = () -> a

  syn Expr =
  | TmClos {ident : Name, body : Expr, env : Lazy EvalEnv, info : Info}

  sem isAtomic =
  | TmClos _ -> true

  sem infoTm =
  | TmClos r -> r.info

  sem withInfo info =
  | TmClos r -> TmClos { r with info = info }

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmClos r ->
    match pprintVarName env r.ident with (env,ident) in
    match pprintCode (pprintIncr indent) env r.body with (env,body) in
   (env,
    join [
      "Clos{lam ", ident, ".",
      pprintNewline (pprintIncr indent), body,
      "}"
    ])

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmClos _ -> error "eqExpr not implemented for TmClos!"
end

lang LamEval = Eval + LamAst + ClosAst + AppEval
  sem apply ctx info =
  | (TmClos t, arg) ->
    eval {ctx with env = evalEnvInsert t.ident arg (t.env ())} t.body

  sem eval ctx =
  | TmLam t ->
    TmClos {ident = t.ident, body = t.body, env = lam. ctx.env, info = t.info}
  | TmClos t -> TmClos t
end

lang LetEval = Eval + LetAst
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
    recursive let envPrime : Lazy EvalEnv = lam.
      let wraplambda = lam v.
        match v with TmLam t then
          TmClos {ident = t.ident, body = t.body, env = envPrime, info = t.info}
        else
          errorSingle [infoTm v]
            "Right-hand side of recursive let must be a lambda"
      in
      foldl
        (lam env. lam bind.
          evalEnvInsert bind.ident (wraplambda bind.body) env)
        ctx.env t.bindings
    in
    eval {ctx with env = envPrime ()} t.inexpr
end

lang ConstAppAst = ConstAst + PrettyPrint + Eq
  syn Expr =
  | TmConstApp {
    const : Const,
    args : [Expr],
    info : Info
  }

  sem infoTm =
  | TmConstApp r -> r.info

  sem withInfo info =
  | TmConstApp r -> TmConstApp { r with info = info }

  sem isAtomic =
  | TmConstApp _ -> true

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmConstApp _ -> error "eqExpr not implemented for TmConstApp!"

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmConstApp r ->
    pprintCode indent env (appSeq_ (uconst_ r.const) r.args)
end

lang ConstDelta = ConstAst
  sem delta : Info -> (Const, [Expr]) -> Expr
end

lang ConstEvalNoDefault =
  Eval + ConstDelta + AppEval + ConstAppAst + SysAst + SeqAst + UnknownTypeAst +
  ConstArity + PrettyPrint

  sem apply ctx info =
  | (TmConst r, arg) -> delta info (r.val, [arg])
  | (TmConstApp r, arg) -> delta info (r.const, snoc r.args arg)

  sem eval ctx =
  | TmConst {val = CArgv {}, info = info} ->
    TmSeq {tms = map str_ argv, ty = tyunknown_, info = info}
  | TmConst c -> TmConst c
end

lang ConstEval = ConstEvalNoDefault
  sem delta info =
  | (const, args) ->
    if lti (length args) (constArity const) then
      TmConstApp {const = const, args = args, info = info}
    else errorSingle [info]
           (join [
             "Invalid application\n",
             expr2str (TmConstApp {const = const, args = args, info = info})
           ])
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

lang MatchEvalBase = Eval
  sem tryMatch : EvalEnv -> Expr -> Pat -> Option EvalEnv
end

lang MatchEval = Eval + MatchAst + MatchEvalBase
  sem eval ctx =
  | TmMatch t ->
    match tryMatch ctx.env (eval ctx t.target) t.pat with Some newEnv then
      eval {ctx with env = newEnv} t.thn
    else eval ctx t.els

  sem tryMatch (env : EvalEnv) (t : Expr) =
  | _ -> None ()
end

lang UtestEval = Eval + Eq + AppEval + UtestAst + BoolAst + SeqAst
  sem eq (e1 : Expr) =
  | _ -> errorSingle [infoTm e1] "Equality not defined for expression"

  sem eval ctx =
  | TmUtest r ->
    let v1 = eval ctx r.test in
    let v2 = eval ctx r.expected in
    let tusing = optionMap (eval ctx) r.tusing in
    let result = match tusing with Some tusing then
      match apply ctx r.info (apply ctx r.info (tusing, v1), v2)
      with TmConst {val = CBool {val = b}} then b
      else errorSingle [r.info] "Invalid utest equivalence function"
    else
      eqExpr v1 v2 in
    (if result then print "Test passed\n" else
      match r.tonfail with Some tonfail then
        match
          apply ctx r.info (apply ctx r.info (tonfail, v1), v2)
          with TmSeq seqr
        then
          print (_evalSeqOfCharsToString seqr.info seqr.tms)
        else errorSingle [r.info] "Invalid utest failure function"
      else print "Test failed\n");
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
lang RefEval = Eval + PrettyPrint + Eq
  syn Expr =
  | TmRef {ref : Ref Expr}

  sem eval ctx =
  | TmRef r -> TmRef r

  sem infoTm =
  | TmRef _ -> NoInfo ()

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmRef _ -> error "eqExpr not implemented for TmRef!"

  sem isAtomic =
  | TmRef _ -> error "isAtomic not implemented for TmRef!"

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmRef _ -> error "pprintCode not implemented for TmRef!"
end

type T
con TInt : Tensor[Int] -> T
con TFloat : Tensor[Float] -> T
con TExpr : use Ast in Tensor[Expr] -> T

lang TensorEval = Eval + Eq + PrettyPrint
  syn Expr =
  | TmTensor {val : T}

  sem eval ctx =
  | TmTensor t -> TmTensor t

  sem infoTm =
  | TmTensor _ -> NoInfo ()

  sem isAtomic =
  | TmTensor _ -> true

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmTensor r ->
    switch r.val
      case TInt t then (env, tensor2string int2string t)
      case TFloat t then (env, tensor2string float2string t)
      case TExpr t1 then
      let t2 = tensorCreateDense (tensorShape t1) (lam. " ") in
      let env =
        tensorFoldi
          (lam env. lam idx. lam e. match pprintCode 0 env e with (env, str) in
                              tensorSetExn t2 idx str; env)
          env t1
      in
      (env, tensor2string (lam x. x) t2)
      end

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmTensor r1 ->
    match lhs with TmTensor r2 then
      switch (r1.val, r2.val)
        case (TInt t1, TInt t2) then
        if tensorEq eqi t1 t2 then Some free
        else None ()
        case (TFloat t1, TFloat t2) then
        if tensorEq eqf t1 t2 then Some free
        else None ()
        case (TExpr t1, TExpr t2) then
        if tensorHasSameShape t1 t2 then
          tensorFoldi
            (lam free. lam idx. lam e1.
              optionBind free
                (lam free. eqExprH env free e1 (tensorGetExn t2 idx)))
            (Some free) t1
        else None ()
        case (_, _) then None ()
      end
    else None ()
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

lang UnsafeCoerceEval = UnsafeCoerceAst + ConstEvalNoDefault + UnsafeCoerceArity
  sem delta info =
  | (CUnsafeCoerce _, [arg]) -> arg
end

lang ArithIntEval = ArithIntAst + ConstEvalNoDefault + ArithIntArity
  sem delta info =
  | (CAddi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = addi n1.val n2.val}}
  | (CSubi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = subi n1.val n2.val}}
  | (CMuli _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = muli n1.val n2.val}}
  | (CDivi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = divi n1.val n2.val}}
  | (CModi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = modi n1.val n2.val}}
  | (CNegi _, [TmConst (t & {val = CInt n})]) ->
    TmConst {t with val = CInt {val = negi n.val}}
end

lang ShiftIntEval = ShiftIntAst + ConstEvalNoDefault + ShiftIntArity
  sem delta info =
  | (CSlli _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = slli n1.val n2.val}}
  | (CSrli _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = srli n1.val n2.val}}
  | (CSrai _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CInt {val = srai n1.val n2.val}}
end

lang ArithFloatEval = ArithFloatAst + ConstEvalNoDefault + ArithFloatArity
  sem delta info =
  | (CAddf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CFloat {val = addf f1.val f2.val}}
  | (CSubf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CFloat {val = subf f1.val f2.val}}
  | (CMulf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CFloat {val = mulf f1.val f2.val}}
  | (CDivf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CFloat {val = divf f1.val f2.val}}
  | (CNegf _, [TmConst (t & {val = CFloat f})]) ->
    TmConst {t with val = CFloat {val = negf f.val}}
end

lang FloatIntConversionEval =
  ConstDelta + FloatIntConversionAst + FloatIntConversionArity
  sem delta info =
  | (CFloorfi _, [TmConst (t & {val = CFloat r})]) ->
    TmConst {t with val = CInt {val = floorfi r.val}}
  | (CCeilfi _, [TmConst (t & {val = CFloat r})]) ->
    TmConst {t with val = CInt {val = ceilfi r.val}}
  | (CRoundfi _, [TmConst (t & {val = CFloat r})]) ->
    TmConst {t with val = CInt {val = roundfi r.val}}
  | (CInt2float _, [TmConst (t & {val = CInt n})]) ->
    TmConst {t with val = CFloat {val = int2float n.val}}
end

lang CmpIntEval = CmpIntAst + ConstEvalNoDefault + CmpIntArity
  sem delta info =
  | (CEqi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CBool {val = eqi n1.val n2.val}}
  | (CNeqi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CBool {val = neqi n1.val n2.val}}
  | (CLti _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CBool {val = lti n1.val n2.val}}
  | (CGti _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CBool {val = gti n1.val n2.val}}
  | (CLeqi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CBool {val = leqi n1.val n2.val}}
  | (CGeqi _, [TmConst {val = CInt n1}, TmConst (t & {val = CInt n2})]) ->
    TmConst {t with val = CBool {val = geqi n1.val n2.val}}
end

lang CmpCharEval = CmpCharAst + ConstEvalNoDefault + CmpCharArity
  sem delta info =
  | (CEqc _, [TmConst {val = CChar c1}, TmConst (t & {val = CChar c2})]) ->
    TmConst {t with val = CBool {val = eqc c1.val c2.val}}
end

lang IntCharConversionEval =
  IntCharConversionAst + ConstEvalNoDefault + IntCharConversionArity

  sem delta info =
  | (CInt2Char _, [TmConst (t & {val = CInt n})]) ->
    TmConst {t with val = CChar {val = int2char n.val}}
  | (CChar2Int _, [TmConst (t & {val = CChar c})]) ->
    TmConst {t with val = CInt {val = char2int c.val}}
end

lang CmpFloatEval = CmpFloatAst + ConstEvalNoDefault + CmpFloatArity
  sem delta info =
  | (CEqf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CBool {val = eqf f1.val f2.val}}
  | (CLtf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CBool {val = ltf f1.val f2.val}}
  | (CLeqf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CBool {val = leqf f1.val f2.val}}
  | (CGtf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CBool {val = gtf f1.val f2.val}}
  | (CGeqf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CBool {val = geqf f1.val f2.val}}
  | (CNeqf _, [TmConst {val = CFloat f1}, TmConst (t & {val = CFloat f2})]) ->
    TmConst {t with val = CBool {val = neqf f1.val f2.val}}
end

lang SymbEval = SymbAst + IntAst + RecordAst + ConstEvalNoDefault + SymbArity
  sem delta info =
  | (CGensym _, [_]) ->
    TmConst {val = CSymb {val = gensym ()}, ty = tyunknown_, info = NoInfo ()}
  | (CSym2hash _, [TmConst (t & {val = CSymb s})]) ->
    TmConst {t with val = CInt {val = sym2hash s.val}}
end

lang CmpSymbEval = CmpSymbAst + ConstEvalNoDefault + CmpSymbArity
  sem delta info =
  | (CEqsym _, [TmConst {val = CSymb s1}, TmConst (t & {val = CSymb s2})]) ->
    TmConst {t with val = CBool {val = eqsym s1.val s2.val}}
end

lang SeqOpEvalFirstOrder =
  SeqOpAst + IntAst + BoolAst + ConstEvalNoDefault + SeqOpArity

  sem delta info =
  | (CHead _, [TmSeq s]) -> head s.tms
  | (CTail _, [TmSeq s]) -> TmSeq {s with tms = tail s.tms}
  | (CNull _, [TmSeq s]) -> TmConst {
    val = CBool {val = null s.tms}, ty = tyunknown_, info = NoInfo ()
  }
  | (CGet _, [TmSeq s, TmConst {val = CInt n}]) -> get s.tms n.val
  | (CSet _, [TmSeq s, TmConst {val = CInt n}, val]) ->
    TmSeq {s with tms = set s.tms n.val val}
  | (CCons _, [tm, TmSeq s]) -> TmSeq {s with tms = cons tm s.tms}
  | (CSnoc _, [TmSeq s, tm]) -> TmSeq {s with tms = snoc s.tms tm}
  | (CConcat _, [TmSeq s1, TmSeq s2]) ->
    TmSeq {s2 with tms = concat s1.tms s2.tms}
  | (CLength _, [TmSeq s]) ->
    TmConst {val = CInt {val = length s.tms}, ty = tyunknown_, info = NoInfo ()}
  | (CReverse _, [TmSeq s]) -> TmSeq {s with tms = reverse s.tms}
  | (CSplitAt _, [TmSeq s, TmConst {val = CInt n}]) ->
    let t = splitAt s.tms n.val in
    utuple_ [TmSeq {s with tms = t.0}, TmSeq {s with tms = t.1}]
  | (CIsList _, [TmSeq s]) ->
    TmConst {
      val = CBool {val = isList s.tms}, ty = tyunknown_, info = NoInfo ()
    }
  | (CIsRope _, [TmSeq s]) ->
    TmConst {
      val = CBool {val = isRope s.tms}, ty = tyunknown_, info = NoInfo ()
    }
  | (CSubsequence _, [
    TmSeq s, TmConst {val = CInt ofs}, TmConst {val = CInt len}
  ]) ->
    TmSeq {s with tms = subsequence s.tms ofs.val len.val}
end

lang SeqOpEval = SeqOpEvalFirstOrder
  sem delta info =
  | (CMap _, [f, TmSeq s]) ->
    let f = lam x. apply (evalCtxEmpty ()) info (f, x) in
    TmSeq {s with tms = map f s.tms}
  | (CMapi _, [f, TmSeq s]) ->
    let f = lam i. lam x.
      apply (evalCtxEmpty ()) info (apply (evalCtxEmpty ()) info (f, int_ i), x)
    in
    TmSeq {s with tms = mapi f s.tms}
  | (CIter _, [f, TmSeq s]) ->
    let f = lam x. apply (evalCtxEmpty ()) info (f, x); () in
    iter f s.tms;
    uunit_
  | (CIteri _, [f, TmSeq s]) ->
    let f = lam i. lam x.
      apply (evalCtxEmpty ()) info
        (apply (evalCtxEmpty ()) info (f, int_ i), x); ()
    in
    iteri f s.tms;
    uunit_
  | (CFoldl _, [f, acc, TmSeq s]) ->
    let f = lam acc. lam x.
      apply (evalCtxEmpty ()) info (apply (evalCtxEmpty ()) info (f, acc), x)
    in
    foldl f acc s.tms
  | (CFoldr _, [f, acc, TmSeq s]) ->
    let f = lam x. lam acc.
      apply (evalCtxEmpty ()) info (apply (evalCtxEmpty ()) info (f, x), acc)
    in
    foldr f acc s.tms
  | (CCreate _, [TmConst {val = CInt n}, f]) ->
    let f = lam i. apply (evalCtxEmpty ()) info (f, int_ i) in
    TmSeq {tms = create n.val f, ty = tyunknown_, info = NoInfo ()}
  | (CCreateList _, [TmConst {val = CInt n}, f]) ->
    let f = lam i. apply (evalCtxEmpty ()) info (f, int_ i) in
    TmSeq {tms = createList n.val f, ty = tyunknown_, info = NoInfo ()}
  | (CCreateRope _, [TmConst {val = CInt n}, f]) ->
    let f = lam i. apply (evalCtxEmpty ()) info (f, int_ i) in
    TmSeq {tms = createRope n.val f, ty = tyunknown_, info = NoInfo ()}
end

lang FloatStringConversionEval =
  ConstDelta + FloatStringConversionAst + BoolAst + FloatStringConversionArity

  sem delta info =
  | (CStringIsFloat _, [TmSeq {tms = tms}]) ->
    TmConst {
      val = CBool {val = stringIsFloat (_evalSeqOfCharsToString info tms)},
      ty = tyunknown_,
      info = NoInfo ()
    }
  | (CString2float _, [TmSeq {tms = tms}]) ->
    TmConst {
      val = CFloat {val = string2float (_evalSeqOfCharsToString info tms)},
      ty = tyunknown_,
      info = NoInfo ()
    }
  | (CFloat2string _, [TmConst {val = CFloat f}]) ->
    TmSeq {
      tms = _evalStringToSeqOfChars (float2string f.val),
      ty = tyunknown_,
      info = NoInfo ()
    }
end

lang FileOpEval =
  ConstDelta + FileOpAst + SeqAst + BoolAst + CharAst + UnknownTypeAst +
  FileOpArity

  sem delta info =
  | (CFileRead _, [TmSeq s]) ->
    let f = _evalSeqOfCharsToString info s.tms in
    str_ (readFile f)
  | (CFileWrite _, [TmSeq f, TmSeq s]) ->
    let f = _evalSeqOfCharsToString info f.tms in
    let d = _evalSeqOfCharsToString info s.tms in
    writeFile f d;
    uunit_
  | (CFileExists _, [TmSeq s]) ->
    let f = _evalSeqOfCharsToString info s.tms in
    TmConst {
      val = CBool {val = fileExists f}, ty = tyunknown_, info = NoInfo ()
    }
  | (CFileDelete _, [TmSeq s]) ->
    let f = _evalSeqOfCharsToString info s.tms in
    deleteFile f;
    uunit_
end

lang IOEval = ConstDelta + IOAst + SeqAst + RecordAst + UnknownTypeAst + IOArity
  sem delta info =
  | (CPrint _, [TmSeq s]) ->
    let s = _evalSeqOfCharsToString info s.tms in
    print s;
    uunit_
  | (CPrintError _, [TmSeq s]) ->
    let s = _evalSeqOfCharsToString info s.tms in
    printError s;
    uunit_
  | (CDPrint _, [_]) -> uunit_
  | (CFlushStdout _, [_]) ->
    flushStdout ();
    uunit_
  | (CFlushStderr _, [_]) ->
    flushStderr ();
    uunit_
  | (CReadLine _, [_]) ->
    let s = readLine () in
    TmSeq {tms = map char_ s, ty = tyunknown_, info = NoInfo ()}
end

lang RandomNumberGeneratorEval =
  ConstDelta + RandomNumberGeneratorAst + IntAst + RandomNumberGeneratorArity

  sem delta info =
  | (CRandIntU _, [TmConst {val = CInt lo}, TmConst (t & {val = CInt hi})]) ->
    TmConst {t with val = CInt {val = randIntU lo.val hi.val}}
  | (CRandSetSeed _, [TmConst {val = CInt n}]) ->
    randSetSeed n.val;
    uunit_
end

lang SysEval = ConstDelta + SysAst + SeqAst + IntAst + CharAst + SysArity
  sem delta info =
  | (CError _, [TmSeq s]) ->
    errorSingle [info] (_evalSeqOfCharsToString info s.tms)
  | (CExit _, [TmConst {val = CInt n}]) -> exit n.val
  | (CCommand _, [TmSeq s]) ->
    TmConst {
      val = CInt {val = command (_evalSeqOfCharsToString info s.tms)},
      ty = tyunknown_, info = NoInfo ()
    }
end

lang TimeEval = ConstDelta + TimeAst + IntAst + TimeArity
  sem delta info =
  | (CSleepMs _, [TmConst {val = CInt n}]) ->
    sleepMs n.val;
    uunit_
  | (CWallTimeMs _, [_]) ->
    float_ (wallTimeMs ())
end

lang RefOpEval = ConstDelta + RefOpAst + RefEval + IntAst + RefOpArity
  sem delta info =
  | (CRef _, [arg]) -> TmRef {ref = ref arg}
  | (CModRef _, [TmRef r, arg]) ->
    modref r.ref arg;
    uunit_
  | (CDeRef _, [TmRef r]) -> deref r.ref
end

lang ConTagEval =
  ConstDelta + ConTagAst + DataAst + IntAst + IntTypeAst + ConTagArity
  sem delta info =
  | (CConstructorTag _, [TmConApp {ident = id}]) ->
    match nameGetSym id with Some sym then TmConst {
      val = CInt {val = sym2hash sym},
      ty = TyInt {info = NoInfo ()},
      info = NoInfo ()
    }
    else
      TmConst {
        val = CInt {val = 0}, ty = TyInt {info = NoInfo ()}, info = NoInfo ()
      }
end

lang TensorOpEval =
  TensorOpAst + SeqAst + IntAst + FloatAst + TensorEval + ConstEvalNoDefault + BoolAst +
  TensorOpArity

  sem _ofTmSeq (info : Info) =
  | TmSeq {tms = tms} ->
    map
      (lam tm.
        match tm with TmConst {val = CInt {val = n}} then n
        else errorSingle [info] "Not an integer sequence")
      tms
  | tm -> dprint tm; errorSingle [info] "Not an integer sequence"

  sem _toTmSeq =
  | is ->
    let tms = map (lam i. int_ i) is in
    seq_ tms

  sem delta info =
  | (CTensorCreateUninitInt _, [shape]) ->
    TmTensor {val = TInt (tensorCreateUninitInt (_ofTmSeq info shape))}
  | (CTensorCreateUninitFloat _, [shape]) ->
    TmTensor {val = TFloat (tensorCreateUninitFloat (_ofTmSeq info shape))}
  | (CTensorCreateInt _, [shape, f]) ->
    let f = lam is.
      match apply (evalCtxEmpty ()) info (f, _toTmSeq is)
        with TmConst {val = CInt n} then n.val
      else errorSingle [info] "Expected integer from f in CTensorCreateInt"
    in
    TmTensor {val = TInt (tensorCreateCArrayInt (_ofTmSeq info shape) f)}
  | (CTensorCreateFloat _, [shape, f]) ->
    let f = lam is.
      match apply (evalCtxEmpty ()) info (f, _toTmSeq is)
        with TmConst {val = CFloat r} then r.val
      else errorSingle [info] "Expected float from f in CTensorCreateFloat"
    in
    TmTensor {val = TFloat (tensorCreateCArrayFloat (_ofTmSeq info shape) f)}
  | (CTensorCreate _, [shape, f]) ->
    let f = lam is. apply (evalCtxEmpty ()) info (f, _toTmSeq is) in
    TmTensor {val = TExpr (tensorCreateDense (_ofTmSeq info shape) f)}
  | (CTensorGetExn _, [TmTensor t, idx]) ->
    let idx = _ofTmSeq info idx in
    switch t.val
    case TInt t then
      let val = tensorGetExn t idx in
      int_ val
    case TFloat t then
      let val = tensorGetExn t idx in
      float_ val
    case TExpr t then
      let val = tensorGetExn t idx in
      val
    end
  | (CTensorSetExn _, [TmTensor t, idx, val]) ->
    let idx = _ofTmSeq info idx in
    switch (t.val, val)
    case (TInt t, TmConst {val = CInt v}) then
      tensorSetExn t idx v.val;
      uunit_
    case (TFloat t, TmConst {val = CFloat v}) then
      tensorSetExn t idx v.val;
      uunit_
    case (TExpr t, v) then
      tensorSetExn t idx v;
      uunit_
    case _ then error "Impossible case in delta!"
    end
  | (CTensorLinearGetExn _, [TmTensor t, TmConst {val = CInt n}]) ->
    switch t.val
      case TInt t then
      let val = tensorLinearGetExn t n.val in
      int_ val
      case TFloat t then
      let val = tensorLinearGetExn t n.val in
      float_ val
      case TExpr t then
      let val = tensorLinearGetExn t n.val in
      val
    end
  | (CTensorLinearSetExn _, [TmTensor t, TmConst {val = CInt n}, val]) ->
    switch (t.val, val)
    case (TInt t, TmConst {val = CInt {val = v}}) then
      tensorLinearSetExn t n.val v;
      uunit_
    case (TFloat t, TmConst {val = CFloat {val = v}}) then
      tensorLinearSetExn t n.val v;
      uunit_
    case (TExpr t, v) then
      tensorLinearSetExn t n.val v;
      uunit_
    case _ then error "Impossible case in delta!"
    end
  | (CTensorRank _, [TmTensor t]) ->
    switch t.val
      case TInt t then int_ (tensorRank t)
      case TFloat t then int_ (tensorRank t)
      case TExpr t then int_ (tensorRank t)
    end
  | (CTensorShape _, [TmTensor t]) ->
    switch t.val
      case TInt t then _toTmSeq (tensorShape t)
      case TFloat t then _toTmSeq (tensorShape t)
      case TExpr t then _toTmSeq (tensorShape t)
    end
  | (CTensorReshapeExn _, [TmTensor t, idx]) ->
    let idx = _ofTmSeq info idx in
    switch t.val
    case TInt t then
      let view = tensorReshapeExn t idx in
      TmTensor {val = TInt view}
    case TFloat t then
      let view = tensorReshapeExn t idx in
      TmTensor {val = TFloat view}
    case TExpr t then
      let view = tensorReshapeExn t idx in
      TmTensor {val = TExpr view}
    end
  | (CTensorCopy _, [TmTensor t]) ->
    switch t.val
    case TInt t then
      let tt = tensorCopy t in
      TmTensor {val = TInt tt}
    case TFloat t then
      let tt = tensorCopy t in
      TmTensor {val = TFloat tt}
    case TExpr t then
      let tt = tensorCopy t in
      TmTensor {val = TExpr tt}
    end
  | (CTensorTransposeExn _, [
    TmTensor t, TmConst {val = CInt n1}, TmConst {val = CInt n2}
  ]) ->
    switch t.val
      case TInt t then
      let tt = tensorTransposeExn t n1.val n2.val in
      TmTensor {val = TInt tt}
      case TFloat t then
      let tt = tensorTransposeExn t n1.val n2.val in
      TmTensor {val = TFloat tt}
      case TExpr t then
      let tt = tensorTransposeExn t n1.val n2.val in
      TmTensor {val = TExpr tt}
    end
  | (CTensorSliceExn _, [TmTensor t, idx]) ->
    let idx = _ofTmSeq info idx in
    switch t.val
    case TInt t then
      let view = tensorSliceExn t idx in
      TmTensor {val = TInt view}
    case TFloat t then
      let view = tensorSliceExn t idx in
      TmTensor {val = TFloat view}
    case TExpr t then
      let view = tensorSliceExn t idx in
      TmTensor {val = TExpr view}
    end
  | (CTensorSubExn _, [
    TmTensor t, TmConst {val = CInt ofs}, TmConst {val = CInt len}
  ]) ->
    switch t.val
      case TInt t then
      let view = tensorSubExn t ofs.val len.val in
      TmTensor {val = TInt view}
      case TFloat t then
      let view = tensorSubExn t ofs.val len.val in
      TmTensor {val = TFloat view}
      case TExpr t then
      let view = tensorSubExn t ofs.val len.val in
      TmTensor {val = TExpr view}
    end
  | (CTensorIterSlice _, [f, TmTensor t]) ->
    let mkg = lam mkt. lam i. lam r.
      let res =
        apply (evalCtxEmpty ()) info
          (apply (evalCtxEmpty ()) info (f, int_ i), TmTensor {val = mkt r})
      in
      ()
    in
    switch t.val
    case TInt t then
      let g = mkg (lam t. TInt t) in
      tensorIterSlice g t;
      uunit_
    case TFloat t then
      let g = mkg (lam t. TFloat t) in
      tensorIterSlice g t;
      uunit_
    case TExpr t then
      let g = mkg (lam t. TExpr t) in
      tensorIterSlice g t;
      uunit_
    end
  | (CTensorEq _, [eq, TmTensor t1, TmTensor t2]) ->
    let mkeq
      : all a. all b.
        (a -> Expr) -> (b -> Expr) -> Tensor[a] -> Tensor[b] -> Bool =
      lam wrapx. lam wrapy. lam t1. lam t2.
        let eq = lam x. lam y.
          match
            apply (evalCtxEmpty ()) info
              (apply (evalCtxEmpty ()) info (eq, wrapx x), wrapy y)
            with TmConst {val = CBool {val = b}}
          then b
          else errorSingle [info] "Invalid equality function"
        in
        tensorEq eq t1 t2
    in
    let result =
      switch t1.val
      case TInt t1 then
        switch t2.val
        case TInt t2 then mkeq int_ int_ t1 t2
        case TFloat t2 then mkeq int_ float_ t1 t2
        case TExpr t2 then mkeq int_ (lam x. x) t1 t2
        end
      case TFloat t1 then
        switch t2.val
        case TInt t2 then mkeq float_ int_ t1 t2
        case TFloat t2 then mkeq float_ float_ t1 t2
        case TExpr t2 then mkeq float_ (lam x. x) t1 t2
        end
      case TExpr t1 then
        switch t2.val
        case TInt t2 then mkeq (lam x. x) int_ t1 t2
        case TFloat t2 then mkeq (lam x. x) float_ t1 t2
        case TExpr t2 then mkeq (lam x. x) (lam x. x) t1 t2
        end
      end
    in
    bool_ result
  | (CTensorToString _, [el2str, TmTensor t]) ->
    let el2str = lam x.
      match apply (evalCtxEmpty ()) info (el2str, x) with TmSeq {tms = tms} then
        _evalSeqOfCharsToString info tms
      else errorSingle [info] "Invalid element to string function"
    in
    let str =
      switch t.val
      case TInt t then tensor2string (lam x. el2str (int_ x)) t
      case TFloat t then tensor2string (lam x. el2str (float_ x)) t
      case TExpr t then tensor2string el2str t
      end
    in
    seq_ (_evalStringToSeqOfChars str)
end

lang BootParserEval =
  ConstDelta + BootParserAst + UnknownTypeAst + IntAst + IntTypeAst + FloatAst +
  FloatTypeAst + CharAst + CharTypeAst + SeqAst + SeqTypeAst + BoolAst +
  RecordAst + BootParserArity + ConstPrettyPrint

  syn Const =
  | CBootParserTree {val : BootParseTree}

  sem getConstStringCode (indent : Int) =
  | CBootParserTree _ ->
    error "getConstStringCode not implemented for CBootParserTree!"

  sem constArity =
  | CBootParserTree _ -> 0

  sem delta info =
  | (CBootParserParseMExprString _, [
    TmRecord {bindings = bs}, TmSeq {tms = seq1}, TmSeq {tms = seq2}
  ]) ->
    match
      map (lam b. mapLookup b bs) (map stringToSid ["0"])
      with [
        Some (TmConst {val = CBool {val = allowFree}})
      ]
    then
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
          seq1 in
      let t =
        bootParserParseMExprString
          (allowFree,) keywords (_evalSeqOfCharsToString info seq2)
      in
      TmConst {
        val = CBootParserTree {val = t},
        ty = TyUnknown {info = NoInfo ()},
        info = NoInfo ()
      }
    else
      errorSingle [info]
        "First argument to bootParserParseMExprString incorrect record"
  | (CBootParserParseMLangString _, [TmSeq {tms = seq}]) ->
    let t = bootParserParseMLangString (_evalSeqOfCharsToString info seq) in
    TmConst {
        val = CBootParserTree {val = t},
        ty = TyUnknown {info = NoInfo ()},
        info = NoInfo ()
    }
  | (CBootParserParseMLangFile _, [TmSeq {tms = seq}]) ->
    let t = bootParserParseMLangFile (_evalSeqOfCharsToString info seq) in
    TmConst {
        val = CBootParserTree {val = t},
        ty = TyUnknown {info = NoInfo ()},
        info = NoInfo ()
    }
  | (CBootParserParseMCoreFile _, [
    TmRecord {bindings = bs}, TmSeq {tms = keywords}, TmSeq {tms = filename}
  ]) ->
    match
      map (lam b. mapLookup b bs) (map stringToSid ["0", "1", "2", "3", "4", "5"])
      with [
        Some (TmConst {val = CBool {val = keepUtests}}),
        Some (TmConst {val = CBool {val = pruneExternalUtests}}),
        Some (TmSeq {tms = externalsExclude}),
        Some (TmConst {val = CBool {val = warn}}),
        Some (TmConst {val = CBool {val = eliminateDeadCode}}),
        Some (TmConst {val = CBool {val = allowFree}})
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
      let pruneArg = (keepUtests,
                      pruneExternalUtests,
                      externalsExclude,
                      warn,
                      eliminateDeadCode,
                      allowFree)
      in
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

      let filename = _evalSeqOfCharsToString info filename in
      let t = bootParserParseMCoreFile pruneArg keywords filename in
      TmConst {
        val = CBootParserTree {val = t},
        ty = TyUnknown {info = NoInfo ()},
        info = NoInfo ()
      }
    else
      errorSingle [info]
        "First argument to bootParserParseMCoreFile incorrect record"
  | (CBootParserGetId _, [TmConst {val = CBootParserTree {val = ptree}}]) ->
    TmConst {val = CInt {val = bootParserGetId ptree},
             ty = TyInt {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetTerm _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CBootParserTree {val = bootParserGetTerm ptree n},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetTop _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CBootParserTree {val = bootParserGetTop ptree n},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetDecl _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CBootParserTree {val = bootParserGetDecl ptree n},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetType _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CBootParserTree {val = bootParserGetType ptree n},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetString _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    let str =
      map
        (lam c. TmConst {val = CChar {val = c},
                       ty = TyChar {info = NoInfo ()}, info = NoInfo ()})
        (bootParserGetString ptree n) in
    TmSeq {
      tms = str,
      ty = TySeq {ty = TyChar {info = NoInfo ()}, info = NoInfo ()},
      info = NoInfo ()
    }
  | (CBootParserGetInt _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CInt {val = bootParserGetInt ptree n},
             ty = TyInt {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetFloat _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CFloat {val = bootParserGetFloat ptree n},
             ty = TyFloat {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetListLength _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CInt {val = bootParserGetListLength ptree n},
             ty = TyInt {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetConst _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CBootParserTree {val = bootParserGetConst ptree n},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetPat _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CBootParserTree {val = bootParserGetPat ptree n},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
  | (CBootParserGetInfo _, [
    TmConst {val = CBootParserTree {val = ptree}},
    TmConst {val = CInt {val = n}}
  ]) ->
    TmConst {val = CBootParserTree {val = bootParserGetInfo ptree n},
             ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}
end

--------------
-- PATTERNS --
--------------

lang NamedPatEval = MatchEvalBase + NamedPat + Eval
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatNamed {ident = PName name} -> Some (evalEnvInsert name t env)
  | PatNamed {ident = PWildcard ()} -> Some env
end

lang SeqTotPatEval = MatchEvalBase + SeqTotPat + SeqAst
  sem tryMatch (env : EvalEnv) (t : Expr) =
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

lang SeqEdgePatEval = MatchEvalBase + SeqEdgePat + SeqAst + Eval
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatSeqEdge {prefix = pre, middle = middle, postfix = post} ->
    match t with TmSeq (r & {tms = tms}) then
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
          optionMap (evalEnvInsert name (TmSeq { r with tms = tms })) env
        else match middle with PWildcard () then
          env
        else never else never else never
      else None ()
    else None ()
end

lang RecordPatEval = MatchEvalBase + RecordAst + RecordPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatRecord r ->
    match t with TmRecord {bindings = bs} then
      let f : Option Pat -> Option Expr -> Option (EvalEnv -> Option EvalEnv) =
        lam pat. lam val.
        match pat with Some p then
          match val with Some v then
            Some (lam env. tryMatch env v p)
          else None ()
        else None ()
      in
      mapFoldlOption
        (lam env. lam. lam f. f env)
        env
        (mapMerge f r.bindings bs)
    else None ()
end

lang DataPatEval = MatchEvalBase + DataAst + DataPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatCon {ident = ident, subpat = subpat, info = info} ->
    match t with TmConApp cn then
      if nameEqSymUnsafe ident cn.ident then
        tryMatch env cn.body subpat
      else None ()
    else None ()
end

lang IntPatEval = MatchEvalBase + IntAst + IntPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatInt i ->
    match t with TmConst c then
      match c.val with CInt i2 then
        if eqi i.val i2.val then Some env else None ()
      else None ()
    else None ()
end

lang CharPatEval = MatchEvalBase + CharAst + CharPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatChar ch ->
    match t with TmConst c then
      match c.val with CChar ch2 then
        if eqChar ch.val ch2.val then Some env else None ()
      else None ()
    else None ()
end

lang BoolPatEval = MatchEvalBase + BoolAst + BoolPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatBool b ->
    let xnor = lam x. lam y. or (and x y) (and (not x) (not y)) in
    match t with TmConst c then
      match c.val with CBool b2 then
        if xnor b.val b2.val then Some env else None ()
      else None ()
    else None ()
end

lang AndPatEval = MatchEvalBase + AndPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatAnd {lpat = l, rpat = r} ->
    optionBind (tryMatch env t l) (lam env. tryMatch env t r)
end

lang OrPatEval = MatchEvalBase + OrPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
  | PatOr {lpat = l, rpat = r} ->
    optionMapOrElse (lam. tryMatch env t r) (lam x. Some x) (tryMatch env t l)
end

lang NotPatEval = MatchEvalBase + NotPat
  sem tryMatch (env : EvalEnv) (t : Expr) =
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
  NeverEval + RefEval + ExtEval +

  -- Constants
  IntArity + FloatArity + BoolArity + CharArity + SymbArity + BootParserArity +
  ArithIntEval + ShiftIntEval + ArithFloatEval + CmpIntEval + CmpFloatEval +
  SymbEval + CmpSymbEval + SeqOpEval + FileOpEval + IOEval + SysEval +
  RandomNumberGeneratorEval + FloatIntConversionEval + CmpCharEval +
  IntCharConversionEval + FloatStringConversionEval + TimeEval + RefOpEval +
  ConTagEval + TensorOpEval + BootParserEval + UnsafeCoerceEval +

  -- Patterns
  NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval +

  -- Pretty Printing
  MExprPrettyPrint
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
  lam t : Expr. eval (evalCtxEmpty ()) t in

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
