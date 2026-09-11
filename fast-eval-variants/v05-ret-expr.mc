-- VALUE TYPE: evaluate to `Expr` instead of a dedicated `Val` syn.
--
-- The baseline has a compact `Val` type: an integer is `VInt n`, one block with
-- one field.  This variant does what eval.mc does and reuses `Expr` as the value
-- type, so the same integer is `TmConst {val = CInt {val = n}, ty = ..., info =
-- ...}` -- three blocks deep, two of whose fields the evaluator never reads.
-- Closures and partially applied constants have nowhere to live in `Expr`, so
-- they are added to it as new constructors.
--
-- This is the allocation-shape question: how much does carrying `ty` and `info`
-- on every intermediate value cost?

include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "utest.mc"
include "list.mc"
include "option.mc"
include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "common.mc"

lang EvalF = Ast + UnknownTypeAst
  -- Values *are* expressions here; the constructors below are the value forms
  -- that have no ordinary `Expr` representation.
  type Val = Expr

  syn Expr =
  | VError (Info, String)

  sem readback : Val -> Option Expr
  sem readback =| e -> Some e

  type EvalFEnv = List (Int, Val)

  sem evalFEnvLookup : Int -> EvalFEnv -> Val
  sem evalFEnvLookup s1 =
  | Nil _ -> error "env lookup failed!"
  | Cons ((s2, val), env) -> if eqi s1 s2 then val else evalFEnvLookup s1 env

  sem mkEvalF : Expr -> EvalFEnv -> Val
  sem mkEvalF =| _ -> error "Unsupported Expr in mkEvalF!"

  sem mkEvalDeclF : Decl -> EvalFEnv -> EvalFEnv
  sem mkEvalDeclF =| _ -> error "Unsupported Decl in mkEvalDeclF!"
end

---------------------
-- TERMS AND DECLS --
---------------------

lang VarEvalF = EvalF + VarAst
  sem mkEvalF =
  | TmVar r ->
    match nameGetSym r.ident with Some s1 then
      evalFEnvLookup (sym2hash s1)
    else error "Unsymbolized TmVarin mkEvalF!"
end

lang AppEvalF = EvalF + AppAst + ConstAst + UnknownTypeAst
  -- The partially applied constant values and `mkDeltaF` live here rather than
  -- in ConstEvalF so that the application case below can consult them while
  -- compiling; ConstEvalF still supplies all the actual cases.
  syn Expr =
  | VConst1 (Const, Val -> Val)
  | VConst2 (Const, Val -> Val -> Val)
  | VConst3 (Const, Val -> Val -> Val -> Val)

  sem mkDeltaF : Const -> Val

  sem mkEvalF =
  | TmApp r ->
    -- A constant applied to exactly as many arguments as it takes: resolve the
    -- delta function once, while compiling, and emit a closure that calls it
    -- directly.  The general path would instead build a VConst2/VConst1 chain
    -- and take it apart again on every single evaluation.  The three shapes
    -- are disjoint, since each looks through a different number of TmApp
    -- layers before expecting a TmConst, and a constant used as a value still
    -- falls through to `mkEvalFApp`.
    match r with
      {lhs = TmApp {lhs = TmApp {lhs = TmConst c, rhs = a}, rhs = b}, rhs = d}
    then
      match mkDeltaF c.val with VConst3 (_, f) then
        let a = mkEvalF a in
        let b = mkEvalF b in
        let d = mkEvalF d in
        lam env. f (a env) (b env) (d env)
      else mkEvalFApp r
    else match r with {lhs = TmApp {lhs = TmConst c, rhs = a}, rhs = b} then
      match mkDeltaF c.val with VConst2 (_, f) then
        let a = mkEvalF a in
        let b = mkEvalF b in
        lam env. f (a env) (b env)
      else mkEvalFApp r
    else match r with {lhs = TmConst c, rhs = a} then
      match mkDeltaF c.val with VConst1 (_, f) then
        let a = mkEvalF a in
        lam env. f (a env)
      else mkEvalFApp r
    else mkEvalFApp r

  sem mkEvalFApp : {lhs : Expr, rhs : Expr, ty : Type, info : Info}
                -> EvalFEnv -> Val
  sem mkEvalFApp =
  | r ->
    let lhs = mkEvalF r.lhs in
    let rhs = mkEvalF r.rhs in
    lam env. applyF (lhs env, rhs env)

  sem applyF : (Val, Val) -> Val
end

lang LamEvalF = AppEvalF + LamAst
  syn Expr =
  | VCls (Val -> Val)

  sem readback =
  | VCls _ -> None ()

  sem mkEvalF =
  | TmLam r ->
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      let body = mkEvalF r.body in
      lam env. VCls (lam val. body (Cons ((s, val), env)))
    else error "Unsymbolized TmLam in mkEvalF!"

  sem applyF =
  | (VCls cls, val) -> cls val
end

lang DeclEvalF = EvalF + DeclAst
  sem mkEvalF =
  | TmDecl r ->
    let inexpr = mkEvalF r.inexpr in
    let decl = mkEvalDeclF r.decl in
    lam env. inexpr (decl env)
end

lang ConstEvalF = AppEvalF + ConstAst + UnknownTypeAst
  sem readback =
  | VConst1 (c, _) | VConst2 (c, _) | VConst3 (c, _) -> Some(TmConst
    { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })

  sem mkEvalF =
  | TmConst r -> let val = mkDeltaF r.val in lam. val

  sem applyF =
  | (VConst1 (_, f), val) -> f val
  | (VConst2 (c, f), val) -> VConst1 (c, f val)
  | (VConst3 (c, f), val) -> VConst2 (c, f val)

  sem mkDeltaF =| _ -> error "Unsupported Const in mkDeltaF!"
end

lang MatchEvalF = EvalF + MatchAst
  sem mkEvalF =
  | TmMatch r ->
    let target = mkEvalF r.target in
    let thn = mkEvalF r.thn in
    let els = mkEvalF r.els in
    let tryMatch = mkTryMatch r.pat in
    lam env.
      match tryMatch (target env) env with Some env then thn env else els env

  sem mkTryMatch : Pat -> Val -> EvalFEnv -> Option EvalFEnv
  sem mkTryMatch =| _ -> error "Unsupported Pat in mkTryMatch!"
end

lang RecordEvalF = EvalF + RecordAst + UnknownTypeAst
  sem mkEvalF =
  | TmRecord r ->
    let bindings = mapMap mkEvalF r.bindings in
    lam env. TmRecord
      { bindings = mapMap (lam x. x env) bindings
      , ty = TyUnknown { info = NoInfo () }, info = NoInfo () }
  | TmRecordUpdate r ->
    let rec = mkEvalF r.rec in
    let key = r.key in
    let value = mkEvalF r.value in
    lam env.
      match rec env with TmRecord rec then
        TmRecord { rec with bindings = mapInsert key (value env) rec.bindings }
      else error "TmRecord type error in mkEvalF!"
end

lang SeqEvalF = EvalF + SeqAst + UnknownTypeAst
  sem mkEvalF =
  | TmSeq r ->
    let vals = map mkEvalF r.tms in
    lam env. TmSeq
      { tms = map (lam x. x env) vals
      , ty = TyUnknown { info = NoInfo () }, info = NoInfo () }
end

lang NeverEvalF = EvalF + NeverAst
  sem mkEvalF =
  | TmNever r ->
    lam. errorSingle [r.info]
         "Reached a never term, which should be impossible in a well-typed program."
end

lang LetEvalF = EvalF + LetDeclAst
  sem mkEvalDeclF =
  | DeclLet r ->
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      let body = mkEvalF r.body in
      lam env. Cons ((s, body env), env)
    else error "Unsymbolized DeclLet in mkEvalDeclF!"
end

lang RecLetsEval = EvalF + RecLetsDeclAst + LamEvalF
  sem mkEvalDeclF =
  | DeclRecLets r ->
    let ts =
      map
        (lam b.
          match b.body with TmLam r then
            match (nameGetSym b.ident, nameGetSym r.ident) with
              (Some s1, Some s2) then
              let s1 = sym2hash s1 in
              let s2 = sym2hash s2 in
              let body = mkEvalF r.body in
              (s1, lam env. lam val. body (Cons ((s2, val), env)))
            else error "Unsymbolized DeclRecLets in mkEvalDeclF!"
          else error "Right-hand side of recursive let must be a lambda")
        r.bindings in
    recursive let reclet = lam env.
      foldl
        (lam acc. lam t.
          match t with (s, cls) in
          Cons ((s, VCls (lam val. cls (reclet env) val)), acc))
        env ts
    in
    reclet
end

lang TypeEvalF = EvalF + TypeDeclAst
  sem mkEvalDeclF =
  | DeclType _ -> lam env. env
end

lang DataEvalF = EvalF + DataAst + DataDeclAst
  sem mkEvalF =
  | TmConApp r ->
    let body = mkEvalF r.body in
    lam env. TmConApp { r with body = body env }

  sem mkEvalDeclF =
  | DeclConDef _ -> lam env. env
end

---------------
-- CONSTANTS --
---------------

lang UnsafeCoerceEvalF = ConstEvalF + UnsafeCoerceAst
  sem mkDeltaF =
  | c & CUnsafeCoerce _ -> VConst1 (c, lam x. x)
end

lang IntEvalF = ConstEvalF + IntAst + UnknownTypeAst
  sem mkDeltaF =
  | c & CInt _ -> (TmConst { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang ArithIntEvalF = ConstEvalF + IntEvalF + ArithIntAst
  sem mkDeltaF =
  | c & CAddi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (addi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSubi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (subi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CMuli _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (muli x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CDivi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (divi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CModi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (modi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CNegi _ -> VConst1
    (c , lam x. match x with TmConst {val = CInt {val = x}} in TmConst { val = CInt { val = (negi x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang ShiftIntEvalF = ConstEvalF + IntEvalF + ShiftIntAst
  sem mkDeltaF =
  | c & CSlli _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (slli x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSrli _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (srli x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSrai _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CInt { val = (srai x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang BoolEvalF = ConstEvalF + BoolAst + UnknownTypeAst
  sem mkDeltaF =
  | c & CBool _ -> (TmConst { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang CmpIntEvalF =
  ConstEvalF +  IntEvalF + BoolEvalF + CmpIntAst

  sem mkDeltaF =
  | c & CEqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CBool { val = (eqi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CNeqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CBool { val = (neqi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CLti _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CBool { val = (lti x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CGti _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CBool { val = (gti x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CLeqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CBool { val = (leqi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CGeqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CInt {val = x}}, TmConst {val = CInt {val = y}}) in
      TmConst { val = CBool { val = (geqi x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang CharEvalF = ConstEvalF + CharAst + UnknownTypeAst
  sem mkDeltaF =
  | c & CChar _ -> (TmConst { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

-- lang IOEvalF = ConstEvalF + IOAst + SeqAst + RecordAst + UnknownTypeAst
--   sem mkDeltaF =
--   | (CPrint _, [TmSeq s]) ->
--     let s = _evalSeqOfCharsToString info s.tms in
--     print s;
--     uunit_
--   | (CPrintError _, [TmSeq s]) ->
--     let s = _evalSeqOfCharsToString info s.tms in
--     printError s;
--     uunit_
--   | (CDPrint _, [_]) -> uunit_
--   | (CFlushStdout _, [_]) ->
--     flushStdout ();
--     uunit_
--   | (CFlushStderr _, [_]) ->
--     flushStderr ();
--     uunit_
--   | (CReadLine _, [_]) ->
--     let s = readLine () in
--     TmSeq {tms = map char_ s, ty = tyunknown_, info = NoInfo ()}
-- end

lang CmpCharEvalF = ConstEvalF + CharEvalF + BoolEvalF + CmpCharAst
  sem mkDeltaF =
  | c & CEqc _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CChar {val = x}}, TmConst {val = CChar {val = y}}) in
      TmConst { val = CBool { val = (eqc x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang IntCharConversionEvalF =
  ConstEvalF + CharEvalF + IntEvalF + IntCharConversionAst

  sem mkDeltaF =
  | c & CInt2Char _ -> VConst1
    (c , lam x. match x with TmConst {val = CInt {val = x}} in TmConst { val = CChar { val = (int2char x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CChar2Int _ -> VConst1
    (c , lam x. match x with TmConst {val = CChar {val = x}} in TmConst { val = CInt { val = (char2int x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang FloatEvalF = ConstEvalF + FloatAst + UnknownTypeAst
  sem mkDeltaF =
  | c & CFloat _ -> TmConst { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }
end

lang ArithFloatEvalF = ConstEvalF + FloatEvalF + ArithFloatAst
  sem mkDeltaF =
  | c & CAddf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CFloat { val = (addf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSubf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CFloat { val = (subf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CMulf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CFloat { val = (mulf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CDivf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CFloat { val = (divf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CNegf _ -> VConst1
    (c , lam x. match x with TmConst {val = CFloat {val = x}} in TmConst { val = CFloat { val = (negf x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang CmpFloatEvalF = ConstEvalF + FloatEvalF + BoolEvalF + CmpFloatAst
  sem mkDeltaF =
  | c & CEqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CBool { val = (eqf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CNeqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CBool { val = (neqf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CLtf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CBool { val = (ltf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CGtf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CBool { val = (gtf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CLeqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CBool { val = (leqf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CGeqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (TmConst {val = CFloat {val = x}}, TmConst {val = CFloat {val = y}}) in
      TmConst { val = CBool { val = (geqf x y) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

lang FloatIntConversionEvalF =
  ConstEvalF + FloatEvalF + IntEvalF + FloatIntConversionAst

  sem mkDeltaF =
  | c & CFloorfi _ -> VConst1
    (c , lam x. match x with TmConst {val = CFloat {val = x}} in TmConst { val = CInt { val = (floorfi x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CCeilfi _ -> VConst1
    (c , lam x. match x with TmConst {val = CFloat {val = x}} in TmConst { val = CInt { val = (ceilfi x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CRoundfi _ -> VConst1
    (c , lam x. match x with TmConst {val = CFloat {val = x}} in TmConst { val = CInt { val = (roundfi x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CInt2float _ -> VConst1
    (c , lam x. match x with TmConst {val = CInt {val = x}} in TmConst { val = CFloat { val = (int2float x) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
end

----------------------------
-- SEQUENCE OPERATIONS --
----------------------------

lang SeqOpEvalF =
  ConstEvalF + SeqEvalF + IntEvalF + BoolEvalF + RecordEvalF + SeqOpAst

  sem mkDeltaF =
  -- First order
  | c & CHead _ -> VConst1
    (c , lam s. match s with TmSeq {tms = s} in head s)
  | c & CTail _ -> VConst1
    (c , lam s. match s with TmSeq {tms = s} in TmSeq { tms = (tail s), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CNull _ -> VConst1
    (c , lam s. match s with TmSeq {tms = s} in TmConst { val = CBool { val = (null s) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CLength _ -> VConst1
    (c , lam s. match s with TmSeq {tms = s} in TmConst { val = CInt { val = (length s) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CReverse _ -> VConst1
    (c , lam s. match s with TmSeq {tms = s} in TmSeq { tms = (reverse s), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CIsList _ -> VConst1
    (c , lam s. match s with TmSeq {tms = s} in TmConst { val = CBool { val = (isList s) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CIsRope _ -> VConst1
    (c , lam s. match s with TmSeq {tms = s} in TmConst { val = CBool { val = (isRope s) }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CGet _ -> VConst2
    (c , lam s. lam i. match (s, i) with (TmSeq {tms = s}, TmConst {val = CInt {val = i}}) in get s i)
  | c & CCons _ -> VConst2
    (c , lam v. lam s. match s with TmSeq {tms = s} in TmSeq { tms = (cons v s), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSnoc _ -> VConst2
    (c , lam s. lam v. match s with TmSeq {tms = s} in TmSeq { tms = (snoc s v), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CConcat _ -> VConst2
    (c , lam s1. lam s2.
      match (s1, s2) with (TmSeq {tms = s1}, TmSeq {tms = s2}) in TmSeq { tms = (concat s1 s2), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSplitAt _ -> VConst2
    (c , lam s. lam i.
      match (s, i) with (TmSeq {tms = s}, TmConst {val = CInt {val = i}}) in
      match splitAt s i with (l, r) in
      TmRecord { bindings = (mapFromSeq cmpSID
          [(stringToSid "0", TmSeq { tms = l, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }), (stringToSid "1", TmSeq { tms = r, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })]), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSet _ -> VConst3
    (c , lam s. lam i. lam v.
      match (s, i) with (TmSeq {tms = s}, TmConst {val = CInt {val = i}}) in TmSeq { tms = (set s i v), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CSubsequence _ -> VConst3
    (c , lam s. lam o. lam n.
      match (s, o, n) with (TmSeq {tms = s}, TmConst {val = CInt {val = o}}, TmConst {val = CInt {val = n}}) in
      TmSeq { tms = (subsequence s o n), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })

  -- Higher order
  | c & CMap _ -> VConst2
    (c , lam f. lam s.
      match s with TmSeq {tms = s} in TmSeq { tms = (map (lam x. applyF (f, x)) s), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CMapi _ -> VConst2
    (c , lam f. lam s.
      match s with TmSeq {tms = s} in
      TmSeq { tms = (mapi (lam i. lam x. applyF (applyF (f, TmConst { val = CInt { val = i }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }), x)) s), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CIter _ -> VConst2
    (c , lam f. lam s.
      match s with TmSeq {tms = s} in
      iter (lam x. applyF (f, x); ()) s;
      TmRecord { bindings = (mapEmpty cmpSID), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CIteri _ -> VConst2
    (c , lam f. lam s.
      match s with TmSeq {tms = s} in
      iteri (lam i. lam x. applyF (applyF (f, TmConst { val = CInt { val = i }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }), x); ()) s;
      TmRecord { bindings = (mapEmpty cmpSID), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CCreate _ -> VConst2
    (c , lam n. lam f.
      match n with TmConst {val = CInt {val = n}} in TmSeq { tms = (create n (lam i. applyF (f, TmConst { val = CInt { val = i }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }))), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CCreateList _ -> VConst2
    (c , lam n. lam f.
      match n with TmConst {val = CInt {val = n}} in TmSeq { tms = (createList n (lam i. applyF (f, TmConst { val = CInt { val = i }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }))), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CCreateRope _ -> VConst2
    (c , lam n. lam f.
      match n with TmConst {val = CInt {val = n}} in TmSeq { tms = (createRope n (lam i. applyF (f, TmConst { val = CInt { val = i }, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }))), ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
  | c & CFoldl _ -> VConst3
    (c , lam f. lam acc. lam s.
      match s with TmSeq {tms = s} in
      foldl (lam acc. lam x. applyF (applyF (f, acc), x)) acc s)
  | c & CFoldr _ -> VConst3
    (c , lam f. lam acc. lam s.
      match s with TmSeq {tms = s} in
      foldr (lam x. lam acc. applyF (applyF (f, x), acc)) acc s)
end

lang SysEvalF = ConstEvalF + IntEvalF + SysAst
  sem mkDeltaF =
  | c & CExit _ -> VConst1 (c, lam x. match x with TmConst {val = CInt {val = x}} in exit x)
end

--------------
-- PATTERNS --
--------------

lang NamedPatEvalF = MatchEvalF + NamedPat
  sem mkTryMatch =
  | PatNamed {ident = PName name} ->
    match nameGetSym name with Some s then
      let s = sym2hash s in
      lam val. lam env. Some (Cons ((s, val), env))
    else error "Unsymbolized PatNamed in mkTryMatch!"
  | PatNamed {ident = PWildcard ()} -> lam. lam env. Some env
end

lang BoolPatEval = MatchEvalF + BoolEvalF + BoolAst + BoolPat
  sem mkTryMatch =
  | PatBool r -> lam val. lam env.
    match val with TmConst {val = CBool {val = b}} then
      match (b, r.val) with (true, true) | (false, false) then Some env
      else None ()
    else None ()
end

lang RecordPatEval = MatchEvalF + RecordEvalF + RecordAst + RecordPat
  sem mkTryMatch =
  | PatRecord r ->
    let pbindings = mapMap mkTryMatch r.bindings in
    lam val. lam env.
      match val with TmRecord {bindings = rbindings} then
        mapFoldlOption
          (lam env. lam k. lam pat.
            match mapLookup k rbindings with Some val then pat val env
            else None ())
          env
          pbindings
      else None ()
end

lang SeqTotPatEvalF = MatchEvalF + SeqEvalF + SeqTotPat
  sem mkTryMatch =
  | PatSeqTot r ->
    let pats = map mkTryMatch r.pats in
    let n = length pats in
    lam val. lam env.
      match val with TmSeq {tms = vals} then
        if eqi (length vals) n then
          optionFoldlM
            (lam env. lam pv. match pv with (pat, v) in pat v env)
            env
            (zipWith (lam pat. lam v. (pat, v)) pats vals)
        else None ()
      else None ()
end

lang SeqEdgePatEvalF = MatchEvalF + SeqEvalF + SeqEdgePat
  sem mkTryMatch =
  | PatSeqEdge r ->
    let pats = map mkTryMatch (concat r.prefix r.postfix) in
    let npre = length r.prefix in
    let npost = length r.postfix in
    let nfix = addi npre npost in
    -- The middle binds the remaining subsequence, or is dropped for `_`.
    let middle =
      match r.middle with PName name then
        match nameGetSym name with Some s then
          let s = sym2hash s in
          lam vals. lam env.
            Some (Cons ((s, TmSeq { tms = vals, ty = TyUnknown { info = NoInfo () }, info = NoInfo () }), env))
        else error "Unsymbolized PatSeqEdge in mkTryMatch!"
      else lam. lam env. Some env
    in
    lam val. lam env.
      match val with TmSeq {tms = vals} then
        if geqi (length vals) nfix then
          match splitAt vals npre with (pre, rest) in
          match splitAt rest (subi (length rest) npost) with (mid, post) in
          match
            optionFoldlM
              (lam env. lam pv. match pv with (pat, v) in pat v env)
              env
              (zipWith (lam pat. lam v. (pat, v)) pats (concat pre post))
          with Some env then middle mid env
          else None ()
        else None ()
      else None ()
end

lang IntPatEvalF = MatchEvalF + IntEvalF + IntPat
  sem mkTryMatch =
  | PatInt r -> lam val. lam env.
    match val with TmConst {val = CInt {val = i}} then
      if eqi i r.val then Some env else None ()
    else None ()
end

lang CharPatEvalF = MatchEvalF + CharEvalF + CharPat
  sem mkTryMatch =
  | PatChar r -> lam val. lam env.
    match val with TmConst {val = CChar {val = c}} then
      if eqc c r.val then Some env else None ()
    else None ()
end

------------------
-- COMPOSITIONS --
------------------

lang MExprEvalF =
  -- Terms and Decls
  VarEvalF + AppEvalF + LamEvalF + DeclEvalF + ConstEvalF + MatchEvalF +
  RecordEvalF + SeqEvalF + NeverEvalF + DataEvalF +

  -- Decls
  LetEvalF + RecLetsEval + TypeEvalF +

  -- Constants
  UnsafeCoerceEvalF + IntEvalF + ArithIntEvalF + ShiftIntEvalF +  BoolEvalF +
  CmpIntEvalF + CharEvalF + CmpCharEvalF + IntCharConversionEvalF +
  FloatEvalF + ArithFloatEvalF + CmpFloatEvalF +
  FloatIntConversionEvalF + SeqOpEvalF + SysEvalF +

  -- Patterns
  NamedPatEvalF + BoolPatEval + RecordPatEval + SeqTotPatEvalF +
  SeqEdgePatEvalF + IntPatEvalF + CharPatEvalF
end

------------
-- RUNNER --
------------

-- Parses, symbolizes and type checks the file named on the command line
-- exactly the way `mi eval` does, then evaluates it with the evaluator above.
-- Build with `mi compile <this file> --output <name>`, run as `<name> FILE.mc`.

lang RunnerF = MExprEvalF + BootParser + MExprSym + MExprTypeCheck
end

mexpr

use RunnerF in

match argv with [_, file] ++ _ then
  let ast =
    parseMCoreFile
      { defaultBootParserParseMCoreFileArg with keepUtests = false }
      file in
  let ast = symbolize ast in
  let ast = removeMetaVarExpr (typeCheckExpr typcheckEnvDefault ast) in
  let eval = mkEvalF ast in eval (Nil ());
  ()
else
  printLn "usage: <runner> FILE.mc";
  exit 1
