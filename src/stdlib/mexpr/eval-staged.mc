/- This file implements a staged interpreter for MExpr -/

include "basic-types.mc"
include "common.mc"
include "error.mc"
include "info.mc"
include "int.mc"
include "list.mc"
include "map.mc"
include "name.mc"
include "option.mc"
include "seq.mc"
include "string.mc"
include "stringid.mc"
include "utest.mc"

include "mexpr/ast-builder.mc"
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"

---------------
-- CALLSTACK --
---------------

-- Implements a callstack backed by a ringbuffer with O(1) pop and push.
type Callstack = { _ringbuffer : Tensor[Info]
                 , _idx : Int
                 , _len : Int
                 , _cap : Int
                 }

let callstackInit : Int -> Option Callstack
= lam n.
    if gti n 0 then
      Some { _ringbuffer = tensorCreateDense [n] (lam. NoInfo ())
           , _idx = 0
           , _len = 0
           , _cap = n
           }
    else None ()

let callstackPush : Info -> Callstack -> Callstack
= lam info. lam cs.
    tensorLinearSetExn cs._ringbuffer cs._idx info;
    { cs with _idx = modi (addi cs._idx 1) cs._cap
    , _len = addi cs._len 1
    }

let callstackPop : Callstack -> Option (Callstack, Info)
= lam cs.
    if gti cs._len 0 then
      let i = if eqi cs._idx 0 then subi cs._cap 1 else subi cs._idx 1 in
      let info = tensorLinearGetExn cs._ringbuffer i in
      Some ( { cs with _idx = i
             , _len = subi cs._len 1
             }
           , info )
    else None ()

let callstackToSeq : Callstack -> [Info]
= lam cs.
    recursive let recur = lam acc. lam cs.
      match callstackPop cs with Some (cs, info) then recur (snoc acc info) cs
      else acc
    in recur [] cs

let callstackPrintTrace : Callstack -> ()
= lam cs.
    recursive let recur = lam remaining. lam cs.
      if leqi remaining 0 then ()
      else
        match callstackPop cs with Some (cs, info) then
          printLn (concat "TRACE: " (info2str info));
          recur (subi remaining 1) cs
        else ()
    in
    recur (mini cs._cap cs._len) cs

-------------------
-- BASE FRAGMENT --
-------------------

lang EvalS = Ast
  -- Values our terms can take.
  syn Val =

  -- Rebuilds a term from a value, if possible.
  sem evalSReadback : Val -> Option Expr

  -- The evaluation environment.
  type EvalSEnv = List (Int, Val)

  -- Looks up symbol hashes in the evaluation environment, gives an error if the
  -- lookup fails.
  sem evalSEnvLookup : Int -> EvalSEnv -> Val
  sem evalSEnvLookup s1 =
  | Nil _ -> error "env lookup failed!"
  | Cons ((s2, val), env) -> if eqi s1 s2 then val else evalSEnvLookup s1 env

  -- Stages a term for evaluation. Passing a callstack reference will make the
  -- evaluation function record the call stack which degrades performance.
  sem evalSStageExpr : (Option (Ref Callstack)) -> Expr -> EvalSEnv -> Val

  -- Stages declarations, see `evalSStageExpr`.
  sem evalSStageDecl : (Option (Ref Callstack)) -> Decl -> EvalSEnv -> EvalSEnv
end

---------------------
-- TERMS AND DECLS --
---------------------

let _sid_0 = stringToSid "0"
let _sid_1 = stringToSid "1"
let _sid_2 = stringToSid "2"
let _sid_3 = stringToSid "3"
let _sid_4 = stringToSid "4"
let _sid_5 = stringToSid "5"

lang VarEvalF = EvalS + VarAst
  sem evalSStageExpr cs +=
  | TmVar r ->
    match nameGetSym r.ident with Some s1 then
      evalSEnvLookup (sym2hash s1)
    else errorSingle [r.info] "Unsymbolized TmVarin evalSStageExpr!"
end

lang AppEvalS = EvalS + AppAst + ConstAst + UnknownTypeAst
  syn Val +=
  | VConst1 (Const, Val -> Val)
  | VConst2 (Const, Val -> Val -> Val)
  | VConst3 (Const, Val -> Val -> Val -> Val)
  -- NOTE(oerikss, 2026-09-29): To build a callstack we need to pass info fields
  -- to higher-order constant functions.
  | VConstInfo1 (Const, Info -> Val -> Val)
  | VConstInfo2 (Const, Info -> Val -> Val -> Val)
  | VConstInfo3 (Const, Info -> Val -> Val -> Val -> Val)

  sem stageDeltaF : (Option (Ref Callstack)) -> Const -> Val

  sem evalSStageExpr cs +=
  | TmApp r ->
    -- A constant applied to exactly as many arguments as it takes: resolve the
    -- delta function once, while compiling, and emit a closure that calls it
    -- directly.  The general path would instead build a VConst2/VConst1 chain
    -- and take it apart again on every single evaluation.  The three shapes
    -- are disjoint, since each looks through a different number of TmApp
    -- layers before expecting a TmConst, and a constant used as a value still
    -- falls through to `stageApp`.
    switch r
    case {lhs = TmApp {lhs = TmApp {lhs = TmConst c, rhs = a}, rhs = b}, rhs = d}
    then
      let val = stageDeltaF cs c.val in
      switch val
      case VConst3 (_, f) then
        let a = evalSStageExpr cs a in
        let b = evalSStageExpr cs b in
        let d = evalSStageExpr cs d in
        lam env. f (a env) (b env) (d env)
      case VConstInfo3 (_, f) then
        let a = evalSStageExpr cs a in
        let b = evalSStageExpr cs b in
        let d = evalSStageExpr cs d in
        lam env. f r.info (a env) (b env) (d env)
      case _ then
        let a = evalSStageExpr cs a in
        let b = evalSStageExpr cs b in
        let d = evalSStageExpr cs d in
        lam env.
          applyS
            (r.info, applyS (r.info, applyS (r.info, val, a env), b env), d env)
      end
    case {lhs = TmApp {lhs = TmConst c, rhs = a}, rhs = b} then
      let val = stageDeltaF cs c.val in
      switch val
      case VConst2 (_, f) then
        let a = evalSStageExpr cs a in
        let b = evalSStageExpr cs b in
        lam env. f (a env) (b env)
      case VConstInfo2 (_, f) then
        let a = evalSStageExpr cs a in
        let b = evalSStageExpr cs b in
        lam env. f r.info (a env) (b env)
      case _ then
        let a = evalSStageExpr cs a in
        let b = evalSStageExpr cs b in
        lam env. applyS (r.info, applyS (r.info, val, a env), b env)
      end
    case {lhs = TmConst c, rhs = a} then
      let val = stageDeltaF cs c.val in
      switch val
      case VConst1 (_, f) then
        let a = evalSStageExpr cs a in
        lam env. f (a env)
      case VConstInfo1 (_, f) then
        let a = evalSStageExpr cs a in
        lam env. f r.info (a env)
      case _ then
        let a = evalSStageExpr cs a in
        lam env. applyS (r.info, val, a env)
      end
    case _ then stageApp cs r
    end

  sem stageApp : (Option (Ref Callstack))
               -> {lhs : Expr, rhs : Expr, ty : Type, info : Info}
               -> EvalSEnv -> Val
  sem stageApp cs =
  | r ->
    let lhs = evalSStageExpr cs r.lhs in
    let rhs = evalSStageExpr cs r.rhs in
    let info = r.info in
    lam env. applyS (info, lhs env, rhs env)

  sem applyS : (Info, Val, Val) -> Val
  sem applyS =
  | (_, VConst1 (_, f), val) -> f val
  | (_, VConst2 (c, f), val) -> VConst1 (c, f val)
  | (_, VConst3 (c, f), val) -> VConst2 (c, f val)
  -- NOTE(oerikss, 2026-09-29): It only makes sense to pass the info field when
  -- the constant function is fully applied since that is when its function
  -- arguments are applied.
  | (info, VConstInfo1 (_, f), val) -> f info val
  | (_, VConstInfo2 (c, f), val) ->
    VConstInfo1 (c, lam info. lam y. f info val y)
  | (_, VConstInfo3 (c, f), val) ->
    VConstInfo2 (c, lam info. lam y. lam z. f info val y z)
end

lang LamEvalS = AppEvalS + LamAst
  syn Val +=
  | VCls (Val -> Val)
  | VClsInfo (Info -> Val -> Val)

  sem evalSReadback +=
  | VCls _ | VClsInfo _ -> None ()

  sem evalSStageExpr cs +=
  | TmLam r ->
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      let body = evalSStageExpr cs r.body in
      switch cs
      case None _ then
        lam env. VCls (lam val. body (Cons ((s, val), env)))
      case Some csr then
        lam env. clsUsingCallstack csr (lam val. body (Cons ((s, val), env)))
      end
    else errorSingle [r.info] "Unsymbolized TmLam in evalSStageExpr!"

  sem clsUsingCallstack : (Ref Callstack) -> (Val -> Val) -> Val
  sem clsUsingCallstack csr =| cls ->
    let cls = lam info. lam val.
      modref csr (callstackPush info (deref csr));
      let val = cls val in
      (match callstackPop (deref csr) with Some (cs, _) then modref csr cs
       else ());
      val in
    VClsInfo cls

  sem applyS +=
  | (_, VCls cls, val) -> cls val
  | (info, VClsInfo cls, val) -> cls info val
end

lang DeclEvalS = EvalS + DeclAst
  sem evalSStageExpr cs +=
  | TmDecl r ->
    let inexpr = evalSStageExpr cs r.inexpr in
    let decl = evalSStageDecl cs r.decl in
    lam env. inexpr (decl env)
end

lang ConstEvalS = AppEvalS + ConstAst + UnknownTypeAst
  sem evalSReadback +=
  | VConst1 (c, _) | VConst2 (c, _) | VConst3 (c, _)
  | VConstInfo1 (c, _) | VConstInfo2 (c, _) | VConstInfo3 (c, _) ->
    Some(TmConst
      { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })

  sem evalSStageExpr cs +=
  | TmConst r -> let val = stageDeltaF cs r.val in lam. val
end

lang MatchEvalS = EvalS
  sem stageTryMatch : Pat -> Val -> EvalSEnv -> Option EvalSEnv
end

lang MatchEvalS = MatchEvalS + MatchAst
  sem evalSStageExpr cs +=
  | TmMatch r ->
    let target = evalSStageExpr cs r.target in
    let thn = evalSStageExpr cs r.thn in
    let els = evalSStageExpr cs r.els in
    let tryMatch = stageTryMatch r.pat in
    lam env.
      match tryMatch (target env) env with Some env then thn env else els env
end

lang RecordEvalS = EvalS + RecordAst + UnknownTypeAst
  syn Val +=
  | VRecord (Map SID Val)

  sem evalSReadback +=
  | VRecord bindings ->
    optionMap
      (lam bindings.
        TmRecord { bindings = bindings
                 , ty = TyUnknown { info = NoInfo () }
                 , info = NoInfo ()
                 })
      (mapFoldlOption
        (lam acc. lam k. lam v.
          match evalSReadback v with Some e then Some (mapInsert k e acc)
          else None ())
        (mapEmpty cmpSID)
        bindings)

  sem evalSStageExpr cs +=
  | TmRecord r ->
    let bindings = mapMap (evalSStageExpr cs) r.bindings in
    lam env. VRecord (mapMap (lam x. x env) bindings)
  | TmRecordUpdate r ->
    let rec = evalSStageExpr cs r.rec in
    let key = r.key in
    let value = evalSStageExpr cs r.value in
    lam env.
      match rec env with VRecord rec then VRecord (mapInsert key (value env) rec)
      else error "TmRecord type error in evalSStageExpr!"
end

let unitVal = use RecordEvalS in VRecord (mapEmpty cmpSID)

lang SeqEvalS = EvalS + SeqAst + UnknownTypeAst
  syn Val +=
  | VSeq [Val]

  sem evalSReadback +=
  | VSeq vals ->
    optionMap
      (lam tms.
        TmSeq { tms = tms
              , ty = TyUnknown { info = NoInfo () }
              , info = NoInfo ()
              })
      (optionMapM evalSReadback vals)

  sem evalSStageExpr cs +=
  | TmSeq r ->
    let vals = map (evalSStageExpr cs) r.tms in
    lam env. VSeq (map (lam x. x env) vals)
end

lang NeverEvalS = EvalS + NeverAst
  sem evalSStageExpr cs +=
  | TmNever r ->
    let err = lam.
      errorSingle [r.info]
        "Reached a never term, which should be impossible in a well-typed program." in
    switch cs
    case None _ then lam. err ()
    case Some cs then
      lam.
        callstackPrintTrace (deref cs);
        print "\n";
        err ()
    end
end

let nameGetSymOrGetFreshSym = lam n.
  match nameGetSym n with Some s then s else gensym ()

lang LetEvalS = EvalS + LetDeclAst
  sem evalSStageDecl cs +=
  | DeclLet r ->
    -- NOTE(oerikss, 2026-09-16): We assume here that unsymbolized let bindings
    -- are not referred to en the rest of the code. This can appear for example
    -- in generated code that involves sequencing of expressions.
    let s = sym2hash (nameGetSymOrGetFreshSym r.ident) in
    let body = evalSStageExpr cs r.body in
    lam env. Cons ((s, body env), env)
end

lang RecLetsEvalS = EvalS + RecLetsDeclAst + LamEvalS
  sem evalSStageDecl cs +=
  | DeclRecLets r ->
    let ts = foldl
      (lam acc. lam b.
        match b.body with TmLam r then
          -- NOTE(oerikss, 2026-09-16): We assume here that unsymbolized let
          -- bindings are not referred to en the rest of the code.
          let s1 = sym2hash (nameGetSymOrGetFreshSym b.ident) in
          let s2 = sym2hash (nameGetSymOrGetFreshSym r.ident) in
          let body = evalSStageExpr cs r.body in
          Cons ((s1, lam env. lam val. body (Cons ((s2, val), env))), acc)
        else
          errorSingle [infoTm b.body]
            "Right-hand side of recursive let must be a lambda")
      (Nil ())
      r.bindings in
    let ts = listReverse ts in
    let errMsg = lam.
      concat "recursive env in DeclRecLets at " (info2str r.info) in
    -- OPT(oerikss, 2026-09-29): Dispach on the presence of a callstack here
    -- rather than inside the returned closure. This means a bit of code
    -- duplication.
    switch cs
    case None _ then
      lam env.
        -- OPT(oerikss, 2026-09-29): Lazily populate the recursive environment,
        -- which is safe since our recursive closures does not look at it until
        -- they are applied.
        let recEnv = ref (lam. error (errMsg ())) in
        let env = listFoldl
          (lam acc. lam t.
             match t with (s, cls) in
             Cons ((s, VCls (lam val. cls (deref recEnv ()) val)), acc))
          env ts in
        modref recEnv (lam. env); env
    case Some cs then
      lam env.
        let recEnv = ref (lam. error (errMsg ())) in
        let env = listFoldl
          (lam acc. lam t.
             match t with (s, cls) in
             Cons ( (s, clsUsingCallstack cs (lam val. cls (deref recEnv ()) val))
                  , acc ))
          env ts in
        modref recEnv (lam. env); env
    end

end

lang TypeEvalS = EvalS + TypeDeclAst
  sem evalSStageDecl cs +=
  | DeclType _ -> lam env. env
end

lang DataEvalS = EvalS + DataAst + DataDeclAst
  syn Val +=
  | VConApp (Int, Val)

  sem evalSStageExpr cs +=
  | TmConApp r ->
    let body = evalSStageExpr cs r.body in
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      lam env. VConApp (s, body env)
    else errorSingle [r.info] "Unsymbolized TmConApp in evalSStageExpr!"

  sem evalSStageDecl cs +=
  | DeclConDef _ -> lam env. env
end

lang UtestEvalS = EvalS + UtestDeclAst
  sem evalSStageDecl cs +=
  | DeclUtest r ->
    warnSingle [r.info] "Skipping evaluation of utest";
    lam env. env
end

lang ExtEvalS = EvalS + ExtDeclAst
  sem evalSStageDecl cs +=
  | DeclExt r ->
    warnSingle [r.info]
      (concat "Skipping external declaration for: " (nameGetStr r.ident));
    lam env. env
end

lang PlaceholderEvalS = EvalS + PlaceholderAst + UnknownTypeAst
  syn Val +=
  | VPlaceholder {}

  sem evalSReadback +=
  | VPlaceholder _ -> Some
    (TmPlaceholder { ty = TyUnknown { info = NoInfo () }, info = NoInfo () })

  sem evalSStageExpr cs +=
  | TmPlaceholder _ -> lam env. VPlaceholder {}
end

lang OpaqueEvalS = EvalS + OpaqueAst
  sem evalSStageExpr cs +=
  | TmOpaque r -> evalSStageExpr cs r.body
end

---------------
-- CONSTANTS --
---------------

lang UnsafeCoerceEvalS = ConstEvalS + UnsafeCoerceAst
  sem stageDeltaF cs +=
  | c & CUnsafeCoerce _ -> VConst1 (c, lam x. x)
end

lang IntEvalS = ConstEvalS + IntAst + UnknownTypeAst
  syn Val +=
  | VInt Int

  sem evalSReadback +=
  | VInt n -> Some ( TmConst
    { val = CInt { val = n }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem stageDeltaF cs +=
  | CInt r -> VInt r.val
end

lang ArithIntEvalS = ConstEvalS + IntEvalS + ArithIntAst
  sem stageDeltaF cs +=
  | c & CAddi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (addi x y))
  | c & CSubi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (subi x y))
  | c & CMuli _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (muli x y))
  | c & CDivi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (divi x y))
  | c & CModi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (modi x y))
  | c & CNegi _ -> VConst1
    (c, lam x. match x with VInt x in VInt (negi x))
end

lang ShiftIntEvalS = ConstEvalS + IntEvalS + ShiftIntAst
  sem stageDeltaF cs +=
  | c & CSlli _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (slli x y))
  | c & CSrli _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (srli x y))
  | c & CSrai _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (srai x y))
end

lang BoolEvalS = ConstEvalS + BoolAst + UnknownTypeAst
  syn Val +=
  | VBool Bool

  sem evalSReadback +=
  | VBool b -> Some( TmConst
    { val = CBool { val = b }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem stageDeltaF cs +=
  | CBool r -> VBool r.val
end

lang CmpIntEvalS =
  ConstEvalS +  IntEvalS + BoolEvalS + CmpIntAst

  sem stageDeltaF cs +=
  | c & CEqi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (eqi x y))
  | c & CNeqi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (neqi x y))
  | c & CLti _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (lti x y))
  | c & CGti _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (gti x y))
  | c & CLeqi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (leqi x y))
  | c & CGeqi _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (geqi x y))
end

lang CharEvalS = ConstEvalS + CharAst + UnknownTypeAst
  syn Val +=
  | VChar Char

  sem evalSReadback +=
  | VChar c -> Some( TmConst
    { val = CChar { val = c }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem stageDeltaF cs +=
  | CChar r -> VChar r.val
end

lang CmpCharEvalS = ConstEvalS + CharEvalS + BoolEvalS + CmpCharAst
  sem stageDeltaF cs +=
  | c & CEqc _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VChar x, VChar y) in VBool (eqc x y))
end

lang IntCharConversionEvalS =
  ConstEvalS + CharEvalS + IntEvalS + IntCharConversionAst

  sem stageDeltaF cs +=
  | c & CInt2Char _ -> VConst1
    (c, lam x. match x with VInt x in VChar (int2char x))
  | c & CChar2Int _ -> VConst1
    (c, lam x. match x with VChar x in VInt (char2int x))
end

lang FloatEvalS = ConstEvalS + FloatAst + UnknownTypeAst
  syn Val +=
  | VFloat Float

  sem evalSReadback +=
  | VFloat f -> Some ( TmConst
    { val = CFloat { val = f }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem stageDeltaF cs +=
  | CFloat r -> VFloat r.val
end

lang ArithFloatEvalS = ConstEvalS + FloatEvalS + ArithFloatAst
  sem stageDeltaF cs +=
  | c & CAddf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (addf x y))
  | c & CSubf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (subf x y))
  | c & CMulf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (mulf x y))
  | c & CDivf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (divf x y))
  | c & CNegf _ -> VConst1
    (c, lam x. match x with VFloat x in VFloat (negf x))
end

lang CmpFloatEvalS = ConstEvalS + FloatEvalS + BoolEvalS + CmpFloatAst
  sem stageDeltaF cs +=
  | c & CEqf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (eqf x y))
  | c & CNeqf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (neqf x y))
  | c & CLtf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (ltf x y))
  | c & CGtf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (gtf x y))
  | c & CLeqf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (leqf x y))
  | c & CGeqf _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (geqf x y))
end

lang FloatIntConversionEvalS =
  ConstEvalS + FloatEvalS + IntEvalS + FloatIntConversionAst

  sem stageDeltaF cs +=
  | c & CFloorfi _ -> VConst1
    (c, lam x. match x with VFloat x in VInt (floorfi x))
  | c & CCeilfi _ -> VConst1
    (c, lam x. match x with VFloat x in VInt (ceilfi x))
  | c & CRoundfi _ -> VConst1
    (c, lam x. match x with VFloat x in VInt (roundfi x))
  | c & CInt2float _ -> VConst1
    (c, lam x. match x with VInt x in VFloat (int2float x))
end

-------------------------
-- SEQUENCE OPERATIONS --
-------------------------

lang SeqOpEvalS =
  ConstEvalS + SeqEvalS + IntEvalS + BoolEvalS + RecordEvalS + SeqOpAst

  sem stageDeltaF cs +=
  -- First order
  | c & CHead _ -> VConst1
    (c, lam s. match s with VSeq s in head s)
  | c & CTail _ -> VConst1
    (c, lam s. match s with VSeq s in VSeq (tail s))
  | c & CNull _ -> VConst1
    (c, lam s. match s with VSeq s in VBool (null s))
  | c & CLength _ -> VConst1
    (c, lam s. match s with VSeq s in VInt (length s))
  | c & CReverse _ -> VConst1
    (c, lam s. match s with VSeq s in VSeq (reverse s))
  | c & CIsList _ -> VConst1
    (c, lam s. match s with VSeq s in VBool (isList s))
  | c & CIsRope _ -> VConst1
    (c, lam s. match s with VSeq s in VBool (isRope s))
  | c & CGet _ -> VConst2
    (c, lam s. lam i. match (s, i) with (VSeq s, VInt i) in get s i)
  | c & CCons _ -> VConst2
    (c, lam v. lam s. match s with VSeq s in VSeq (cons v s))
  | c & CSnoc _ -> VConst2
    (c, lam s. lam v. match s with VSeq s in VSeq (snoc s v))
  | c & CConcat _ -> VConst2
    (c, lam s1. lam s2.
      match (s1, s2) with (VSeq s1, VSeq s2) in VSeq (concat s1 s2))
  | c & CSplitAt _ -> VConst2
    (c, lam s. lam i.
      match (s, i) with (VSeq s, VInt i) in
      match splitAt s i with (l, r) in
      VRecord
        (mapFromSeq cmpSID
          [(_sid_0, VSeq l), (_sid_1, VSeq r)]))
  | c & CSet _ -> VConst3
    (c, lam s. lam i. lam v.
      match (s, i) with (VSeq s, VInt i) in VSeq (set s i v))
  | c & CSubsequence _ -> VConst3
    (c, lam s. lam o. lam n.
      match (s, o, n) with (VSeq s, VInt o, VInt n) in
      VSeq (subsequence s o n))

  -- Higher order
  | c & CMap _ -> VConstInfo2
    (c, lam info. lam f. lam s.
      match s with VSeq s in
      VSeq (map (lam x. applyS (info, f, x)) s))
  | c & CMapi _ -> VConstInfo2
    (c, lam info. lam f. lam s.
      match s with VSeq s in
      VSeq
        (mapi (lam i. lam x. applyS (info, applyS (info, f, VInt i), x)) s))
  | c & CIter _ -> VConstInfo2
    (c, lam info. lam f. lam s.
      match s with VSeq s in
      iter (lam x. applyS (info, f, x); ()) s;
      unitVal)
  | c & CIteri _ -> VConstInfo2
    (c, lam info. lam f. lam s.
      match s with VSeq s in
      iteri
        (lam i. lam x. applyS (info, applyS (info, f, VInt i), x); ())
        s;
      unitVal)
  | c & CCreate _ -> VConstInfo2
    (c, lam info. lam n. lam f.
      match n with VInt n in
      VSeq (create n (lam i. applyS (info, f, VInt i))))
  | c & CCreateList _ -> VConstInfo2
    (c, lam info. lam n. lam f.
      match n with VInt n in
      VSeq (createList n (lam i. applyS (info, f, VInt i))))
  | c & CCreateRope _ -> VConstInfo2
    (c, lam info. lam n. lam f.
      match n with VInt n in
      VSeq (createRope n (lam i. applyS (info, f, VInt i))))
  | c & CFoldl _ -> VConstInfo3
    (c, lam info. lam f. lam acc. lam s.
      match s with VSeq s in
      foldl (lam acc. lam x. applyS (info, applyS (info, f, acc), x)) acc s)
  | c & CFoldr _ -> VConstInfo3
    (c, lam info. lam f. lam acc. lam s.
      match s with VSeq s in
      foldr (lam x. lam acc. applyS (info, applyS (info, f, x), acc)) acc s)
end

lang StringConvEvalS = SeqEvalS + CharEvalS
  sem valToString : Val -> String
  sem valToString =
  | VSeq vals -> map (lam v. match v with VChar c in c) vals

  sem stringToVal : String -> Val
  sem stringToVal =
  | s -> VSeq (map (lam c. VChar c) s)
end

lang SysEvalS = ConstEvalS + IntEvalS + StringConvEvalS + SysAst
  sem stageDeltaF cs +=
  | c & CExit _ -> VConst1 (c, lam x. match x with VInt x in exit x)
  | c & CError _ ->
    switch cs
    case None _ then VConst1 (c, lam s. error (valToString s))
    case Some cs then
      VConst1 (c, lam s.
        callstackPrintTrace (deref cs);
        print "\n";
        error (valToString s))
    end
  | CArgv _ -> VSeq (map stringToVal argv)
  | c & CCommand _ -> VConst1 (c, lam s. VInt (command (valToString s)))
  | c & CExec _ -> VConst2
    (c, lam p. lam args.
      match args with VSeq args in
      exec (valToString p) (map valToString args))
end

lang SymbEvalS = ConstEvalS + IntEvalS + SymbAst
  sem stageDeltaF cs +=
  | c & CGensym _ -> VConst1 (c, lam. VInt (sym2hash (gensym ())))
  | c & CSym2hash _ -> VConst1 (c, lam x. match x with VInt _ in x)
end

lang CmpSymbEvalS = ConstEvalS + SymbEvalS + BoolEvalS + CmpSymbAst
  sem stageDeltaF cs +=
  | c & CEqsym _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (eqi x y))
end

lang ConTagEvalS = ConstEvalS + DataEvalS + IntEvalS + ConTagAst
  sem stageDeltaF cs +=
  | c & CConstructorTag _ -> VConst1
    (c, lam v. match v with VConApp (tag, _) in VInt tag)
end

lang FloatStringConversionEvalS =
  ConstEvalS + BoolEvalS + FloatEvalS + StringConvEvalS +
  FloatStringConversionAst

  sem stageDeltaF cs +=
  | c & CStringIsFloat _ ->
    VConst1 (c, lam s. VBool (stringIsFloat (valToString s)))
  | c & CString2float _ ->
    VConst1 (c, lam s. VFloat (string2float (valToString s)))
  | c & CFloat2string _ -> VConst1
    (c, lam x. match x with VFloat f in stringToVal (float2string f))
end

lang FileOpEvalS =
  ConstEvalS + BoolEvalS + RecordEvalS + StringConvEvalS + FileOpAst

  sem stageDeltaF cs +=
  | c & CFileRead _ -> VConst1
    (c, lam f. stringToVal (readFile (valToString f)))
  | c & CFileWrite _ -> VConst2
    (c, lam f. lam d.
      writeFile (valToString f) (valToString d); unitVal)
  | c & CFileExists _ -> VConst1 (c, lam f. VBool (fileExists (valToString f)))
  | c & CFileDelete _ -> VConst1
    (c, lam f. deleteFile (valToString f); unitVal)
end

lang IOEvalS = ConstEvalS + RecordEvalS + StringConvEvalS + IOAst
  sem stageDeltaF cs +=
  | c & CPrint _ -> VConst1
    (c, lam s. print (valToString s); unitVal)
  | c & CPrintError _ -> VConst1
    (c, lam s. printError (valToString s); unitVal)
  | c & CDPrint _ -> VConst1 (c, lam. unitVal)
  | c & CFlushStdout _ -> VConst1
    (c, lam. flushStdout (); unitVal)
  | c & CFlushStderr _ -> VConst1
    (c, lam. flushStderr (); unitVal)
  | c & CReadLine _ -> VConst1 (c, lam. stringToVal (readLine ()))
  | c & CReadBytesAsString _ -> VConst1
    (c, lam. error "CReadBytesAsString: unimplemented")
end

lang RandomNumberGeneratorEvalS =
  ConstEvalS + IntEvalS + RecordEvalS + RandomNumberGeneratorAst

  sem stageDeltaF cs +=
  | c & CRandIntU _ -> VConst2
    (c, lam lo. lam hi.
          match (lo, hi) with (VInt lo, VInt hi) in VInt (randIntU lo hi))
  | c & CRandSetSeed _ -> VConst1
    (c, lam n. match n with VInt n in randSetSeed n; unitVal)
end

lang TimeEvalS = ConstEvalS + IntEvalS + FloatEvalS + RecordEvalS + TimeAst
  sem stageDeltaF cs +=
  | c & CWallTimeMs _ -> VConst1 (c, lam. VFloat (wallTimeMs ()))
  | c & CSleepMs _ -> VConst1
    (c, lam n. match n with VInt n in sleepMs n; unitVal)
end

lang RefOpEvalS = ConstEvalS + RecordEvalS + RefOpAst
  syn Val +=
  | VRef (Ref Val)

  sem evalSReadback +=
  | VRef r -> None ()

  sem stageDeltaF cs +=
  | c & CRef _ -> VConst1 (c, lam v. VRef (ref v))
  | c & CModRef _ -> VConst2
    (c, lam r. lam v.
          match r with VRef r in modref r v; unitVal)
  | c & CDeRef _ -> VConst1 (c, lam r. match r with VRef r in deref r)
end

lang TypeOpEvalS = ConstEvalS + TypeOpAst
  sem stageDeltaF cs +=
  | c & CTypeOf _ -> VConst1 (c, lam. error "CTypeOf: unimplemented")
end

lang TensorOpEvalS =
  ConstEvalS + IntEvalS + FloatEvalS + SeqEvalS + BoolEvalS + RecordEvalS +
  StringConvEvalS + TensorOpAst

  syn Val +=
  | VTensorInt (Tensor[Int])
  | VTensorFloat (Tensor[Float])
  | VTensorExpr (Tensor[Val])

  sem evalSReadback +=
  | VTensorInt _ | VTensorFloat _ | VTensorExpr _ -> None ()

  sem valSeqToShape : Val -> [Int]
  sem valSeqToShape =
  | VSeq vals -> map (lam v. match v with VInt i in i) vals

  sem shapeToValSeq : [Int] -> Val
  sem shapeToValSeq =
  | is -> VSeq (map (lam i. VInt i) is)

  sem tensorValRank : Val -> Int
  sem tensorValRank =
  | VTensorInt t -> tensorRank t
  | VTensorFloat t -> tensorRank t
  | VTensorExpr t -> tensorRank t

  sem tensorValShape : Val -> [Int]
  sem tensorValShape =
  | VTensorInt t -> tensorShape t
  | VTensorFloat t -> tensorShape t
  | VTensorExpr t -> tensorShape t

  sem tensorValGetExn : [Int] -> Val -> Val
  sem tensorValGetExn is =
  | VTensorInt t -> VInt (tensorGetExn t is)
  | VTensorFloat t -> VFloat (tensorGetExn t is)
  | VTensorExpr t -> tensorGetExn t is

  sem tensorValLinearGetExn : Int -> Val -> Val
  sem tensorValLinearGetExn i =
  | VTensorInt t -> VInt (tensorLinearGetExn t i)
  | VTensorFloat t -> VFloat (tensorLinearGetExn t i)
  | VTensorExpr t -> tensorLinearGetExn t i

  sem tensorValReshapeExn : [Int] -> Val -> Val
  sem tensorValReshapeExn is =
  | VTensorInt t -> VTensorInt (tensorReshapeExn t is)
  | VTensorFloat t -> VTensorFloat (tensorReshapeExn t is)
  | VTensorExpr t -> VTensorExpr (tensorReshapeExn t is)

  sem tensorValCopy : Val -> Val
  sem tensorValCopy =
  | VTensorInt t -> VTensorInt (tensorCopy t)
  | VTensorFloat t -> VTensorFloat (tensorCopy t)
  | VTensorExpr t -> VTensorExpr (tensorCopy t)

  sem tensorValTransposeExn : Int -> Int -> Val -> Val
  sem tensorValTransposeExn d0 d1 =
  | VTensorInt t -> VTensorInt (tensorTransposeExn t d0 d1)
  | VTensorFloat t -> VTensorFloat (tensorTransposeExn t d0 d1)
  | VTensorExpr t -> VTensorExpr (tensorTransposeExn t d0 d1)

  sem tensorValSliceExn : [Int] -> Val -> Val
  sem tensorValSliceExn is =
  | VTensorInt t -> VTensorInt (tensorSliceExn t is)
  | VTensorFloat t -> VTensorFloat (tensorSliceExn t is)
  | VTensorExpr t -> VTensorExpr (tensorSliceExn t is)

  sem tensorValSubExn : Int -> Int -> Val -> Val
  sem tensorValSubExn ofs len =
  | VTensorInt t -> VTensorInt (tensorSubExn t ofs len)
  | VTensorFloat t -> VTensorFloat (tensorSubExn t ofs len)
  | VTensorExpr t -> VTensorExpr (tensorSubExn t ofs len)

  sem tensorValIterSlice : Info -> Val -> Val -> Val
  sem tensorValIterSlice info f =
  | VTensorInt t ->
    tensorIterSlice
      (lam i. lam s.
        applyS (info, applyS (info, f, VInt i), VTensorInt s); ())
      t;
    unitVal
  | VTensorFloat t ->
    tensorIterSlice
      (lam i. lam s.
        applyS (info, applyS (info, f, VInt i), VTensorFloat s); ())
      t;
    unitVal
  | VTensorExpr t ->
    tensorIterSlice
      (lam i. lam s.
        applyS (info, applyS (info, f, VInt i), VTensorExpr s); ())
      t;
    unitVal

  sem tensorValToString : Info -> Val -> Val -> Val
  sem tensorValToString info el2str =
  | VTensorInt t ->
    stringToVal
      (tensor2string (lam x. valToString (applyS (info, el2str, VInt x))) t)
  | VTensorFloat t ->
    stringToVal
      (tensor2string
        (lam x. valToString (applyS (info, el2str, VFloat x))) t)
  | VTensorExpr t ->
    stringToVal
      (tensor2string (lam x. valToString (applyS (info, el2str, x))) t)

  sem tensorValSetExn : [Int] -> Val -> Val -> Val
  sem tensorValSetExn is t =
  | v ->
    (switch (t, v)
     case (VTensorInt t, VInt v) then tensorSetExn t is v
     case (VTensorFloat t, VFloat v) then tensorSetExn t is v
     case (VTensorExpr t, v) then tensorSetExn t is v
     case _ then error "tensorValSetExn: type error"
     end);
    unitVal

  sem tensorValLinearSetExn : Int -> Val -> Val -> Val
  sem tensorValLinearSetExn i t =
  | v ->
    (switch (t, v)
     case (VTensorInt t, VInt v) then tensorLinearSetExn t i v
     case (VTensorFloat t, VFloat v) then tensorLinearSetExn t i v
     case (VTensorExpr t, v) then tensorLinearSetExn t i v
     case _ then error "tensorValLinearSetExn: type error"
     end);
    unitVal

  sem tensorValEq : Info -> Val -> Val -> Val -> Val
  sem tensorValEq info eq t1 =
  | t2 ->
    let veq = lam a. lam b.
      match applyS (info, applyS (info, eq, a), b) with VBool b in b in
    VBool
      (switch (t1, t2)
       case (VTensorInt t1, VTensorInt t2) then
         tensorEq (lam a. lam b. veq (VInt a) (VInt b)) t1 t2
       case (VTensorInt t1, VTensorFloat t2) then
         tensorEq (lam a. lam b. veq (VInt a) (VFloat b)) t1 t2
       case (VTensorInt t1, VTensorExpr t2) then
         tensorEq (lam a. lam b. veq (VInt a) b) t1 t2
       case (VTensorFloat t1, VTensorInt t2) then
         tensorEq (lam a. lam b. veq (VFloat a) (VInt b)) t1 t2
       case (VTensorFloat t1, VTensorFloat t2) then
         tensorEq (lam a. lam b. veq (VFloat a) (VFloat b)) t1 t2
       case (VTensorFloat t1, VTensorExpr t2) then
         tensorEq (lam a. lam b. veq (VFloat a) b) t1 t2
       case (VTensorExpr t1, VTensorInt t2) then
         tensorEq (lam a. lam b. veq a (VInt b)) t1 t2
       case (VTensorExpr t1, VTensorFloat t2) then
         tensorEq (lam a. lam b. veq a (VFloat b)) t1 t2
       case (VTensorExpr t1, VTensorExpr t2) then
         tensorEq veq t1 t2
       case _ then error "tensorValEq: not a tensor"
       end)

  sem stageDeltaF cs +=
  | c & CTensorCreateUninitInt _ -> VConst1
    (c, lam shape. VTensorInt (tensorCreateUninitInt (valSeqToShape shape)))
  | c & CTensorCreateUninitFloat _ -> VConst1
    (c, lam shape. VTensorFloat (tensorCreateUninitFloat (valSeqToShape shape)))
  | c & CTensorCreateInt _ -> VConstInfo2
    (c, lam info. lam shape. lam f.
      VTensorInt
        (tensorCreateCArrayInt
          (valSeqToShape shape)
          (lam is.
            match applyS (info, f, shapeToValSeq is) with VInt n in n)))
  | c & CTensorCreateFloat _ -> VConstInfo2
    (c, lam info. lam shape. lam f.
      VTensorFloat
        (tensorCreateCArrayFloat
          (valSeqToShape shape)
          (lam is.
            match applyS (info, f, shapeToValSeq is) with VFloat x in x)))
  | c & CTensorCreate _ -> VConstInfo2
    (c, lam info. lam shape. lam f.
      VTensorExpr
        (tensorCreateDense
          (valSeqToShape shape) (lam is. applyS (info, f, shapeToValSeq is))))
  | c & CTensorGetExn _ -> VConst2
    (c, lam t. lam idx. tensorValGetExn (valSeqToShape idx) t)
  | c & CTensorSetExn _ -> VConst3
    (c, lam t. lam idx. lam v. tensorValSetExn (valSeqToShape idx) t v)
  | c & CTensorLinearGetExn _ -> VConst2
    (c, lam t. lam i. match i with VInt i in tensorValLinearGetExn i t)
  | c & CTensorLinearSetExn _ -> VConst3
    (c, lam t. lam i. lam v. match i with VInt i in tensorValLinearSetExn i t v)
  | c & CTensorRank _ -> VConst1 (c, lam t. VInt (tensorValRank t))
  | c & CTensorShape _ -> VConst1 (c, lam t. shapeToValSeq (tensorValShape t))
  | c & CTensorReshapeExn _ -> VConst2
    (c, lam t. lam shape. tensorValReshapeExn (valSeqToShape shape) t)
  | c & CTensorCopy _ -> VConst1 (c, tensorValCopy)
  | c & CTensorTransposeExn _ -> VConst3
    (c, lam t. lam d0. lam d1.
      match (d0, d1) with (VInt d0, VInt d1) in tensorValTransposeExn d0 d1 t)
  | c & CTensorSliceExn _ -> VConst2
    (c, lam t. lam idx. tensorValSliceExn (valSeqToShape idx) t)
  | c & CTensorSubExn _ -> VConst3
    (c, lam t. lam ofs. lam len.
      match (ofs, len) with (VInt ofs, VInt len) in tensorValSubExn ofs len t)
  | c & CTensorIterSlice _ -> VConstInfo2 (c, tensorValIterSlice)
  | c & CTensorEq _ -> VConstInfo3 (c, tensorValEq)
  | c & CTensorToString _ -> VConstInfo2 (c, tensorValToString)
end

lang BootParserEvalF =
  ConstEvalS + IntEvalS + FloatEvalS + BoolEvalS + RecordEvalS +
  StringConvEvalS + BootParserAst

  syn Val +=
  | VBootParserTree BootParseTree

  sem evalSReadback +=
  | VBootParserTree _ -> None ()

  sem valSeqToStrings : Val -> [String]
  sem valSeqToStrings =
  | VSeq vals -> map valToString vals

  sem stageDeltaF cs +=
  | c & CBootParserParseMExprString _ -> VConst3
    (c, lam opts. lam keywords. lam src.
      match opts with VRecord bindings in
      match mapLookup _sid_0 bindings with Some (VBool allowFree) in
      VBootParserTree
        (bootParserParseMExprString
          (allowFree,) (valSeqToStrings keywords) (valToString src)))
  | c & CBootParserParseMLangString _ -> VConst1
    (c, lam src. VBootParserTree (bootParserParseMLangString (valToString src)))
  | c & CBootParserParseMLangFile _ -> VConst1
    (c, lam f. VBootParserTree (bootParserParseMLangFile (valToString f)))
  | c & CBootParserParseMCoreFile _ -> VConst3
    (c, lam opts. lam keywords. lam filename.
      match opts with VRecord bindings in
      match
        map (lam k. mapLookup k bindings)
          [_sid_0, _sid_1, _sid_2, _sid_3, _sid_4, _sid_5]
      with
        [ Some (VBool keepUtests), Some (VBool pruneExternalUtests)
        , Some externalsExclude, Some (VBool warn)
        , Some (VBool eliminateDeadCode), Some (VBool allowFree) ]
      in
      let pruneArg =
        ( keepUtests, pruneExternalUtests, valSeqToStrings externalsExclude
        , warn, eliminateDeadCode, allowFree ) in
      VBootParserTree
        (bootParserParseMCoreFile
          pruneArg (valSeqToStrings keywords) (valToString filename)))
  | c & CBootParserGetId _ -> VConst1
    (c, lam t. match t with VBootParserTree t in VInt (bootParserGetId t))
  | c & CBootParserGetTerm _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetTerm t n))
  | c & CBootParserGetTop _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetTop t n))
  | c & CBootParserGetDecl _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetDecl t n))
  | c & CBootParserGetType _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetType t n))
  | c & CBootParserGetConst _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetConst t n))
  | c & CBootParserGetPat _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetPat t n))
  | c & CBootParserGetCopat _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetCopat t n))
  | c & CBootParserGetInfo _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VBootParserTree (bootParserGetInfo t n))
  | c & CBootParserGetString _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      stringToVal (bootParserGetString t n))
  | c & CBootParserGetInt _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VInt (bootParserGetInt t n))
  | c & CBootParserGetFloat _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VFloat (bootParserGetFloat t n))
  | c & CBootParserGetListLength _ -> VConst2
    (c, lam t. lam n.
      match (t, n) with (VBootParserTree t, VInt n) in
      VInt (bootParserGetListLength t n))
end

--------------
-- PATTERNS --
--------------

lang NamedPatEvalS = MatchEvalS + NamedPat
  sem stageTryMatch +=
  | PatNamed {ident = PName name} ->
    match nameGetSym name with Some s then
      let s = sym2hash s in
      lam val. lam env. Some (Cons ((s, val), env))
    else error "Unsymbolized PatNamed in stageTryMatch!"
  | PatNamed {ident = PWildcard ()} -> lam. lam env. Some env
end

lang BoolPatEvalS = MatchEvalS + BoolEvalS + BoolAst + BoolPat
  sem stageTryMatch +=
  | PatBool r -> lam val. lam env.
    match val with VBool b then
      match (b, r.val) with (true, true) | (false, false) then Some env
      else None ()
    else None ()
end

lang RecordPatEvalS = MatchEvalS + RecordEvalS + RecordAst + RecordPat +
                     MatchAst + VarAst + NeverAst + NamedPat
  sem evalSStageExpr cs +=
  -- OPT(oerikss, 2026-09-29): Stage a simpler evaluation function for the
  -- common special match case expr.label
  | TmMatch (r & {pat = PatRecord p
                 ,thn = TmVar v
                 ,els = TmNever _}) ->
    let target = evalSStageExpr cs r.target in
    let els = evalSStageExpr cs r.els in
    let default = lam.
      let thn = evalSStageExpr cs r.thn in
      let tryMatch = stageTryMatch r.pat in
      lam env.
        match tryMatch (target env) env with Some env then thn env
        else els env in
    match mapBindings p.bindings with [(sid, PatNamed {ident = PName n})] then
      if nameEq v.ident n then
        lam env.
          match target env with VRecord rbindings then
            match mapLookup sid rbindings with Some val then val
            else els env
          else els env
      else default ()
    else default ()

  sem stageTryMatch +=
  | PatRecord r ->
    let pbindings = mapMap stageTryMatch r.bindings in
    lam val. lam env.
      match val with VRecord rbindings then
        mapFoldlOption
          (lam env. lam k. lam pat.
            match mapLookup k rbindings with Some val then pat val env
            else None ())
          env
          pbindings
      else None ()
end

lang SeqTotPatEvalS = MatchEvalS + SeqEvalS + SeqTotPat
  sem stageTryMatch +=
  | PatSeqTot r ->
    let pats = map stageTryMatch r.pats in
    let n = length pats in
    lam val. lam env.
      match val with VSeq vals then
        if eqi (length vals) n then
          optionFoldlM
            (lam env. lam pv. match pv with (pat, v) in pat v env)
            env
            (zipWith (lam pat. lam v. (pat, v)) pats vals)
        else None ()
      else None ()
end

lang SeqEdgePatEvalS = MatchEvalS + SeqEvalS + SeqEdgePat
  sem stageTryMatch +=
  | PatSeqEdge r ->
    let pats = map stageTryMatch (concat r.prefix r.postfix) in
    let npre = length r.prefix in
    let npost = length r.postfix in
    let nfix = addi npre npost in
    -- The middle binds the remaining subsequence, or is dropped for `_`.
    let middle =
      match r.middle with PName name then
        match nameGetSym name with Some s then
          let s = sym2hash s in
          lam vals. lam env. Some (Cons ((s, VSeq vals), env))
        else error "Unsymbolized PatSeqEdge in stageTryMatch!"
      else lam. lam env. Some env
    in
    lam val. lam env.
      match val with VSeq vals then
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

lang DataPatEvalS = MatchEvalS + DataEvalS + DataPat
  sem stageTryMatch +=
  | PatCon r ->
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      let subpat = stageTryMatch r.subpat in
      lam val. lam env.
        match val with VConApp (c, arg) then
          if eqi c s then subpat arg env
          else None ()
        else None ()
    else error "Unsymbolized PatCon in stageTryMatch!"
end

lang IntPatEvalS = MatchEvalS + IntEvalS + IntPat
  sem stageTryMatch +=
  | PatInt r -> lam val. lam env.
    match val with VInt i then
      if eqi i r.val then Some env else None ()
    else None ()
end

lang CharPatEvalS = MatchEvalS + CharEvalS + CharPat
  sem stageTryMatch +=
  | PatChar r -> lam val. lam env.
    match val with VChar c then
      if eqc c r.val then Some env else None ()
    else None ()
end

lang AndPatEvalS = MatchEvalS + AndPat
  sem stageTryMatch +=
  | PatAnd r ->
    let lpat = stageTryMatch r.lpat in
    let rpat = stageTryMatch r.rpat in
    lam val. lam env.
      match lpat val env with Some env then rpat val env
      else None ()
end

lang OrPatEvalS = MatchEvalS + OrPat
  sem stageTryMatch +=
  | PatOr r ->
    let lpat = stageTryMatch r.lpat in
    let rpat = stageTryMatch r.rpat in
    lam val. lam env.
      match lpat val env with Some env then Some env else rpat val env
end

lang NotPatEvalS = MatchEvalS + NotPat
  sem stageTryMatch +=
  | PatNot r ->
    let subpat = stageTryMatch r.subpat in
    lam val. lam env.
      match subpat val env with Some _ then None () else Some env
end

------------------
-- COMPOSITIONS --
------------------

lang MExprEvalS =
  -- Terms and Decls
  VarEvalF + AppEvalS + LamEvalS + DeclEvalS + ConstEvalS + MatchEvalS +
  RecordEvalS + SeqEvalS + NeverEvalS + DataEvalS + UtestEvalS + ExtEvalS +
  PlaceholderEvalS + OpaqueEvalS +

  -- Decls
  LetEvalS + RecLetsEvalS + TypeEvalS +

  -- Constants
  UnsafeCoerceEvalS + IntEvalS + ArithIntEvalS + ShiftIntEvalS +  BoolEvalS +
  CmpIntEvalS + CharEvalS + CmpCharEvalS + IntCharConversionEvalS +
  FloatEvalS + ArithFloatEvalS + CmpFloatEvalS +
  FloatIntConversionEvalS + SeqOpEvalS + StringConvEvalS + SysEvalS +
  SymbEvalS + CmpSymbEvalS + ConTagEvalS + FloatStringConversionEvalS +
  FileOpEvalS + IOEvalS + RandomNumberGeneratorEvalS + TimeEvalS +
  RefOpEvalS + TypeOpEvalS + TensorOpEvalS + BootParserEvalF +

  -- Patterns
  NamedPatEvalS + BoolPatEvalS + RecordPatEvalS + SeqTotPatEvalS +
  SeqEdgePatEvalS + DataPatEvalS + IntPatEvalS + CharPatEvalS +
  AndPatEvalS + OrPatEvalS + NotPatEvalS
end

lang TestLang = MExprEvalS + MExprEq + MExprPrettyPrint + MExprSym end

mexpr

use TestLang in

let toString =
  let toString = optionMapOr "None" expr2str in
  utestDefaultToString toString toString in

let eq = optionEq eqExpr in

let env : EvalSEnv = Nil () in

let eval : Expr -> Val = lam e. evalSStageExpr (None ()) (symbolize e) env in

utest evalSReadback (eval (app_ (ulam_ "x" (var_ "x")) (int_ 0)))
with Some (int_ 0) using eq else toString in

utest evalSReadback (eval (app_ (ulam_ "x" (addi_ (var_ "x") (int_ 2))) (int_ 1)))
with Some (int_ 3) using eq else toString in

-------------------------------------------
-- UNIT TESTS FOR THE CONSTANT FRAGMENTS --
-------------------------------------------

-- SymbEvalS

-- `sym2hash` on an already-hash-represented symbol is a no-op.
utest
  evalSReadback
    (eval (bindall_ [ulet_ "s" (gensym_ uunit_)]
      (eqi_ (var_ "s") (sym2hash_ (var_ "s")))))
with Some true_ using eq else toString in

-- Reading the same binding's hash twice gives the same value.
utest
  evalSReadback
    (eval (bindall_ [ulet_ "s" (gensym_ uunit_)]
      (eqi_ (sym2hash_ (var_ "s")) (sym2hash_ (var_ "s")))))
with Some true_ using eq else toString in

-- Two separate `gensym`s are (almost certainly) distinct.
utest
  evalSReadback
    (eval (bindall_ [ulet_ "s1" (gensym_ uunit_), ulet_ "s2" (gensym_ uunit_)]
      (eqi_ (var_ "s1") (var_ "s2"))))
with Some false_ using eq else toString in

-- CmpSymbEvalS

utest
  evalSReadback
    (eval (bindall_ [ulet_ "s" (gensym_ uunit_)]
      (eqsym_ (var_ "s") (var_ "s"))))
with Some true_ using eq else toString in

utest
  evalSReadback
    (eval (bindall_ [ulet_ "s1" (gensym_ uunit_), ulet_ "s2" (gensym_ uunit_)]
      (eqsym_ (var_ "s1") (var_ "s2"))))
with Some false_ using eq else toString in

-- ConTagEvalS

let constructorTag_ = lam e. app_ (uconst_ (CConstructorTag ())) e in

-- Same constructor -> same tag, regardless of its argument.
utest
  evalSReadback
    (eval (bindall_ [ucondef_ "Foo", ucondef_ "Bar"]
      (eqi_
        (constructorTag_ (conapp_ "Foo" (int_ 0)))
        (constructorTag_ (conapp_ "Foo" (int_ 1))))))
with Some true_ using eq else toString in

-- Different constructors -> different tags.
utest
  evalSReadback
    (eval (bindall_ [ucondef_ "Foo", ucondef_ "Bar"]
      (eqi_
        (constructorTag_ (conapp_ "Foo" (int_ 0)))
        (constructorTag_ (conapp_ "Bar" (int_ 0))))))
with Some false_ using eq else toString in

-- FloatStringConversionEvalS

utest evalSReadback (eval (string2float_ (str_ "1.5")))
with Some (float_ 1.5) using eq else toString in

utest evalSReadback (eval (float2string_ (float_ 1.5)))
with Some (str_ "1.5") using eq else toString in

utest evalSReadback (eval (stringIsfloat_ (str_ "1.5")))
with Some true_ using eq else toString in

utest evalSReadback (eval (stringIsfloat_ (str_ "abc")))
with Some false_ using eq else toString in

-- FileOpEvalS

-- The scratch path is computed as an ordinary host-level string (this outer
-- `mexpr` block is run by the real evaluator, unrestricted), then spliced in
-- as a literal -- `readFile_`/`writeFile_`/etc. themselves stay inside the
-- fast evaluator's supported subset. Suffixed with a fresh symbol's hash so
-- repeated runs (or a run alongside other test suites) never collide.
let scratchFile =
  concat "/tmp/eval-fast-test-" (int2string (sym2hash (gensym ()))) in

utest
  evalSReadback
    (eval (bindall_ [ulet_ "_" (writeFile_ (str_ scratchFile) (str_ "hello"))]
      (readFile_ (str_ scratchFile))))
with Some (str_ "hello") using eq else toString in

utest evalSReadback (eval (fileExists_ (str_ scratchFile)))
with Some true_ using eq else toString in

utest
  evalSReadback
    (eval (bindall_ [ulet_ "_" (deleteFile_ (str_ scratchFile))]
      (fileExists_ (str_ scratchFile))))
with Some false_ using eq else toString in

-- `CReadLine`/`CReadBytesAsString` are not exercised here: the former would
-- block on stdin (nothing is piped into this test run), and the latter has
-- no runtime semantics -- see the `IOEvalS` fragment's comment above.

-- RandomNumberGeneratorEvalS

utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "_" (randSetSeed_ (int_ 42))
        , ulet_ "n" (randIntU_ (int_ 10) (int_ 20)) ]
        (and_ (geqi_ (var_ "n") (int_ 10)) (lti_ (var_ "n") (int_ 20)))))
with Some true_ using eq else toString in

-- TimeEvalS

utest evalSReadback (eval (geqf_ (wallTimeMs_ uunit_) (float_ 0.0)))
with Some true_ using eq else toString in

utest evalSReadback (eval (sleepMs_ (int_ 0))) with Some uunit_ using eq else toString in

-- RefOpEvalS

utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "r1" (ref_ (int_ 1))
        , ulet_ "r2" (ref_ (float_ 2.0)) ]
        (utuple_ [deref_ (var_ "r1"), deref_ (var_ "r2")])))
with Some (utuple_ [int_ 1, float_ 2.0]) using eq else toString in

utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "r" (ref_ (int_ 1))
        , ulet_ "_" (modref_ (var_ "r") (int_ 2)) ]
        (deref_ (var_ "r"))))
with Some (int_ 2) using eq else toString in

-- TensorOpEvalS

let tensorCreateUninitInt_ = lam shape. app_ (uconst_ (CTensorCreateUninitInt ())) shape in
let tensorCreateUninitFloat_ = lam shape. app_ (uconst_ (CTensorCreateUninitFloat ())) shape in

utest evalSReadback (eval (utensorRank_ (tensorCreateUninitInt_ (seq_ [int_ 2, int_ 3]))))
with Some (int_ 2) using eq else toString in

utest evalSReadback (eval (utensorShape_ (tensorCreateUninitFloat_ (seq_ [int_ 4]))))
with Some (seq_ [int_ 4]) using eq else toString in

-- create (int/float/generic) + get, rank-1 and rank-0
utest
  evalSReadback
    (eval
      (bindall_
        [ulet_ "t" (tensorCreateInt_ (seq_ [int_ 3]) (ulam_ "is" (get_ (var_ "is") (int_ 0))))]
        (utuple_
          [ utensorGetExn_ (var_ "t") (seq_ [int_ 0])
          , utensorGetExn_ (var_ "t") (seq_ [int_ 1])
          , utensorGetExn_ (var_ "t") (seq_ [int_ 2]) ])))
with Some (utuple_ [int_ 0, int_ 1, int_ 2]) using eq else toString in

utest
  evalSReadback (eval (utensorGetExn_ (tensorCreateFloat_ (seq_ []) (ulam_ "is" (float_ 3.14))) (seq_ [])))
with Some (float_ 3.14) using eq else toString in

utest
  evalSReadback
    (eval
      (utensorGetExn_
        (utensorCreate_ (seq_ [int_ 2])
          (ulam_ "is" (utuple_ [get_ (var_ "is") (int_ 0), get_ (var_ "is") (int_ 0)])))
        (seq_ [int_ 1])))
with Some (utuple_ [int_ 1, int_ 1]) using eq else toString in

-- set then get round trip
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t" (tensorCreateInt_ (seq_ [int_ 3]) (ulam_ "is" (int_ 0)))
        , ulet_ "_" (utensorSetExn_ (var_ "t") (seq_ [int_ 1]) (int_ 42)) ]
        (utensorGetExn_ (var_ "t") (seq_ [int_ 1]))))
with Some (int_ 42) using eq else toString in

-- linear get/set
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t" (tensorCreateInt_ (seq_ [int_ 3]) (ulam_ "is" (int_ 0)))
        , ulet_ "_" (utensorLinearSetExn_ (var_ "t") (int_ 2) (int_ 9)) ]
        (utensorLinearGetExn_ (var_ "t") (int_ 2))))
with Some (int_ 9) using eq else toString in

-- rank and shape
utest
  evalSReadback
    (eval
      (bindall_
        [ulet_ "t" (tensorCreateInt_ (seq_ [int_ 2, int_ 3]) (ulam_ "is" (int_ 0)))]
        (utuple_ [utensorRank_ (var_ "t"), utensorShape_ (var_ "t")])))
with Some (utuple_ [int_ 2, seq_ [int_ 2, int_ 3]]) using eq else toString in

-- reshape's resulting shape
utest
  evalSReadback
    (eval
      (utensorShape_
        (utensorReshapeExn_
          (tensorCreateInt_ (seq_ [int_ 6]) (ulam_ "is" (int_ 0)))
          (seq_ [int_ 2, int_ 3]))))
with Some (seq_ [int_ 2, int_ 3]) using eq else toString in

-- copy independence: mutating the copy leaves the original unaffected
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t" (tensorCreateInt_ (seq_ [int_ 1]) (ulam_ "is" (int_ 7)))
        , ulet_ "c" (utensorCopy_ (var_ "t"))
        , ulet_ "_" (utensorSetExn_ (var_ "c") (seq_ [int_ 0]) (int_ 99)) ]
        (utuple_
          [ utensorGetExn_ (var_ "t") (seq_ [int_ 0])
          , utensorGetExn_ (var_ "c") (seq_ [int_ 0]) ])))
with Some (utuple_ [int_ 7, int_ 99]) using eq else toString in

-- transpose's resulting shape
utest
  evalSReadback
    (eval
      (utensorShape_
        (utensorTransposeExn_
          (tensorCreateInt_ (seq_ [int_ 2, int_ 3]) (ulam_ "is" (int_ 0)))
          (int_ 0) (int_ 1))))
with Some (seq_ [int_ 3, int_ 2]) using eq else toString in

-- slice's resulting rank and shape
utest
  evalSReadback
    (eval
      (bindall_
        [ulet_ "t" (tensorCreateInt_ (seq_ [int_ 2, int_ 3]) (ulam_ "is" (int_ 0)))]
        (utuple_
          [ utensorRank_ (utensorSliceExn_ (var_ "t") (seq_ [int_ 0]))
          , utensorShape_ (utensorSliceExn_ (var_ "t") (seq_ [int_ 0])) ])))
with Some (utuple_ [int_ 1, seq_ [int_ 3]]) using eq else toString in

-- sub's resulting rank and shape
utest
  evalSReadback
    (eval
      (bindall_
        [ulet_ "t" (tensorCreateInt_ (seq_ [int_ 6]) (ulam_ "is" (int_ 0)))]
        (utuple_
          [ utensorRank_ (utensorSubExn_ (var_ "t") (int_ 2) (int_ 3))
          , utensorShape_ (utensorSubExn_ (var_ "t") (int_ 2) (int_ 3)) ])))
with Some (utuple_ [int_ 1, seq_ [int_ 3]]) using eq else toString in

-- iterSlice: mutating through a slice is visible in the original tensor
-- (tensors are views, not copies)
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t" (tensorCreateInt_ (seq_ [int_ 3]) (ulam_ "is" (int_ 0)))
        , ulet_ "_"
            (utensorIterSlice_
              (ulam_ "i" (ulam_ "s" (utensorSetExn_ (var_ "s") (seq_ []) (var_ "i"))))
              (var_ "t")) ]
        (utuple_
          [ utensorGetExn_ (var_ "t") (seq_ [int_ 0])
          , utensorGetExn_ (var_ "t") (seq_ [int_ 1])
          , utensorGetExn_ (var_ "t") (seq_ [int_ 2]) ])))
with Some (utuple_ [int_ 0, int_ 1, int_ 2]) using eq else toString in

-- eq: same-kind equal and unequal
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t1" (tensorCreateInt_ (seq_ [int_ 2]) (ulam_ "is" (get_ (var_ "is") (int_ 0))))
        , ulet_ "t2" (tensorCreateInt_ (seq_ [int_ 2]) (ulam_ "is" (get_ (var_ "is") (int_ 0)))) ]
        (utensorEq_ (ulam_ "a" (ulam_ "b" (eqi_ (var_ "a") (var_ "b"))))
          (var_ "t1") (var_ "t2"))))
with Some true_ using eq else toString in

utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t1" (tensorCreateInt_ (seq_ [int_ 2]) (ulam_ "is" (int_ 0)))
        , ulet_ "t2" (tensorCreateInt_ (seq_ [int_ 2]) (ulam_ "is" (int_ 1))) ]
        (utensorEq_ (ulam_ "a" (ulam_ "b" (eqi_ (var_ "a") (var_ "b"))))
          (var_ "t1") (var_ "t2"))))
with Some false_ using eq else toString in

-- eq: mixed kind (int tensor vs. generic tensor storing plain ints)
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t1" (tensorCreateInt_ (seq_ [int_ 2])
                        (ulam_ "is" (get_ (var_ "is") (int_ 0))))
        , ulet_ "t2" (utensorCreate_ (seq_ [int_ 2])
                        (ulam_ "is" (get_ (var_ "is") (int_ 0)))) ]
        (utensorEq_ (ulam_ "a" (ulam_ "b" (eqi_ (var_ "a") (var_ "b"))))
          (var_ "t1") (var_ "t2"))))
with Some true_ using eq else toString in

-- toString, matching the same bracket/tab/comma format used elsewhere in
-- the suite (a constant element-to-string function isolates the format
-- check from int-to-string conversion, which isn't available inside this
-- restricted expression language)
utest
  evalSReadback
    (eval
      (utensor2string_
        (ulam_ "x" (str_ "n"))
        (tensorCreateInt_ (seq_ [int_ 2, int_ 3]) (ulam_ "is" (int_ 0)))))
with Some (str_ "[\n\t[n, n, n],\n\t[n, n, n]\n]") using eq else toString in

-- BootParserEvalF

-- There is no `bootParser*_` ast-builder helper, so these are built by hand
-- from the raw constants, the same trick used for `CConstructorTag` and
-- `CTensorCreateUninit*` above. An MExpr tuple already compiles to a record
-- keyed "0", "1", ... -- exactly the shape the two `Parse*` constants below
-- expect for their options argument, so no separate record-builder is
-- needed.
let bootParserParseMExprString_ = lam allowFree. lam keywords. lam src.
  appf3_ (uconst_ (CBootParserParseMExprString ()))
    (utuple_ [bool_ allowFree]) (seq_ (map str_ keywords)) (str_ src) in
let bootParserGetId_ = lam t. app_ (uconst_ (CBootParserGetId ())) t in
let bootParserGetTerm_ = lam t. lam n.
  appf2_ (uconst_ (CBootParserGetTerm ())) t (int_ n) in
let bootParserGetString_ = lam t. lam n.
  appf2_ (uconst_ (CBootParserGetString ())) t (int_ n) in
let bootParserGetInt_ = lam t. lam n.
  appf2_ (uconst_ (CBootParserGetInt ())) t (int_ n) in
let bootParserGetFloat_ = lam t. lam n.
  appf2_ (uconst_ (CBootParserGetFloat ())) t (int_ n) in
let bootParserGetConst_ = lam t. lam n.
  appf2_ (uconst_ (CBootParserGetConst ())) t (int_ n) in
let bootParserGetListLength_ = lam t. lam n.
  appf2_ (uconst_ (CBootParserGetListLength ())) t (int_ n) in

-- Parse "x" with `allowFree` (mirrors `boot-parser.mc`'s own `allowFree`
-- test): root tag 100 = TmVar, string field 0 = the identifier, int field 0
-- = the frozen flag.
utest
  evalSReadback
    (eval
      (bindall_ [ulet_ "t" (bootParserParseMExprString_ true [] "x")]
        (utuple_
          [ bootParserGetId_ (var_ "t")
          , bootParserGetString_ (var_ "t") 0
          , bootParserGetInt_ (var_ "t") 0 ])))
with Some (utuple_ [int_ 100, str_ "x", int_ 0]) using eq else toString in

-- Parse "lam x. x": root tag 102 = TmLam, string field 0 = the parameter.
-- `GetTerm` at field 0 gives the body sub-tree (tag 100 = TmVar, string
-- field 0 = "x" again) -- the one thing the plain-literal tests above don't
-- reach.
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t" (bootParserParseMExprString_ false [] "lam x. x")
        , ulet_ "body" (bootParserGetTerm_ (var_ "t") 0) ]
        (utuple_
          [ bootParserGetId_ (var_ "t")
          , bootParserGetString_ (var_ "t") 0
          , bootParserGetId_ (var_ "body")
          , bootParserGetString_ (var_ "body") 0 ])))
with Some (utuple_ [int_ 102, str_ "x", int_ 100, str_ "x"])
using eq else toString in

-- Parse "3.14": root tag 105 = TmConst. `GetConst` at field 0 gives a const
-- sub-tree of tag 302 = CFloat, whose float field 0 is the value --
-- exercises `GetConst`/`GetFloat`.
utest
  evalSReadback
    (eval
      (bindall_
        [ ulet_ "t" (bootParserParseMExprString_ false [] "3.14")
        , ulet_ "c" (bootParserGetConst_ (var_ "t") 0) ]
        (utuple_
          [ bootParserGetId_ (var_ "t")
          , bootParserGetId_ (var_ "c")
          , bootParserGetFloat_ (var_ "c") 0 ])))
with Some (utuple_ [int_ 105, int_ 302, float_ 3.14]) using eq else toString in

-- Parse "[1, 2, 3]": root tag 106 = TmSeq, whose list-length field 0 is the
-- element count -- exercises `GetListLength`.
utest
  evalSReadback
    (eval
      (bindall_ [ulet_ "t" (bootParserParseMExprString_ false [] "[1, 2, 3]")]
        (utuple_
          [ bootParserGetId_ (var_ "t")
          , bootParserGetListLength_ (var_ "t") 0 ])))
with Some (utuple_ [int_ 106, int_ 3]) using eq else toString in

------------------------------
-- UNIT TESTS FOR CALLSTACK --
------------------------------

let mkInfo = lam i. infoVal "" i 0 0 0 in

utest callstackInit -1 with None () in
utest
  match callstackInit 4 with Some cs then
    let cs = foldl (flip callstackPush) cs (create 42 mkInfo) in
    utest
      match
        optionMapAccumLM
          (lam cs. lam. callstackPop cs) cs (create 4 (lam. 0))
      with Some (_, infos) then
        utest infos with create 4 (lam i. mkInfo (subi 41 i)) in
        true
      else false
    with true in
    true
else false with true in

------------------------------------------------
-- UNIT TESTS FOR CALLSTACK-AWARE EVALUATION  --
------------------------------------------------

-- Single closure, single call: checks that TmLam's `Some csr` branch wires
-- up clsUsingCallstack at all, and that a normal (non-erroring) call leaves
-- the callstack balanced (empty) afterward.
let xN = nameSym "x" in
let infoApp = mkInfo 1000 in
let term = tmApp infoApp tyunknown_ (nulam_ xN (nvar_ xN)) (int_ 42) in
(match callstackInit 8 with Some cs0 then
  let csr = ref cs0 in
  let v = evalSStageExpr (Some csr) (symbolize term) env in
  utest evalSReadback v with Some (int_ 42) using eq else toString in
  utest callstackPop (deref csr) with None () in
  ()
else ());

-- Nested closures, two separate call sites with distinct infos.
let xN = nameSym "x" in
let yN = nameSym "y" in
let info1 = mkInfo 1001 in
let info2 = mkInfo 1002 in
let lam2 = nulam_ xN (nulam_ yN (addi_ (nvar_ xN) (nvar_ yN))) in
let term = tmApp info2 tyunknown_
             (tmApp info1 tyunknown_ lam2 (int_ 1)) (int_ 2) in
(match callstackInit 8 with Some cs0 then
  let csr = ref cs0 in
  let v = evalSStageExpr (Some csr) (symbolize term) env in
  utest evalSReadback v with Some (int_ 3) using eq else toString in
  utest callstackPop (deref csr) with None () in
  ()
else ());

-- Recursive let: exercises RecLetsEvalS's `Some cs` branch specifically.
let countN = nameSym "count" in
let nArgN = nameSym "n" in
let infoCall = mkInfo 1003 in
let recBody =
  if_ (leqi_ (nvar_ nArgN) (int_ 0))
    (int_ 0)
    (tmApp infoCall tyunknown_ (nvar_ countN) (subi_ (nvar_ nArgN) (int_ 1)))
in
let decl = nreclets_ [(countN, tyunknown_, nulam_ nArgN recBody)] in
let term = bind_ decl (tmApp infoCall tyunknown_ (nvar_ countN) (int_ 5)) in
(match callstackInit 8 with Some cs0 then
  let csr = ref cs0 in
  let v = evalSStageExpr (Some csr) (symbolize term) env in
  utest evalSReadback v with Some (int_ 0) using eq else toString in
  utest callstackPop (deref csr) with None () in
  ()
else ());

-- Direct nesting test: evalSStageExpr-driven tests above can only observe
-- callstack state before/after a *complete* top-level evaluation, since
-- interpreted MExpr has no way to peek at the host evaluator's Callstack
-- mid-call. Build closures directly via clsUsingCallstack instead, so the
-- innermost one's body can inspect the callstack while the outer call is still
-- in flight.
let csr =
  ref (optionGetOrElse (lam. error "callstack init failed") (callstackInit 8))
in
let observed = ref [] in
let dInfoA = mkInfo 2001 in
let dInfoB = mkInfo 2002 in
let innerCls =
  clsUsingCallstack csr
    (lam val. modref observed (callstackToSeq (deref csr)); val) in
let outerCls =
  clsUsingCallstack csr (lam val. applyS (dInfoB, innerCls, val)) in
let result = applyS (dInfoA, outerCls, VInt 0) in
utest deref observed with [dInfoB, dInfoA] in
utest evalSReadback result with Some (int_ 0) using eq else toString in

()
