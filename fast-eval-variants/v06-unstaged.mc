-- STRATEGY: walk the AST on every step instead of pre-building closures.
--
-- The baseline is staged: `mkEvalF` traverses the AST once and returns a
-- closure, so the shape of the program is decided before evaluation starts and
-- the running program never looks at an `Expr` again.  This variant is the
-- ordinary alternative -- a recursive `evalF env expr` that matches on the AST
-- node every time it reaches one.
--
-- The work that moves from build time to run time is: matching the AST node,
-- reading `nameGetSym`/`sym2hash` out of every variable, lambda and pattern,
-- and rebuilding the delta closure for every constant occurrence.  Everything
-- else -- the environment representation, the key type, the value type -- is
-- identical to the baseline, so the difference is the staging alone.

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

lang EvalF = Ast
  syn Val =
  | VError (Info, String)

  sem readback : Val -> Option Expr
  sem readback =| _ -> error "Unsupported Val in readback!"

  type EvalFEnv = List (Int, Val)

  sem evalFEnvLookup : Int -> EvalFEnv -> Val
  sem evalFEnvLookup s1 =
  | Nil _ -> error "env lookup failed!"
  | Cons ((s2, val), env) -> if eqi s1 s2 then val else evalFEnvLookup s1 env

  sem evalF : EvalFEnv -> Expr -> Val
  sem evalF env =| _ -> error "Unsupported Expr in evalF!"

  sem evalDeclF : EvalFEnv -> Decl -> EvalFEnv
  sem evalDeclF env =| _ -> error "Unsupported Decl in evalDeclF!"
end

---------------------
-- TERMS AND DECLS --
---------------------

lang VarEvalF = EvalF + VarAst
  sem evalF env =
  | TmVar r ->
    match nameGetSym r.ident with Some s1 then
      evalFEnvLookup (sym2hash s1) env
    else error "Unsymbolized TmVar in evalF!"
end

lang AppEvalF = EvalF + AppAst
  sem evalF env =
  | TmApp r -> applyF (evalF env r.lhs, evalF env r.rhs)

  -- Fusing saturated constant applications, the baseline's optimisation,
  -- cannot be carried over: it happens while compiling, and this evaluator
  -- never compiles.
  sem applyF : (Val, Val) -> Val
end

lang LamEvalF = AppEvalF + LamAst
  syn Val =
  | VCls (Val -> Val)

  sem readback =
  | VCls _ -> None ()

  sem evalF env =
  | TmLam r ->
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      VCls (lam val. evalF (Cons ((s, val), env)) r.body)
    else error "Unsymbolized TmLam in evalF!"

  sem applyF =
  | (VCls cls, val) -> cls val
end

lang DeclEvalF = EvalF + DeclAst
  sem evalF env =
  | TmDecl r -> evalF (evalDeclF env r.decl) r.inexpr
end

lang ConstEvalF = AppEvalF + ConstAst + UnknownTypeAst
  syn Val =
  | VConst1 (Const, Val -> Val)
  | VConst2 (Const, Val -> Val -> Val)
  | VConst3 (Const, Val -> Val -> Val -> Val)

  sem readback =
  | VConst1 (c, _) | VConst2 (c, _) | VConst3 (c, _) -> Some(TmConst
    { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })

  sem evalF env =
  | TmConst r -> mkDeltaF r.val

  sem applyF =
  | (VConst1 (_, f), val) -> f val
  | (VConst2 (c, f), val) -> VConst1 (c, f val)
  | (VConst3 (c, f), val) -> VConst2 (c, f val)

  sem mkDeltaF : Const -> Val
  sem mkDeltaF =| _ -> error "Unsupported Const in mkDeltaF!"
end

lang MatchEvalF = EvalF + MatchAst
  sem evalF env =
  | TmMatch r ->
    match tryMatchF (evalF env r.target) env r.pat with Some env then
      evalF env r.thn
    else evalF env r.els

  sem tryMatchF : Val -> EvalFEnv -> Pat -> Option EvalFEnv
  sem tryMatchF val env =| _ -> error "Unsupported Pat in tryMatchF!"
end

lang RecordEvalF = EvalF + RecordAst
  syn Val =
  | VRecord (Map SID Val)

  sem evalF env =
  | TmRecord r -> VRecord (mapMap (lam e. evalF env e) r.bindings)
  | TmRecordUpdate r ->
    match evalF env r.rec with VRecord rec then
      VRecord (mapInsert r.key (evalF env r.value) rec)
    else error "TmRecord type error in evalF!"
end

lang SeqEvalF = EvalF + SeqAst + UnknownTypeAst
  syn Val =
  | VSeq [Val]

  sem readback =
  | VSeq vals ->
    optionMap
      (lam tms.
        TmSeq { tms = tms, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })
      (optionMapM readback vals)

  sem evalF env =
  | TmSeq r -> VSeq (map (lam e. evalF env e) r.tms)
end

lang NeverEvalF = EvalF + NeverAst
  sem evalF env =
  | TmNever r ->
    errorSingle [r.info]
      "Reached a never term, which should be impossible in a well-typed program."
end

lang LetEvalF = EvalF + LetDeclAst
  sem evalDeclF env =
  | DeclLet r ->
    match nameGetSym r.ident with Some s then
      Cons ((sym2hash s, evalF env r.body), env)
    else error "Unsymbolized DeclLet in evalDeclF!"
end

lang RecLetsEval = EvalF + RecLetsDeclAst + LamEvalF
  sem evalDeclF env =
  | DeclRecLets r ->
    recursive let reclet = lam env.
      foldl
        (lam acc. lam b.
          match b.body with TmLam l then
            match (nameGetSym b.ident, nameGetSym l.ident) with
              (Some s1, Some s2) then
              let s1 = sym2hash s1 in
              let s2 = sym2hash s2 in
              Cons
                ( ( s1
                  , VCls
                      (lam val.
                        evalF (Cons ((s2, val), reclet env)) l.body) )
                , acc )
            else error "Unsymbolized DeclRecLets in evalDeclF!"
          else error "Right-hand side of recursive let must be a lambda")
        env
        r.bindings
    in
    reclet env
end

lang TypeEvalF = EvalF + TypeDeclAst
  sem evalDeclF env =
  | DeclType _ -> env
end

lang DataEvalF = EvalF + DataAst + DataDeclAst
  syn Val =
  | VConApp (Int, Val)

  sem evalF env =
  | TmConApp r ->
    match nameGetSym r.ident with Some s then
      VConApp (sym2hash s, evalF env r.body)
    else error "Unsymbolized TmConApp in evalF!"

  sem evalDeclF env =
  | DeclConDef _ -> env
end

---------------
-- CONSTANTS --
---------------

lang UnsafeCoerceEvalF = ConstEvalF + UnsafeCoerceAst
  sem mkDeltaF =
  | c & CUnsafeCoerce _ -> VConst1 (c, lam x. x)
end

lang IntEvalF = ConstEvalF + IntAst + UnknownTypeAst
  syn Val =
  | VInt Int

  sem readback =
  | VInt n -> Some ( TmConst
    { val = CInt { val = n }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem mkDeltaF =
  | CInt r -> VInt r.val
end

lang ArithIntEvalF = ConstEvalF + IntEvalF + ArithIntAst
  sem mkDeltaF =
  | c & CAddi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (addi x y))
  | c & CSubi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (subi x y))
  | c & CMuli _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (muli x y))
  | c & CDivi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (divi x y))
  | c & CModi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (modi x y))
  | c & CNegi _ -> VConst1
    (c , lam x. match x with VInt x in VInt (negi x))
end

lang ShiftIntEvalF = ConstEvalF + IntEvalF + ShiftIntAst
  sem mkDeltaF =
  | c & CSlli _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (slli x y))
  | c & CSrli _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (srli x y))
  | c & CSrai _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (srai x y))
end

lang BoolEvalF = ConstEvalF + BoolAst + UnknownTypeAst
  syn Val =
  | VBool Bool

  sem readback =
  | VBool b -> Some( TmConst
    { val = CBool { val = b }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem mkDeltaF =
  | CBool r -> VBool r.val
end

lang CmpIntEvalF =
  ConstEvalF +  IntEvalF + BoolEvalF + CmpIntAst

  sem mkDeltaF =
  | c & CEqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (eqi x y))
  | c & CNeqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (neqi x y))
  | c & CLti _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (lti x y))
  | c & CGti _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (gti x y))
  | c & CLeqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (leqi x y))
  | c & CGeqi _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (geqi x y))
end

lang CharEvalF = ConstEvalF + CharAst + UnknownTypeAst
  syn Val =
  | VChar Char

  sem readback =
  | VChar c -> Some( TmConst
    { val = CChar { val = c }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem mkDeltaF =
  | CChar r -> VChar r.val
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
    (c , lam x. lam y. match (x, y) with (VChar x, VChar y) in VBool (eqc x y))
end

lang IntCharConversionEvalF =
  ConstEvalF + CharEvalF + IntEvalF + IntCharConversionAst

  sem mkDeltaF =
  | c & CInt2Char _ -> VConst1
    (c , lam x. match x with VInt x in VChar (int2char x))
  | c & CChar2Int _ -> VConst1
    (c , lam x. match x with VChar x in VInt (char2int x))
end

lang FloatEvalF = ConstEvalF + FloatAst + UnknownTypeAst
  syn Val =
  | VFloat Float

  sem readback =
  | VFloat f -> Some ( TmConst
    { val = CFloat { val = f }
    , ty = TyUnknown { info = NoInfo () }
    , info = NoInfo () } )

  sem mkDeltaF =
  | CFloat r -> VFloat r.val
end

lang ArithFloatEvalF = ConstEvalF + FloatEvalF + ArithFloatAst
  sem mkDeltaF =
  | c & CAddf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (addf x y))
  | c & CSubf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (subf x y))
  | c & CMulf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (mulf x y))
  | c & CDivf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VFloat (divf x y))
  | c & CNegf _ -> VConst1
    (c , lam x. match x with VFloat x in VFloat (negf x))
end

lang CmpFloatEvalF = ConstEvalF + FloatEvalF + BoolEvalF + CmpFloatAst
  sem mkDeltaF =
  | c & CEqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (eqf x y))
  | c & CNeqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (neqf x y))
  | c & CLtf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (ltf x y))
  | c & CGtf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (gtf x y))
  | c & CLeqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (leqf x y))
  | c & CGeqf _ -> VConst2
    (c , lam x. lam y. match (x, y) with (VFloat x, VFloat y) in VBool (geqf x y))
end

lang FloatIntConversionEvalF =
  ConstEvalF + FloatEvalF + IntEvalF + FloatIntConversionAst

  sem mkDeltaF =
  | c & CFloorfi _ -> VConst1
    (c , lam x. match x with VFloat x in VInt (floorfi x))
  | c & CCeilfi _ -> VConst1
    (c , lam x. match x with VFloat x in VInt (ceilfi x))
  | c & CRoundfi _ -> VConst1
    (c , lam x. match x with VFloat x in VInt (roundfi x))
  | c & CInt2float _ -> VConst1
    (c , lam x. match x with VInt x in VFloat (int2float x))
end

----------------------------
-- SEQUENCE OPERATIONS --
----------------------------

lang SeqOpEvalF =
  ConstEvalF + SeqEvalF + IntEvalF + BoolEvalF + RecordEvalF + SeqOpAst

  sem mkDeltaF =
  -- First order
  | c & CHead _ -> VConst1
    (c , lam s. match s with VSeq s in head s)
  | c & CTail _ -> VConst1
    (c , lam s. match s with VSeq s in VSeq (tail s))
  | c & CNull _ -> VConst1
    (c , lam s. match s with VSeq s in VBool (null s))
  | c & CLength _ -> VConst1
    (c , lam s. match s with VSeq s in VInt (length s))
  | c & CReverse _ -> VConst1
    (c , lam s. match s with VSeq s in VSeq (reverse s))
  | c & CIsList _ -> VConst1
    (c , lam s. match s with VSeq s in VBool (isList s))
  | c & CIsRope _ -> VConst1
    (c , lam s. match s with VSeq s in VBool (isRope s))
  | c & CGet _ -> VConst2
    (c , lam s. lam i. match (s, i) with (VSeq s, VInt i) in get s i)
  | c & CCons _ -> VConst2
    (c , lam v. lam s. match s with VSeq s in VSeq (cons v s))
  | c & CSnoc _ -> VConst2
    (c , lam s. lam v. match s with VSeq s in VSeq (snoc s v))
  | c & CConcat _ -> VConst2
    (c , lam s1. lam s2.
      match (s1, s2) with (VSeq s1, VSeq s2) in VSeq (concat s1 s2))
  | c & CSplitAt _ -> VConst2
    (c , lam s. lam i.
      match (s, i) with (VSeq s, VInt i) in
      match splitAt s i with (l, r) in
      VRecord
        (mapFromSeq cmpSID
          [(stringToSid "0", VSeq l), (stringToSid "1", VSeq r)]))
  | c & CSet _ -> VConst3
    (c , lam s. lam i. lam v.
      match (s, i) with (VSeq s, VInt i) in VSeq (set s i v))
  | c & CSubsequence _ -> VConst3
    (c , lam s. lam o. lam n.
      match (s, o, n) with (VSeq s, VInt o, VInt n) in
      VSeq (subsequence s o n))

  -- Higher order
  | c & CMap _ -> VConst2
    (c , lam f. lam s.
      match s with VSeq s in VSeq (map (lam x. applyF (f, x)) s))
  | c & CMapi _ -> VConst2
    (c , lam f. lam s.
      match s with VSeq s in
      VSeq (mapi (lam i. lam x. applyF (applyF (f, VInt i), x)) s))
  | c & CIter _ -> VConst2
    (c , lam f. lam s.
      match s with VSeq s in
      iter (lam x. applyF (f, x); ()) s;
      VRecord (mapEmpty cmpSID))
  | c & CIteri _ -> VConst2
    (c , lam f. lam s.
      match s with VSeq s in
      iteri (lam i. lam x. applyF (applyF (f, VInt i), x); ()) s;
      VRecord (mapEmpty cmpSID))
  | c & CCreate _ -> VConst2
    (c , lam n. lam f.
      match n with VInt n in VSeq (create n (lam i. applyF (f, VInt i))))
  | c & CCreateList _ -> VConst2
    (c , lam n. lam f.
      match n with VInt n in VSeq (createList n (lam i. applyF (f, VInt i))))
  | c & CCreateRope _ -> VConst2
    (c , lam n. lam f.
      match n with VInt n in VSeq (createRope n (lam i. applyF (f, VInt i))))
  | c & CFoldl _ -> VConst3
    (c , lam f. lam acc. lam s.
      match s with VSeq s in
      foldl (lam acc. lam x. applyF (applyF (f, acc), x)) acc s)
  | c & CFoldr _ -> VConst3
    (c , lam f. lam acc. lam s.
      match s with VSeq s in
      foldr (lam x. lam acc. applyF (applyF (f, x), acc)) acc s)
end

lang SysEvalF = ConstEvalF + IntEvalF + SysAst
  sem mkDeltaF =
  | c & CExit _ -> VConst1 (c, lam x. match x with VInt x in exit x)
end

--------------
-- PATTERNS --
--------------

lang NamedPatEvalF = MatchEvalF + NamedPat
  sem tryMatchF val env =
  | PatNamed {ident = PName name} ->
    match nameGetSym name with Some s then
      Some (Cons ((sym2hash s, val), env))
    else error "Unsymbolized PatNamed in tryMatchF!"
  | PatNamed {ident = PWildcard ()} -> Some env
end

lang BoolPatEval = MatchEvalF + BoolEvalF + BoolAst + BoolPat
  sem tryMatchF val env =
  | PatBool r ->
    match val with VBool b then
      match (b, r.val) with (true, true) | (false, false) then Some env
      else None ()
    else None ()
end

lang RecordPatEval = MatchEvalF + RecordEvalF + RecordAst + RecordPat
  sem tryMatchF val env =
  | PatRecord r ->
    match val with VRecord rbindings then
      mapFoldlOption
        (lam env. lam k. lam pat.
          match mapLookup k rbindings with Some val then tryMatchF val env pat
          else None ())
        env
        r.bindings
    else None ()
end

lang SeqTotPatEvalF = MatchEvalF + SeqEvalF + SeqTotPat
  sem tryMatchF val env =
  | PatSeqTot r ->
    match val with VSeq vals then
      if eqi (length vals) (length r.pats) then
        optionFoldlM
          (lam env. lam pv. match pv with (pat, v) in tryMatchF v env pat)
          env
          (zipWith (lam pat. lam v. (pat, v)) r.pats vals)
      else None ()
    else None ()
end

lang SeqEdgePatEvalF = MatchEvalF + SeqEvalF + SeqEdgePat
  sem tryMatchF val env =
  | PatSeqEdge r ->
    match val with VSeq vals then
      let npre = length r.prefix in
      let npost = length r.postfix in
      if geqi (length vals) (addi npre npost) then
        match splitAt vals npre with (pre, rest) in
        match splitAt rest (subi (length rest) npost) with (mid, post) in
        match
          optionFoldlM
            (lam env. lam pv. match pv with (pat, v) in tryMatchF v env pat)
            env
            (zipWith (lam pat. lam v. (pat, v))
               (concat r.prefix r.postfix) (concat pre post))
        with Some env then
          -- The middle binds the remaining subsequence, or is dropped for `_`.
          match r.middle with PName name then
            match nameGetSym name with Some s then
              Some (Cons ((sym2hash s, VSeq mid), env))
            else error "Unsymbolized PatSeqEdge in tryMatchF!"
          else Some env
        else None ()
      else None ()
    else None ()
end

lang IntPatEvalF = MatchEvalF + IntEvalF + IntPat
  sem tryMatchF val env =
  | PatInt r ->
    match val with VInt i then
      if eqi i r.val then Some env else None ()
    else None ()
end

lang CharPatEvalF = MatchEvalF + CharEvalF + CharPat
  sem tryMatchF val env =
  | PatChar r ->
    match val with VChar c then
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
  evalF (Nil ()) ast;
  ()
else
  printLn "usage: <runner> FILE.mc";
  exit 1
