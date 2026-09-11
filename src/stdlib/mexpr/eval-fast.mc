include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "utest.mc"
include "list.mc"
include "option.mc"

lang EvalF = Ast
  syn Val =
  | VError (Info, String)

  sem readback : Val -> Option Expr

  type EvalFEnv = List (Int, Val)

  sem evalFEnvLookup : Int -> EvalFEnv -> Val
  sem evalFEnvLookup s1 =
  | Nil _ -> error "env lookup failed!"
  | Cons ((s2, val), env) -> if eqi s1 s2 then val else evalFEnvLookup s1 env

  sem mkEvalF : Expr -> EvalFEnv -> Val

  sem mkEvalDeclF : Decl -> EvalFEnv -> EvalFEnv
end

---------------------
-- TERMS AND DECLS --
---------------------

lang VarEvalF = EvalF + VarAst
  sem mkEvalF =
  | TmVar r ->
    match nameGetSym r.ident with Some s1 then
      evalFEnvLookup (sym2hash s1)
    else errorSingle [r.info] "Unsymbolized TmVarin mkEvalF!"
end

lang AppEvalF = EvalF + AppAst + ConstAst + UnknownTypeAst
  syn Val =
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
  syn Val =
  | VCls (Val -> Val)

  sem readback =
  | VCls _ -> None ()

  sem mkEvalF =
  | TmLam r ->
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      let body = mkEvalF r.body in
      lam env. VCls (lam val. body (Cons ((s, val), env)))
    else errorSingle [r.info] "Unsymbolized TmLam in mkEvalF!"

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
end

lang RecordEvalF = EvalF + RecordAst
  syn Val =
  | VRecord (Map SID Val)

  sem mkEvalF =
  | TmRecord r ->
    let bindings = mapMap mkEvalF r.bindings in
    lam env. VRecord (mapMap (lam x. x env) bindings)
  | TmRecordUpdate r ->
    let rec = mkEvalF r.rec in
    let key = r.key in
    let value = mkEvalF r.value in
    lam env.
      match rec env with VRecord rec then VRecord (mapInsert key (value env) rec)
      else error "TmRecord type error in mkEvalF!"
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

  sem mkEvalF =
  | TmSeq r ->
    let vals = map mkEvalF r.tms in
    lam env. VSeq (map (lam x. x env) vals)
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
    else errorSingle [r.info] "Unsymbolized DeclLet in mkEvalDeclF!"
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
            else errorSingle [r.info] "Unsymbolized DeclRecLets in mkEvalDeclF!"
          else errorSingle [infoTm b.body] "Right-hand side of recursive let must be a lambda")
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
  syn Val =
  | VConApp (Int, Val)

  sem mkEvalF =
  | TmConApp r ->
    let body = mkEvalF r.body in
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      lam env. VConApp (s, body env)
    else errorSingle [r.info] "Unsymbolized TmConApp in mkEvalF!"

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
    match val with VBool b then
      match (b, r.val) with (true, true) | (false, false) then Some env
      else None ()
    else None ()
end

lang RecordPatEval = MatchEvalF + RecordEvalF + RecordAst + RecordPat
  sem mkTryMatch =
  | PatRecord r ->
    let pbindings = mapMap mkTryMatch r.bindings in
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

lang SeqTotPatEvalF = MatchEvalF + SeqEvalF + SeqTotPat
  sem mkTryMatch =
  | PatSeqTot r ->
    let pats = map mkTryMatch r.pats in
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
          lam vals. lam env. Some (Cons ((s, VSeq vals), env))
        else error "Unsymbolized PatSeqEdge in mkTryMatch!"
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

lang IntPatEvalF = MatchEvalF + IntEvalF + IntPat
  sem mkTryMatch =
  | PatInt r -> lam val. lam env.
    match val with VInt i then
      if eqi i r.val then Some env else None ()
    else None ()
end

lang CharPatEvalF = MatchEvalF + CharEvalF + CharPat
  sem mkTryMatch =
  | PatChar r -> lam val. lam env.
    match val with VChar c then
      if eqc c r.val then Some env else None ()
    else None ()
end

------------------
-- COMPOSITIONS --
------------------

-- Missing, relative to `MExprAst` in `ast.mc`:
--
-- * Terms: TmPlaceholder, TmOpaque.
-- * Decls: DeclUtest, DeclExt.
-- * Constants: SymbAst, CmpSymbAst, FloatStringConversionAst, FileOpAst,
--   IOAst, RandomNumberGeneratorAst, TimeAst, ConTagAst, RefOpAst, TypeOpAst,
--   TensorOpAst and BootParserAst.  SysAst is only partially covered: CExit
--   has a delta function, CError, CArgv, CCommand and CExec do not.
-- * Patterns: PatCon, PatAnd, PatOr and PatNot.  DataEvalF can thus build a
--   constructor, but nothing can take one apart.
--
-- Types and kinds are not evaluated, so nothing is missing there.

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

lang TestLang = MExprEvalF + MExprEq + MExprPrettyPrint end

mexpr

use TestLang in

let toString =
  let toString = optionMapOr "None" expr2str in
  utestDefaultToString toString toString in

let eq = optionEq eqExpr in

let env = evalFEnvEmpty () in

let eval = mkEvalF (app_ (ulam_ "x" (var_ "x")) (int_ 0)) in
utest readback (eval env) with Some (int_ 0) using eq else toString in

let eval = mkEvalF (app_ (ulam_ "x" (addi_ (var_ "x") (int_ 2))) (int_ 1)) in
utest readback (eval env) with Some (int_ 3) using eq else toString in

()
