include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
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

lang RecordEvalF = EvalF + RecordAst + UnknownTypeAst
  syn Val =
  | VRecord (Map SID Val)

  sem readback =
  | VRecord bindings ->
    optionMap
      (lam bindings.
        TmRecord { bindings = bindings
                 , ty = TyUnknown { info = NoInfo () }
                 , info = NoInfo ()
                 })
      (mapFoldlOption
        (lam acc. lam k. lam v.
          match readback v with Some e then Some (mapInsert k e acc)
          else None ())
        (mapEmpty cmpSID)
        bindings)

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
        TmSeq { tms = tms
              , ty = TyUnknown { info = NoInfo () }
              , info = NoInfo ()
              })
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

let nameGetSymOrGetFreshSym = lam n.
  match nameGetSym n with Some s then s else gensym ()

lang LetEvalF = EvalF + LetDeclAst
  sem mkEvalDeclF =
  | DeclLet r ->
    -- NOTE(oerikss, 2026-09-16): We assume here that unsymbolized let bindings
    -- are not referred to en the rest of the code. This can appear for example
    -- in generated code that involves sequencing of expressions.
    let s = sym2hash (nameGetSymOrGetFreshSym r.ident) in
    let body = mkEvalF r.body in
    lam env. Cons ((s, body env), env)
end

lang RecLetsEval = EvalF + RecLetsDeclAst + LamEvalF
  sem mkEvalDeclF =
  | DeclRecLets r ->
    let ts =
      map
        (lam b.
          match b.body with TmLam r then
            -- NOTE(oerikss, 2026-09-16): We assume here that unsymbolized let
            -- bindings are not referred to en the rest of the code.
            let s1 = sym2hash (nameGetSymOrGetFreshSym b.ident) in
            let s2 = sym2hash (nameGetSymOrGetFreshSym r.ident) in
            let body = mkEvalF r.body in
            (s1, lam env. lam val. body (Cons ((s2, val), env)))
          else
            errorSingle [infoTm b.body]
              "Right-hand side of recursive let must be a lambda")
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

lang UtestEvalF = EvalF + UtestDeclAst
  sem mkEvalDeclF =
  | DeclUtest r ->
    warnSingle [r.info] "Skipping evaluation of utest";
    lam env. env
end

lang ExtEvalF = EvalF + ExtDeclAst
  sem mkEvalDeclF =
  | DeclExt r ->
    warnSingle [r.info]
      (concat "Skipping external declaration for: " (nameGetStr r.ident));
    lam env. env
end

lang PlaceholderEvalF = EvalF + PlaceholderAst + UnknownTypeAst
  syn Val =
  | VPlaceholder {}

  sem readback =
  | VPlaceholder _ -> Some
    (TmPlaceholder { ty = TyUnknown { info = NoInfo () }, info = NoInfo () })

  sem mkEvalF =
  | TmPlaceholder _ -> lam env. VPlaceholder {}
end

lang OpaqueEvalF = EvalF + OpaqueAst
  sem mkEvalF =
  | TmOpaque r -> mkEvalF r.body
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

lang ShiftIntEvalF = ConstEvalF + IntEvalF + ShiftIntAst
  sem mkDeltaF =
  | c & CSlli _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (slli x y))
  | c & CSrli _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (srli x y))
  | c & CSrai _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VInt (srai x y))
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
    (c, lam x. lam y. match (x, y) with (VChar x, VChar y) in VBool (eqc x y))
end

lang IntCharConversionEvalF =
  ConstEvalF + CharEvalF + IntEvalF + IntCharConversionAst

  sem mkDeltaF =
  | c & CInt2Char _ -> VConst1
    (c, lam x. match x with VInt x in VChar (int2char x))
  | c & CChar2Int _ -> VConst1
    (c, lam x. match x with VChar x in VInt (char2int x))
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

lang CmpFloatEvalF = ConstEvalF + FloatEvalF + BoolEvalF + CmpFloatAst
  sem mkDeltaF =
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

lang FloatIntConversionEvalF =
  ConstEvalF + FloatEvalF + IntEvalF + FloatIntConversionAst

  sem mkDeltaF =
  | c & CFloorfi _ -> VConst1
    (c, lam x. match x with VFloat x in VInt (floorfi x))
  | c & CCeilfi _ -> VConst1
    (c, lam x. match x with VFloat x in VInt (ceilfi x))
  | c & CRoundfi _ -> VConst1
    (c, lam x. match x with VFloat x in VInt (roundfi x))
  | c & CInt2float _ -> VConst1
    (c, lam x. match x with VInt x in VFloat (int2float x))
end

----------------------------
-- SEQUENCE OPERATIONS --
----------------------------

lang SeqOpEvalF =
  ConstEvalF + SeqEvalF + IntEvalF + BoolEvalF + RecordEvalF + SeqOpAst

  sem mkDeltaF =
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
          [(stringToSid "0", VSeq l), (stringToSid "1", VSeq r)]))
  | c & CSet _ -> VConst3
    (c, lam s. lam i. lam v.
      match (s, i) with (VSeq s, VInt i) in VSeq (set s i v))
  | c & CSubsequence _ -> VConst3
    (c, lam s. lam o. lam n.
      match (s, o, n) with (VSeq s, VInt o, VInt n) in
      VSeq (subsequence s o n))

  -- Higher order
  | c & CMap _ -> VConst2
    (c, lam f. lam s.
      match s with VSeq s in VSeq (map (lam x. applyF (f, x)) s))
  | c & CMapi _ -> VConst2
    (c, lam f. lam s.
      match s with VSeq s in
      VSeq (mapi (lam i. lam x. applyF (applyF (f, VInt i), x)) s))
  | c & CIter _ -> VConst2
    (c, lam f. lam s.
      match s with VSeq s in
      iter (lam x. applyF (f, x); ()) s;
      VRecord (mapEmpty cmpSID))
  | c & CIteri _ -> VConst2
    (c, lam f. lam s.
      match s with VSeq s in
      iteri (lam i. lam x. applyF (applyF (f, VInt i), x); ()) s;
      VRecord (mapEmpty cmpSID))
  | c & CCreate _ -> VConst2
    (c, lam n. lam f.
      match n with VInt n in VSeq (create n (lam i. applyF (f, VInt i))))
  | c & CCreateList _ -> VConst2
    (c, lam n. lam f.
      match n with VInt n in VSeq (createList n (lam i. applyF (f, VInt i))))
  | c & CCreateRope _ -> VConst2
    (c, lam n. lam f.
      match n with VInt n in VSeq (createRope n (lam i. applyF (f, VInt i))))
  | c & CFoldl _ -> VConst3
    (c, lam f. lam acc. lam s.
      match s with VSeq s in
      foldl (lam acc. lam x. applyF (applyF (f, acc), x)) acc s)
  | c & CFoldr _ -> VConst3
    (c, lam f. lam acc. lam s.
      match s with VSeq s in
      foldr (lam x. lam acc. applyF (applyF (f, x), acc)) acc s)
end

lang StringConvEvalF = SeqEvalF + CharEvalF
  sem valToString : Val -> String
  sem valToString =
  | VSeq vals -> map (lam v. match v with VChar c in c) vals

  sem stringToVal : String -> Val
  sem stringToVal =
  | s -> VSeq (map (lam c. VChar c) s)
end

lang SysEvalF = ConstEvalF + IntEvalF + StringConvEvalF + SysAst
  sem mkDeltaF =
  | c & CExit _ -> VConst1 (c, lam x. match x with VInt x in exit x)
  | c & CError _ -> VConst1 (c, lam s. error (valToString s))
  | CArgv _ -> VSeq (map stringToVal argv)
  | c & CCommand _ -> VConst1 (c, lam s. VInt (command (valToString s)))
  | c & CExec _ -> VConst2
    (c, lam p. lam args.
      match args with VSeq args in
      exec (valToString p) (map valToString args))
end

lang SymbEvalF = ConstEvalF + IntEvalF + SymbAst
  sem mkDeltaF =
  | c & CGensym _ -> VConst1 (c, lam. VInt (sym2hash (gensym ())))
  | c & CSym2hash _ -> VConst1 (c, lam x. match x with VInt _ in x)
end

lang CmpSymbEvalF = ConstEvalF + SymbEvalF + BoolEvalF + CmpSymbAst
  sem mkDeltaF =
  | c & CEqsym _ -> VConst2
    (c, lam x. lam y. match (x, y) with (VInt x, VInt y) in VBool (eqi x y))
end

lang ConTagEvalF = ConstEvalF + DataEvalF + IntEvalF + ConTagAst
  sem mkDeltaF =
  | c & CConstructorTag _ -> VConst1
    (c, lam v. match v with VConApp (tag, _) in VInt tag)
end

lang FloatStringConversionEvalF =
  ConstEvalF + BoolEvalF + FloatEvalF + StringConvEvalF +
  FloatStringConversionAst

  sem mkDeltaF =
  | c & CStringIsFloat _ ->
    VConst1 (c, lam s. VBool (stringIsFloat (valToString s)))
  | c & CString2float _ ->
    VConst1 (c, lam s. VFloat (string2float (valToString s)))
  | c & CFloat2string _ -> VConst1
    (c, lam x. match x with VFloat f in stringToVal (float2string f))
end

lang FileOpEvalF =
  ConstEvalF + BoolEvalF + RecordEvalF + StringConvEvalF + FileOpAst

  sem mkDeltaF =
  | c & CFileRead _ -> VConst1
    (c, lam f. stringToVal (readFile (valToString f)))
  | c & CFileWrite _ -> VConst2
    (c, lam f. lam d.
      writeFile (valToString f) (valToString d); VRecord (mapEmpty cmpSID))
  | c & CFileExists _ -> VConst1 (c, lam f. VBool (fileExists (valToString f)))
  | c & CFileDelete _ -> VConst1
    (c, lam f. deleteFile (valToString f); VRecord (mapEmpty cmpSID))
end

lang IOEvalF = ConstEvalF + RecordEvalF + StringConvEvalF + IOAst
  sem mkDeltaF =
  | c & CPrint _ -> VConst1
    (c, lam s. print (valToString s); VRecord (mapEmpty cmpSID))
  | c & CPrintError _ -> VConst1
    (c, lam s. printError (valToString s); VRecord (mapEmpty cmpSID))
  | c & CDPrint _ -> VConst1 (c, lam. VRecord (mapEmpty cmpSID))
  | c & CFlushStdout _ -> VConst1
    (c, lam. flushStdout (); VRecord (mapEmpty cmpSID))
  | c & CFlushStderr _ -> VConst1
    (c, lam. flushStderr (); VRecord (mapEmpty cmpSID))
  | c & CReadLine _ -> VConst1 (c, lam. stringToVal (readLine ()))
  | c & CReadBytesAsString _ -> VConst1
    (c, lam. error "CReadBytesAsString: unimplemented")
end

lang RandomNumberGeneratorEvalF =
  ConstEvalF + IntEvalF + RecordEvalF + RandomNumberGeneratorAst

  sem mkDeltaF =
  | c & CRandIntU _ -> VConst2
    (c, lam lo. lam hi.
          match (lo, hi) with (VInt lo, VInt hi) in VInt (randIntU lo hi))
  | c & CRandSetSeed _ -> VConst1
    (c, lam n. match n with VInt n in randSetSeed n; VRecord (mapEmpty cmpSID))
end

lang TimeEvalF = ConstEvalF + IntEvalF + FloatEvalF + RecordEvalF + TimeAst
  sem mkDeltaF =
  | c & CWallTimeMs _ -> VConst1 (c, lam. VFloat (wallTimeMs ()))
  | c & CSleepMs _ -> VConst1
    (c, lam n. match n with VInt n in sleepMs n; VRecord (mapEmpty cmpSID))
end

lang RefOpEvalF = ConstEvalF + RecordEvalF + RefOpAst
  syn Val =
  | VRef (Ref Val)

  sem readback =
  | VRef _ -> None ()

  sem mkDeltaF =
  | c & CRef _ -> VConst1 (c, lam v. VRef (ref v))
  | c & CModRef _ -> VConst2
    (c, lam r. lam v.
          match r with VRef r in modref r v; VRecord (mapEmpty cmpSID))
  | c & CDeRef _ -> VConst1 (c, lam r. match r with VRef r in deref r)
end

lang TypeOpEvalF = ConstEvalF + TypeOpAst
  sem mkDeltaF =
  | c & CTypeOf _ -> VConst1 (c, lam. error "CTypeOf: unimplemented")
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

lang DataPatEvalF = MatchEvalF + DataEvalF + DataPat
  sem mkTryMatch =
  | PatCon r ->
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      let subpat = mkTryMatch r.subpat in
      lam val. lam env.
        match val with VConApp (c, arg) then
          if eqi c s then subpat arg env
          else None ()
        else None ()
    else error "Unsymbolized PatCon in mkTryMatch!"
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

lang AndPatEvalF = MatchEvalF + AndPat
  sem mkTryMatch =
  | PatAnd r ->
    let lpat = mkTryMatch r.lpat in
    let rpat = mkTryMatch r.rpat in
    lam val. lam env.
      match lpat val env with Some env then rpat val env
      else None ()
end

lang OrPatEvalF = MatchEvalF + OrPat
  sem mkTryMatch =
  | PatOr r ->
    let lpat = mkTryMatch r.lpat in
    let rpat = mkTryMatch r.rpat in
    lam val. lam env.
      match lpat val env with Some env then Some env else rpat val env
end

lang NotPatEvalF = MatchEvalF + NotPat
  sem mkTryMatch =
  | PatNot r ->
    let subpat = mkTryMatch r.subpat in
    lam val. lam env.
      match subpat val env with Some _ then None () else Some env
end

------------------
-- COMPOSITIONS --
------------------

-- Missing, relative to `MExprAst` in `ast.mc`:
--
-- * Constants: TensorOpAst and BootParserAst.
--
-- Types and kinds are not evaluated, so nothing is missing there.

lang MExprEvalF =
  -- Terms and Decls
  VarEvalF + AppEvalF + LamEvalF + DeclEvalF + ConstEvalF + MatchEvalF +
  RecordEvalF + SeqEvalF + NeverEvalF + DataEvalF + UtestEvalF + ExtEvalF +
  PlaceholderEvalF + OpaqueEvalF +

  -- Decls
  LetEvalF + RecLetsEval + TypeEvalF +

  -- Constants
  UnsafeCoerceEvalF + IntEvalF + ArithIntEvalF + ShiftIntEvalF +  BoolEvalF +
  CmpIntEvalF + CharEvalF + CmpCharEvalF + IntCharConversionEvalF +
  FloatEvalF + ArithFloatEvalF + CmpFloatEvalF +
  FloatIntConversionEvalF + SeqOpEvalF + StringConvEvalF + SysEvalF +
  SymbEvalF + CmpSymbEvalF + ConTagEvalF + FloatStringConversionEvalF +
  FileOpEvalF + IOEvalF + RandomNumberGeneratorEvalF + TimeEvalF +
  RefOpEvalF + TypeOpEvalF +

  -- Patterns
  NamedPatEvalF + BoolPatEval + RecordPatEval + SeqTotPatEvalF +
  SeqEdgePatEvalF + DataPatEvalF + IntPatEvalF + CharPatEvalF +
  AndPatEvalF + OrPatEvalF + NotPatEvalF
end

lang TestLang = MExprEvalF + MExprEq + MExprPrettyPrint + MExprSym end

mexpr

use TestLang in

let toString =
  let toString = optionMapOr "None" expr2str in
  utestDefaultToString toString toString in

let eq = optionEq eqExpr in

let env : EvalFEnv = Nil () in

let eval : Expr -> Val = lam e. mkEvalF (symbolize e) env in

utest readback (eval (app_ (ulam_ "x" (var_ "x")) (int_ 0)))
with Some (int_ 0) using eq else toString in

utest readback (eval (app_ (ulam_ "x" (addi_ (var_ "x") (int_ 2))) (int_ 1)))
with Some (int_ 3) using eq else toString in

-----------------------------------------------
-- UNIT TESTS FOR THE NEW CONSTANT FRAGMENTS  --
-- (one section per `lang ...EvalF` fragment) --
-----------------------------------------------

-- SymbEvalF

-- `sym2hash` on an already-hash-represented symbol is a no-op.
utest
  readback
    (eval (bindall_ [ulet_ "s" (gensym_ uunit_)]
      (eqi_ (var_ "s") (sym2hash_ (var_ "s")))))
with Some true_ using eq else toString in

-- Reading the same binding's hash twice gives the same value.
utest
  readback
    (eval (bindall_ [ulet_ "s" (gensym_ uunit_)]
      (eqi_ (sym2hash_ (var_ "s")) (sym2hash_ (var_ "s")))))
with Some true_ using eq else toString in

-- Two separate `gensym`s are (almost certainly) distinct.
utest
  readback
    (eval (bindall_ [ulet_ "s1" (gensym_ uunit_), ulet_ "s2" (gensym_ uunit_)]
      (eqi_ (var_ "s1") (var_ "s2"))))
with Some false_ using eq else toString in

-- CmpSymbEvalF

utest
  readback
    (eval (bindall_ [ulet_ "s" (gensym_ uunit_)]
      (eqsym_ (var_ "s") (var_ "s"))))
with Some true_ using eq else toString in

utest
  readback
    (eval (bindall_ [ulet_ "s1" (gensym_ uunit_), ulet_ "s2" (gensym_ uunit_)]
      (eqsym_ (var_ "s1") (var_ "s2"))))
with Some false_ using eq else toString in

-- ConTagEvalF

let constructorTag_ = lam e. app_ (uconst_ (CConstructorTag ())) e in

-- Same constructor -> same tag, regardless of its argument.
utest
  readback
    (eval (bindall_ [ucondef_ "Foo", ucondef_ "Bar"]
      (eqi_
        (constructorTag_ (conapp_ "Foo" (int_ 0)))
        (constructorTag_ (conapp_ "Foo" (int_ 1))))))
with Some true_ using eq else toString in

-- Different constructors -> different tags.
utest
  readback
    (eval (bindall_ [ucondef_ "Foo", ucondef_ "Bar"]
      (eqi_
        (constructorTag_ (conapp_ "Foo" (int_ 0)))
        (constructorTag_ (conapp_ "Bar" (int_ 0))))))
with Some false_ using eq else toString in

-- FloatStringConversionEvalF

utest readback (eval (string2float_ (str_ "1.5")))
with Some (float_ 1.5) using eq else toString in

utest readback (eval (float2string_ (float_ 1.5)))
with Some (str_ "1.5") using eq else toString in

utest readback (eval (stringIsfloat_ (str_ "1.5")))
with Some true_ using eq else toString in

utest readback (eval (stringIsfloat_ (str_ "abc")))
with Some false_ using eq else toString in

-- FileOpEvalF

-- The scratch path is computed as an ordinary host-level string (this outer
-- `mexpr` block is run by the real evaluator, unrestricted), then spliced in
-- as a literal -- `readFile_`/`writeFile_`/etc. themselves stay inside the
-- fast evaluator's supported subset. Suffixed with a fresh symbol's hash so
-- repeated runs (or a run alongside other test suites) never collide.
let scratchFile =
  concat "/tmp/eval-fast-test-" (int2string (sym2hash (gensym ()))) in

utest
  readback
    (eval (bindall_ [ulet_ "_" (writeFile_ (str_ scratchFile) (str_ "hello"))]
      (readFile_ (str_ scratchFile))))
with Some (str_ "hello") using eq else toString in

utest readback (eval (fileExists_ (str_ scratchFile)))
with Some true_ using eq else toString in

utest
  readback
    (eval (bindall_ [ulet_ "_" (deleteFile_ (str_ scratchFile))]
      (fileExists_ (str_ scratchFile))))
with Some false_ using eq else toString in

-- IOEvalF

utest readback (eval (print_ (str_ "eval-fast.mc: IOEvalF test\n")))
with Some uunit_ using eq else toString in

utest readback (eval (printError_ (str_ "eval-fast.mc: IOEvalF test (stderr)\n")))
with Some uunit_ using eq else toString in

utest readback (eval (flushStdout_ uunit_)) with Some uunit_ using eq else toString in
utest readback (eval (flushStderr_ uunit_)) with Some uunit_ using eq else toString in
utest readback (eval (dprint_ (int_ 42))) with Some uunit_ using eq else toString in

-- `CReadLine`/`CReadBytesAsString` are not exercised here: the former would
-- block on stdin (nothing is piped into this test run), and the latter has
-- no runtime semantics -- see the `IOEvalF` fragment's comment above.

-- RandomNumberGeneratorEvalF

utest
  readback
    (eval
      (bindall_
        [ ulet_ "_" (randSetSeed_ (int_ 42))
        , ulet_ "n" (randIntU_ (int_ 10) (int_ 20)) ]
        (and_ (geqi_ (var_ "n") (int_ 10)) (lti_ (var_ "n") (int_ 20)))))
with Some true_ using eq else toString in

-- TimeEvalF

utest readback (eval (geqf_ (wallTimeMs_ uunit_) (float_ 0.0)))
with Some true_ using eq else toString in

utest readback (eval (sleepMs_ (int_ 0))) with Some uunit_ using eq else toString in

-- RefOpEvalF

utest
  readback
    (eval
      (bindall_
        [ ulet_ "r1" (ref_ (int_ 1))
        , ulet_ "r2" (ref_ (float_ 2.0)) ]
        (utuple_ [deref_ (var_ "r1"), deref_ (var_ "r2")])))
with Some (utuple_ [int_ 1, float_ 2.0]) using eq else toString in

utest
  readback
    (eval
      (bindall_
        [ ulet_ "r" (ref_ (int_ 1))
        , ulet_ "_" (modref_ (var_ "r") (int_ 2)) ]
        (deref_ (var_ "r"))))
with Some (int_ 2) using eq else toString in

-- SysEvalF (remaining constants)

-- `CError`, `CArgv`, `CCommand`, and `CExec` are implemented (see the
-- `SysEvalF` fragment above) but deliberately not invoked in a live `utest`
-- here: `CError` halts the whole program, `CArgv`'s value depends on how
-- this file itself was invoked, `CCommand` shells out (unreliable across
-- platforms/CI), and `CExec` replaces the current process image
-- (`Unix.execvp`) and would kill this very test run.

-- TypeOpEvalF

-- `CTypeOf` is not invoked here since it always errors -- see the
-- `TypeOpEvalF` fragment above.

()
