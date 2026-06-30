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
  sem readback =| _ -> error "Unsupported Val in readback!"

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

lang AppEvalF = EvalF + AppAst
  sem mkEvalF =
  | TmApp r ->
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
  syn Val =
  | VConst1 (Const, Val -> Val)
  | VConst2 (Const, Val -> Val -> Val)

  sem readback =
  | VConst1 (c, _) | VConst2 (c, _) -> Some(TmConst
    { val = c, ty = TyUnknown { info = NoInfo () }, info = NoInfo () })

  sem mkEvalF =
  | TmConst r -> let val = mkDeltaF r.val in lam. val

  sem applyF =
  | (VConst1 (_, f), val) -> f val
  | (VConst2 (c, f), val) -> VConst1 (c, f val)

  sem mkDeltaF : Const -> Val
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
  syn Val =
  | VConApp (Int, Val)

  sem mkEvalF =
  | TmConApp r ->
    let body = mkEvalF r.body in
    match nameGetSym r.ident with Some s then
      let s = sym2hash s in
      lam env. VConApp (s, body env)
    else error "Unsymbolized TmConApp in mkEvalF!"

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
  CmpIntEvalF + CharEvalF + SysEvalF +

  -- Patterns
  NamedPatEvalF + BoolPatEval + RecordPatEval
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
