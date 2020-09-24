-- Alpha equivalence for closed MExpr terms. Supports both non-symbolized and
-- symbolized terms.

include "name.mc"
include "bool.mc"

include "mexpr/ast.mc"

-----------------
-- ENVIRONMENT --
-----------------

type NameEnv = AssocMap Name Name

type Env = {
  varEnv : NameEnv,
  conEnv : NameEnv
}

-----------
-- TERMS --
-----------

lang VarEq = VarAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmVar {ident = i2} ->
    match env with {varEnv = varEnv} then
      match lhs with TmVar {ident = i1} then
        match assocLookup {eq = nameEq} i1 varEnv with Some n2 then
          nameEq i2 n2
        else error (concat "Unbound variable in eq: " (nameGetStr i2))
      else false
    else never
end

lang AppEq = AppAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmApp {lhs = rl, rhs = rr} ->
    match lhs with TmApp {lhs = ll, rhs = lr} then
      if eqexpr env ll rl then eqexpr env lr rr else false
    else false
end

lang FunEq = FunAst
  sem eqexpr (env : Env) (lhs : Expr) =
  -- NOTE: The type annotation is currently ignored.
  | TmLam {ident = i2, body = b2} ->
    match env with {varEnv = varEnv, conEnv = conEnv} then
      match lhs with TmLam {ident = i1, body = b1} then
        let varEnv = assocInsert {eq = nameEq} i1 i2 varEnv in
        eqexpr {varEnv = varEnv, conEnv = conEnv} b1 b2
      else false
    else never
end

lang RecordEq = RecordAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmRecord {bindings = bs2} ->
    match lhs with TmRecord {bindings = bs1} then
      if eqi (assocLength bs1) (assocLength bs2) then
        assocAll
          (lam k1. lam v1.
            assocAny (lam k2. lam v2. and (eqstr k1 k2) (eqexpr env v1 v2))
              bs2)
          bs1
      else false
    else false

  | TmRecordUpdate {rec = r2, key = k2, value = v2} ->
    match lhs with TmRecordUpdate {rec = r1, key = k1, value = v1} then
      and (and (eqexpr env r1 r2) (eqstr k1 k2)) (eqexpr env v1 v2)
    else false
end

lang LetEq = LetAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmLet {ident = i2, body = b2, inexpr = ie2} ->
    match env with {varEnv = varEnv, conEnv = conEnv} then
      match lhs with TmLet {ident = i1, body = b1, inexpr = ie1} then
        if eqexpr env b1 b2 then
          let varEnv = assocInsert {eq = nameEq} i1 i2 varEnv in
          eqexpr {varEnv = varEnv, conEnv = conEnv} ie1 ie2
        else false
      else false
    else never
end

lang RecLetsEq = RecLetsAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmRecLets {bindings = bs2} ->
    -- This requires the bindings to occur in the same order.
    -- NOTE: Do we want to allow equality of differently ordered (but equal)
    -- bindings as well?
    match env with {varEnv = varEnv, conEnv = conEnv} then
      match lhs with TmRecLets {bindings = bs1} then
        if eqi (length bs1) (length bs2) then
          let bszip = zipWith (lam b1. lam b2. (b1, b2)) bs1 bs2 in
          let varEnv =
            foldl
              (lam varEnv. lam t.
                 assocInsert {eq = nameEq} (t.0).ident (t.1).ident varEnv)
              varEnv bszip
          in
          let env = {varEnv = varEnv, conEnv = conEnv} in
          all (lam t. eqexpr env (t.0).body (t.1).body) bszip
        else false
      else false
    else never
end

lang ConstEq = ConstAst
  sem eqconst (lhs : Const) =
  -- Intentionally left blank

  sem eqexpr (env : Env) (lhs : Expr) =
  | TmConst {val = v2} ->
    match lhs with TmConst {val = v1} then
      eqconst v1 v2
    else false
end

lang DataEq = DataAst
  sem eqexpr (env : Env) (lhs : Expr) =
  -- Type annotation ignored here as well
  | TmConDef {ident = i2, inexpr = ie2} ->
    match env with {varEnv = varEnv, conEnv = conEnv} then
      match lhs with TmConDef {ident = i1, inexpr = ie1} then
        let conEnv = assocInsert {eq = nameEq} i1 i2 conEnv in
        eqexpr {varEnv = varEnv, conEnv = conEnv} ie1 ie2
      else false
    else never

  | TmConApp {ident = i2, body = b2} ->
    match env with {varEnv = varEnv, conEnv = conEnv} then
      match lhs with TmConApp {ident = i1, body = b1} then
        match assocLookup {eq = nameEq} i1 conEnv with Some n2 then
          if nameEq i2 n2 then
            eqexpr env b1 b2
          else false
        else error (concat "Unbound constructor in eq: " (nameGetStr i2))
      else false
    else never

end

lang MatchEq = MatchAst
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- Intentionally left blank

  sem eqexpr (env : Env) (lhs : Expr) =
  | TmMatch {target = t2, pat = p2, thn = thn2, els = els2} ->
    match lhs with TmMatch {target = t1, pat = p1, thn = thn1, els = els1} then
      if eqexpr env t1 t2 then
        if eqexpr env els1 els2 then
          match eqpat env assocEmpty p1 p2 with Some patEnv then
            match env with {varEnv = varEnv, conEnv = conEnv} then
              -- TODO: Waiting for symbolize updates from Viktor (varEnv should
              -- be merged with patEnv using mergepreferright from assoc.mc)
              eqexpr {varEnv = varEnv, conEnv = conEnv} thn1 thn2
            else never
          else false
        else false
      else false
    else false

end

lang UtestEq = UtestAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmUtest {test = t2, expected = e2, next = n2} ->
    match lhs with TmUtest {test = t1, expected = e1, next = n1} then
      if eqexpr env t1 t2 then
        if eqexpr env e1 e2 then
          eqexpr env n1 n2
        else false
      else false
    else false
end

lang SeqEq = SeqAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmSeq {tms = ts2} ->
    match lhs with TmSeq {tms = ts1} then
      if eqi (length ts1) (length ts2) then
        let z = zipWith (lam t1. lam t2. (t1,t2)) ts1 ts2 in
        all (lam tp. eqexpr env tp.0 tp.1) z
      else false
    else false
end

lang NeverEq = NeverAst
  sem eqexpr (env : Env) (lhs : Expr) =
  | TmNever _ -> match lhs with TmNever _ then true else false
end

---------------
-- CONSTANTS --
---------------

lang IntEq = IntAst
  sem eqconst (lhs : Const) =
  | CInt {val = v2} -> match lhs with CInt {val = v1} then eqi v1 v2 else false
end

lang ArithEq = ArithIntAst
  sem eqconst (lhs : Const) =
  | CAddi {} -> match lhs with CAddi _ then true else false
  | CSubi {} -> match lhs with CSubi _ then true else false
  | CMuli {} -> match lhs with CMuli _ then true else false
end

lang FloatEq = FloatAst
  sem eqconst (lhs : Const) =
  | CFloat {val = v2} ->
    match lhs with CFloat {val = v1} then eqf v1 v2 else false
end

lang ArithFloatEq = ArithFloatAst
  sem eqconst (lhs : Const) =
  | CAddf {} -> match lhs with CAddf _ then true else false
  | CSubf {} -> match lhs with CSubf _ then true else false
  | CMulf {} -> match lhs with CMulf _ then true else false
  | CDivf {} -> match lhs with CDivf _ then true else false
  | CNegf {} -> match lhs with CNegf _ then true else false
end

lang BoolEq = BoolAst
  sem eqconst (lhs : Const) =
  | CBool {val = v2} ->
    match lhs with CBool {val = v1} then eqb v1 v2 else false
  | CNot {} -> match lhs with CNot _ then true else false
end

lang CmpIntEq = CmpIntAst
  sem eqconst (lhs : Const) =
  | CEqi {} -> match lhs with CEqi _ then true else false
  | CLti {} -> match lhs with CLti _ then true else false
end

lang CmpFloatEq = CmpFloatAst
  sem eqconst (lhs : Const) =
  | CEqf {} -> match lhs with CEqf _ then true else false
  | CLtf {} -> match lhs with CLtf _ then true else false
end

lang CharEq = CharAst
  sem eqconst (lhs : Const) =
  | CChar {val = v2} ->
    match lhs with CChar {val = v1} then eqchar v1 v2 else false
end

lang SymbEq = SymbAst
  sem eqconst (lhs : Const) =
  | CSymb {val = v2} ->
    match lhs with CSymb {val = v1} then eqs v1 v2 else false
end

lang CmpSymbEq = CmpSymbAst
  sem eqconst (lhs : Const) =
  | CEqs {} -> match lhs with CEqs _ then true else false
end

-- TODO Remove constants no longer available in boot?
lang SeqOpEq = SeqOpAst
  sem eqconst (lhs : Const) =
  | CGet {} -> match lhs with CGet _ then true else false
  | CCons {} -> match lhs with CCons _ then true else false
  | CSnoc {} -> match lhs with CSnoc _ then true else false
  | CConcat {} -> match lhs with CConcat _ then true else false
  | CLength {} -> match lhs with CLength _ then true else false
  | CHead {} -> match lhs with CHead _ then true else false
  | CTail {} -> match lhs with CTail _ then true else false
  | CNull {} -> match lhs with CNull _ then true else false
  | CReverse {} -> match lhs with CReverse _ then true else false
end

--------------
-- PATTERNS --
--------------

let _eqpatname : NameEnv -> PatName -> PatName -> Option NameEnv =
  lam penv. lam p1. lam p2.
    match (p1,p2) with (PName n1,PName n2) then
      match assocLookup {eq=nameEq} n1 penv with Some i2 then
        if nameEq i2 n2 then Some penv else None ()
      else Some (assocInsert {eq = nameEq} n1 n2 penv)
    else match (p1,p2) with (PWildcard _,PWildcard _) then Some penv
    else None ()

lang VarPatEq = VarPat
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PVar p2 -> match lhs with PVar p1 then _eqpatname patEnv p1 p2 else None ()
end

lang SeqTotPatEq
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang SeqEdgPatEq
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang RecordPatEq = RecordPat
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PRecord {bindings = bs2} ->
    match lhs with PRecord {bindings = bs1} then
      if eqi (assocLength bs1) (assocLength bs2) then
        assocFoldOption {eq=eqstr}
          (lam patEnv. lam k1. lam p1.
             match assocLookup {eq=eqstr} k1 bs2 with Some p2 then
               eqpat env patEnv p1 p2
             else None ())
          patEnv bs1
      else None ()
    else None ()
end

lang DataPatEq = DataPat
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PCon {ident = i2, subpat = s2} ->
    match lhs with PCon {ident = i1, subpat = s1} then
      match env with {conEnv = conEnv} then
        match assocLookup {eq=nameEq} i1 conEnv with n2 then
          if nameEq i2 n2 then eqpat env patEnv s1 s2
          else None ()
        else None ()
      else never
    else None ()
end

lang IntPatEq = IntPat
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PInt {val = i2} ->
    match lhs with PInt {val = i1} then
      if eqi i1 i2 then Some patEnv else None ()
    else None ()
end

lang CharPatEq = CharPat
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PChar {val = c2} ->
    match lhs with PChar {val = c1} then
      if eqchar c1 c2 then Some patEnv else None ()
    else None ()
end

lang BoolPatEq = BoolPat
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PBool {val = b2} ->
    match lhs with PBool {val = b1} then
      if eqb b1 b2 then Some patEnv else None ()
    else None ()
end

lang AndPatEq
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang OrPatEq
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang NotPatEq
  sem eqpat (env : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

-----------------------------
-- MEXPR ALPHA EQUIVALENCE --
-----------------------------


-----------
-- TESTS --
-----------
