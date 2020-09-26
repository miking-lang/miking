-- Alpha equivalence for closed MExpr terms. Supports both non-symbolized and
-- symbolized terms.

include "name.mc"
include "bool.mc"

include "mexpr/ast.mc"
include "mexpr/symbolize.mc"

-----------------
-- ENVIRONMENT --
-----------------

type NameEnv = AssocMap Name Name

type Env = {
  varEnv : NameEnv,
  conEnv : NameEnv
}

-- Checks if i1->i2 exists in either the bound or free environment (bound takes
-- precedence). If so, return the given free environment. If the mapping does
-- not exist, add it to the free environment and return this updated
-- environment. In all other cases, return None ().
let _checkNames : NameEnv -> NameEnv -> Name -> Name -> Option NameEnv =
  lam env. lam free. lam i1. lam i2.
    match optionOr
            (assocLookup {eq = nameEq} i1 env) -- Known bound var
            (assocLookup {eq = nameEq} i1 free) -- Known free var
    with Some n2 then
      if nameEq i2 n2 then Some free else None ()
    else -- Unknown (free) var
      Some (assocInsert {eq = nameEq} i1 i2 free)

-----------
-- TERMS --
-----------

lang VarEq = VarAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmVar {ident = i2} ->
    match lhs with TmVar {ident = i1} then
      match (env,free) with ({varEnv = varEnv},{varEnv = freeVarEnv}) then
        match _checkNames varEnv freeVarEnv i1 i2 with Some freeVarEnv then
          Some {free with varEnv = freeVarEnv}
        else None ()
      else never
    else None ()
end

lang AppEq = AppAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmApp {lhs = rl, rhs = rr} ->
    match lhs with TmApp {lhs = ll, rhs = lr} then
      match eqexpr env free ll rl with Some free then
        eqexpr env free lr rr
      else None ()
    else None ()
end

lang FunEq = FunAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  -- NOTE dlunde 2020-09-26: The type annotation is currently ignored.
  | TmLam {ident = i2, body = b2} ->
    match env with {varEnv = varEnv} then
      match lhs with TmLam {ident = i1, body = b1} then
        let varEnv = assocInsert {eq = nameEq} i1 i2 varEnv in
        eqexpr {env with varEnv = varEnv} free b1 b2
      else None ()
    else never
end

lang RecordEq = RecordAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmRecord {bindings = bs2} ->
    match lhs with TmRecord {bindings = bs1} then
      if eqi (assocLength bs1) (assocLength bs2) then
        assocFoldlM {eq=eqstr}
          (lam free. lam k1. lam v1.
            match assocLookup {eq=eqstr} k1 bs2 with Some v2 then
              eqexpr env free v1 v2
            else None ())
          free bs1
      else None ()
    else None ()

  | TmRecordUpdate {rec = r2, key = k2, value = v2} ->
    match lhs with TmRecordUpdate {rec = r1, key = k1, value = v1} then
      if eqstr k1 k2 then
        match eqexpr env free r1 r2 with Some free then
          eqexpr env free v1 v2
        else None ()
      else None ()
    else None ()
end

lang LetEq = LetAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmLet {ident = i2, body = b2, inexpr = ie2} ->
    match lhs with TmLet {ident = i1, body = b1, inexpr = ie1} then
      match eqexpr env free b1 b2 with Some free then
        match env with {varEnv = varEnv} then
          let varEnv = assocInsert {eq = nameEq} i1 i2 varEnv in
          eqexpr {env with varEnv = varEnv} free ie1 ie2
        else never
      else None ()
    else None ()
end

lang RecLetsEq = RecLetsAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmRecLets {bindings = bs2} ->
    -- NOTE dlunde 2020-09-25: This requires the bindings to occur in the same
    -- order. Do we want to allow equality of differently ordered (but equal)
    -- bindings as well?
    match env with {varEnv = varEnv} then
      match lhs with TmRecLets {bindings = bs1} then
        if eqi (length bs1) (length bs2) then
          let bszip = zipWith (lam b1. lam b2. (b1, b2)) bs1 bs2 in
          let varEnv =
            foldl
              (lam varEnv. lam t.
                 assocInsert {eq = nameEq} (t.0).ident (t.1).ident varEnv)
              varEnv bszip
          in
          let env = {env with varEnv = varEnv} in
          optionFoldlM (lam free. lam t. eqexpr env free (t.0).body (t.1).body)
            free bszip
        else None ()
      else None ()
    else never
end

lang ConstEq = ConstAst
  sem eqconst (lhs : Const) =
  -- Intentionally left blank

  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmConst {val = v2} ->
    match lhs with TmConst {val = v1} then
      if eqconst v1 v2 then Some free else None ()
    else None ()
end

lang DataEq = DataAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  -- Type annotation ignored here as well
  | TmConDef {ident = i2, inexpr = ie2} ->
    match env with {conEnv = conEnv} then
      match lhs with TmConDef {ident = i1, inexpr = ie1} then
        let conEnv = assocInsert {eq = nameEq} i1 i2 conEnv in
        eqexpr {env with conEnv = conEnv} free ie1 ie2
      else None ()
    else never

  | TmConApp {ident = i2, body = b2} ->
    match lhs with TmConApp {ident = i1, body = b1} then
      match (env,free) with ({conEnv = conEnv},{conEnv = freeConEnv}) then
        match _checkNames conEnv freeConEnv i1 i2 with Some freeConEnv then
          eqexpr env {free with conEnv = freeConEnv} b1 b2
        else None ()
      else never
    else None ()
end

lang MatchEq = MatchAst
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- Intentionally left blank

  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmMatch {target = t2, pat = p2, thn = thn2, els = els2} ->
    match lhs with TmMatch {target = t1, pat = p1, thn = thn1, els = els1} then
      match eqexpr env free t1 t2 with Some free then
        match eqexpr env free els1 els2 with Some free then
          match eqpat env free assocEmpty p1 p2 with Some (free,patEnv) then
            match env with {varEnv = varEnv} then
              eqexpr
                { env with
                  varEnv = assocMergePreferRight {eq = nameEq} varEnv patEnv }
                free thn1 thn2
            else never
          else None ()
        else None ()
      else None ()
    else None ()

end

lang UtestEq = UtestAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmUtest {test = t2, expected = e2, next = n2} ->
    match lhs with TmUtest {test = t1, expected = e1, next = n1} then
      match eqexpr env free t1 t2 with Some free then
        match eqexpr env free e1 e2 with Some free then
          eqexpr env free n1 n2
        else None ()
      else None ()
    else None ()
end

lang SeqEq = SeqAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmSeq {tms = ts2} ->
    match lhs with TmSeq {tms = ts1} then
      if eqi (length ts1) (length ts2) then
        let z = zipWith (lam t1. lam t2. (t1,t2)) ts1 ts2 in
        optionFoldlM (lam free. lam tp. eqexpr env free tp.0 tp.1) free z
      else None ()
    else None ()
end

lang NeverEq = NeverAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmNever _ -> match lhs with TmNever _ then Some free else None ()
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

let _eqpatname : NameEnv -> NameEnv -> PatName -> PatName -> Option NameEnv =
  lam penv. lam free. lam p1. lam p2.
    match (p1,p2) with (PName n1,PName n2) then
      match assocLookup {eq=nameEq} n1 penv with Some i2 then
        if nameEq i2 n2 then Some (free,penv) else None ()
      else Some (free, assocInsert {eq = nameEq} n1 n2 penv)
    else match (p1,p2) with (PWildcard _,PWildcard _) then Some (free,penv)
    else None ()

lang VarPatEq = VarPat
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PVar p2 ->
    match lhs with PVar p1 then
      _eqpatname patEnv free p1 p2
    else None ()
end

lang SeqTotPatEq
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang SeqEdgPatEq
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang RecordPatEq = RecordPat
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PRecord {bindings = bs2} ->
    match lhs with PRecord {bindings = bs1} then
      if eqi (assocLength bs1) (assocLength bs2) then
        assocFoldlM {eq=eqstr}
          (lam tEnv. lam k1. lam p1.
             match tEnv with (free,patEnv) then
               match assocLookup {eq=eqstr} k1 bs2 with Some p2 then
                 eqpat env free patEnv p1 p2
               else None ()
             else never)
          (free,patEnv) bs1
      else None ()
    else None ()
end

lang DataPatEq = DataPat
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PCon {ident = i2, subpat = s2} ->
    match lhs with PCon {ident = i1, subpat = s1} then
      match (env,free) with ({conEnv = conEnv},{conEnv = freeConEnv}) then
        match _checkNames conEnv freeConEnv i1 i2 with Some freeConEnv then
          eqpat env {free with conEnv = freeConEnv} patEnv s1 s2
        else None ()
      else never
    else None ()
end

lang IntPatEq = IntPat
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PInt {val = i2} ->
    match lhs with PInt {val = i1} then
      if eqi i1 i2 then Some (free,patEnv) else None ()
    else None ()
end

lang CharPatEq = CharPat
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PChar {val = c2} ->
    match lhs with PChar {val = c1} then
      if eqchar c1 c2 then Some (free,patEnv) else None ()
    else None ()
end

lang BoolPatEq = BoolPat
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PBool {val = b2} ->
    match lhs with PBool {val = b1} then
      if eqb b1 b2 then Some (free,patEnv) else None ()
    else None ()
end

lang AndPatEq
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang OrPatEq
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

lang NotPatEq
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  -- TODO
end

-----------------------------
-- MEXPR ALPHA EQUIVALENCE --
-----------------------------

lang MExprEq =

  MExprSym

  -- Terms
  + VarEq + AppEq + FunEq + RecordEq + LetEq + RecLetsEq + ConstEq + DataEq +
  MatchEq + UtestEq + SeqEq + NeverEq

  -- Constants
  + IntEq + ArithEq + FloatEq + ArithFloatEq + BoolEq + CmpIntEq + CmpFloatEq +
  CharEq + SymbEq + CmpSymbEq + SeqOpEq

  -- Patterns
  + VarPatEq + SeqTotPatEq + SeqEdgPatEq + RecordPatEq + DataPatEq + IntPatEq +
  CharPatEq + BoolPatEq + AndPatEq + OrPatEq + NotPatEq

---------------------------
-- CONVENIENCE FUNCTIONS --
---------------------------

let eqmexpr = use MExprEq in
  lam e1. lam e2.
    let empty = {varEnv = assocEmpty, conEnv = assocEmpty} in
    match eqexpr empty empty e1 e2 with Some _ then true else false

-----------
-- TESTS --
-----------

mexpr

use MExprEq in

let sm = symbolizeMExpr in

let lv1 = ulam_ "x" (var_ "x") in
let lv2 = ulam_ "y" (var_ "y") in

utest lv1 with lv2 using eqmexpr in
utest eqmexpr (int_ 1) lv2 with false in

utest sm lv1 with sm lv2 using eqmexpr in
utest eqmexpr (sm (int_ 1)) (sm lv2) with false in


let a1 = app_ lv1 lv2 in
let a2 = app_ lv2 lv1 in

utest a1 with a2 using eqmexpr in
utest eqmexpr a1 lv1 with false in

utest sm a1 with sm a2 using eqmexpr in
utest eqmexpr (sm a1) (sm lv1) with false in


let r1 = record_ [("a",lv1), ("b",a1), ("c",a2)] in
let r2 = record_ [("b",a1), ("a",lv2), ("c",a2)] in
let r3e = record_ [("a",lv1), ("b",a1), ("d",a2)] in
let r4e = record_ [("a",lv1), ("b",a1), ("c",lv2)] in

utest r1 with r2 using eqmexpr in
utest eqmexpr r1 r3e with false in
utest eqmexpr r1 r4e with false in

utest sm r1 with sm r2 using eqmexpr in
utest eqmexpr (sm r1) (sm r3e) with false in
utest eqmexpr (sm r1) (sm r4e) with false in


let ru1 = recordupdate_ r1 "b" lv1 in
let ru2 = recordupdate_ r2 "b" lv2 in
let ru3e = recordupdate_ r3e "b" lv2 in
let ru4e = recordupdate_ r2 "c" lv2 in

utest ru1 with ru2 using eqmexpr in
utest eqmexpr ru1 ru3e with false in
utest eqmexpr ru1 ru4e with false in

utest sm ru1 with sm ru2 using eqmexpr in
utest eqmexpr (sm ru1) (sm ru3e) with false in
utest eqmexpr (sm ru1) (sm ru4e) with false in


let let1 = bind_ (let_ "x" lv1) a1 in
let let2 = bind_ (let_ "y" lv2) a2 in
let let3e = bind_ (let_ "x" (int_ 1)) a1 in
let let4e = bind_ (let_ "x" lv2) lv1 in

utest let1 with let2 using eqmexpr in
utest eqmexpr let1 let3e with false in
utest eqmexpr let1 let4e with false in

utest sm let1 with sm let2 using eqmexpr in
utest eqmexpr (sm let1) (sm let3e) with false in
utest eqmexpr (sm let1) (sm let4e) with false in


let rlet1 = reclets_ [("x", a1), ("y", lv1)] in
let rlet2 = reclets_ [("x", a2), ("y", lv2)] in
let rlet3 = reclets_ [("y", a2), ("x", lv2)] in
let rlet4e = reclets_ [("y", lv1), ("x", a1)] in -- Order matters
utest rlet1 with rlet2 using eqmexpr in
utest rlet1 with rlet3 using eqmexpr in
utest eqmexpr rlet1 rlet4e with false in

-- TODO Remaining tests

()
