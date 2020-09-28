-- Alpha equivalence for MExpr terms. Supports both non-symbolized and
-- symbolized terms. Also supports terms with unbound variables and
-- constructors.

include "name.mc"
include "bool.mc"

include "mexpr/ast.mc"
include "mexpr/symbolize.mc"

-----------------
-- ENVIRONMENT --
-----------------

-- The environment used throughout equality checking must be bijective. We use
-- double assocMaps to check this.
type NameEnv = (AssocMap Name Name, AssocMap Name Name)

let _eqEmptyNameEnv = (assocEmpty, assocEmpty)

type Env = {
  varEnv : NameEnv,
  conEnv : NameEnv
}

let _eqUpdateEnv : NameEnv -> NameEnv -> NameEnv =
  lam old. lam new.
    let m = assocMergePreferRight {eq=nameEq} in
    (m old.0 new.0, m old.1 new.1)

let _eqInsert : Name -> Name -> NameEnv -> NameEnv =
  lam i1. lam i2. lam env.
    let t1 = assocInsert {eq = nameEq} i1 i2 env.0 in
    let t2 = assocInsert {eq = nameEq} i2 i1 env.1 in
    (t1,t2)

-- Returns Some true if the mapping exists and is consistent, Some false if the
-- mapping does not exist, and None () if the mapping exists but is
-- inconsistent (the environment is found to not be bijective).
let _eqCheckEnv : Name -> Name -> NameEnv -> Option Bool =
  lam i1. lam i2. lam env.
    let m = (assocLookup {eq = nameEq} i1 env.0,
             assocLookup {eq = nameEq} i2 env.1) in

    -- Binding exists in both directions
    match m with (Some v2, Some v1) then
      if and (nameEq i1 v1) (nameEq i2 v2) then
        Some true -- Bindings are consistent
      else None () -- Bindings are inconsistent

    -- Binding exists only in one direction (inconsistent)
    else match m with (Some _, None ()) | (None (), Some _) then
      None ()

    -- Binding is completely missing (consistent)
    else match m with (None (), None ()) then
      Some false
    else never

-- Checks if i1 <-> i2 exists in either the bound or free environments (bound
-- takes precedence). If so, return the given free environment. If the mapping
-- does not exist, add it to the free environment and return this updated
-- environment. If the mapping is found to be inconsistent, return None ().
let _eqCheckEnvs : Name -> Name -> NameEnv -> NameEnv -> Option NameEnv =
  lam i1. lam i2. lam env. lam free.
    let lenv = _eqCheckEnv i1 i2 env in
    match lenv with Some true then Some free -- Consistent bound name exists
    else match lenv with Some false then
      let lfree = _eqCheckEnv i1 i2 free in
      match lfree with Some true then Some free -- Consistent free name exists
      else match lfree with Some false then
        Some (_eqInsert i1 i2 free) -- New free variable encountered
      else match lfree with None () then None () -- Inconsistent bindings
      else never
    else match lenv with None () then None () -- Inconsistent bindings
    else never

-----------
-- TERMS --
-----------

lang VarEq = VarAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmVar {ident = i2} ->

    match lhs with TmVar {ident = i1} then
      match (env,free) with ({varEnv = varEnv},{varEnv = freeVarEnv}) then
        match _eqCheckEnvs i1 i2 varEnv freeVarEnv with Some freeVarEnv then
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
        let varEnv = _eqInsert i1 i2 varEnv in
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
          let varEnv = _eqInsert i1 i2 varEnv in
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
                 _eqInsert (t.0).ident (t.1).ident varEnv)
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
        let conEnv = _eqInsert i1 i2 conEnv in
        eqexpr {env with conEnv = conEnv} free ie1 ie2
      else None ()
    else never

  | TmConApp {ident = i2, body = b2} ->
    match lhs with TmConApp {ident = i1, body = b1} then
      match (env,free) with ({conEnv = conEnv},{conEnv = freeConEnv}) then
        match _eqCheckEnvs i1 i2 conEnv freeConEnv with Some freeConEnv then
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
          match eqpat env free _eqEmptyNameEnv p1 p2 with Some (free,patEnv) then
            match env with {varEnv = varEnv} then
              eqexpr
                { env with
                  varEnv = _eqUpdateEnv varEnv patEnv }
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
      let lpenv = _eqCheckEnv n1 n2 penv in
      match lpenv with Some true then Some (free,penv)
      else match lpenv with Some false then
        Some (free, _eqInsert n1 n2 penv)
      else match lpenv with None () then None ()
      else never

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
        match _eqCheckEnvs i1 i2 conEnv freeConEnv with Some freeConEnv then
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
    let empty = {varEnv = _eqEmptyNameEnv, conEnv = _eqEmptyNameEnv} in
    match eqexpr empty empty e1 e2 with Some _ then true else false

-----------
-- TESTS --
-----------

mexpr

use MExprEq in

let sm = symbolizeMExpr in

let v1 = var_ "x" in
let v2 = var_ "y" in
utest v1 with v2 using eqmexpr in
utest eqmexpr (int_ 1) v1 with false in
-- TODO dlunde 2020-09-28: Symbolize does not work for open terms
-- utest sm v1 with sm v2 using eqmexpr in
-- utest eqmexpr (sm (int_ 1)) (sm v1) with false in

-- Variables are equal as long as they occur in the same positions
let v3 = app_ (var_ "x") (var_ "y") in
let v4 = app_ (var_ "y") (var_ "x") in
let v5e = app_ (var_ "x") (var_ "x") in
utest v3 with v4 using eqmexpr in
utest eqmexpr v3 v5e with false in

let lam1 = ulam_ "x" v1 in
let lam2 = ulam_ "y" v2 in
utest lam1 with lam2 using eqmexpr in
utest sm lam1 with sm lam2 using eqmexpr in
utest eqmexpr (int_ 1) lam2 with false in
utest eqmexpr (sm (int_ 1)) (sm lam2) with false in

let lamNested1 = ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y"))) in
let lamNested2 = ulam_ "x" (ulam_ "x" (app_ (var_ "x") (var_ "x"))) in
utest eqmexpr lamNested1 lamNested2 with false in
utest eqmexpr (sm lamNested1) (sm lamNested2) with false in
utest eqmexpr lamNested2 lamNested1 with false in
utest eqmexpr (sm lamNested2) (sm lamNested1) with false in

let a1 = app_ lam1 lam2 in
let a2 = app_ lam2 lam1 in
utest a1 with a2 using eqmexpr in
utest sm a1 with sm a2 using eqmexpr in
utest eqmexpr a1 lam1 with false in
utest eqmexpr (sm a1) (sm lam1) with false in

let r1 = record_ [("a",lam1), ("b",a1), ("c",a2)] in
let r2 = record_ [("b",a1), ("a",lam2), ("c",a2)] in
let r3e = record_ [("a",lam1), ("b",a1), ("d",a2)] in
let r4e = record_ [("a",lam1), ("b",a1), ("c",lam2)] in
let r5e = record_ [("a",lam1), ("b",a1), ("c",a2), ("d",lam2)] in
utest r1 with r2 using eqmexpr in
utest sm r1 with sm r2 using eqmexpr in
utest eqmexpr r1 r3e with false in
utest eqmexpr (sm r1) (sm r3e) with false in
utest eqmexpr r1 r4e with false in
utest eqmexpr (sm r1) (sm r4e) with false in
utest eqmexpr r1 r5e with false in
utest eqmexpr (sm r1) (sm r5e) with false in

let ru1 = recordupdate_ r1 "b" lam1 in
let ru2 = recordupdate_ r2 "b" lam2 in
let ru3e = recordupdate_ r3e "b" lam2 in
let ru4e = recordupdate_ r2 "c" lam2 in
utest ru1 with ru2 using eqmexpr in
utest sm ru1 with sm ru2 using eqmexpr in
utest eqmexpr ru1 ru3e with false in
utest eqmexpr (sm ru1) (sm ru3e) with false in
utest eqmexpr ru1 ru4e with false in
utest eqmexpr (sm ru1) (sm ru4e) with false in

let let1 = bind_ (let_ "x" lam1) a1 in
let let2 = bind_ (let_ "y" lam2) a2 in
let let3e = bind_ (let_ "x" (int_ 1)) a1 in
let let4e = bind_ (let_ "x" lam2) lam1 in
utest let1 with let2 using eqmexpr in
utest sm let1 with sm let2 using eqmexpr in
utest eqmexpr let1 let3e with false in
utest eqmexpr (sm let1) (sm let3e) with false in
utest eqmexpr let1 let4e with false in
utest eqmexpr (sm let1) (sm let4e) with false in

let rlet1 = reclets_ [("x", a1), ("y", lam1)] in
let rlet2 = reclets_ [("x", a2), ("y", lam2)] in
let rlet3 = reclets_ [("y", a2), ("x", lam2)] in
let rlet4e = reclets_ [("y", lam1), ("x", a1)] in -- Order matters
utest rlet1 with rlet2 using eqmexpr in
utest sm rlet1 with sm rlet2 using eqmexpr in
utest rlet1 with rlet3 using eqmexpr in
utest sm rlet1 with sm rlet3 using eqmexpr in
utest eqmexpr rlet1 rlet4e with false in
utest eqmexpr (sm rlet1) (sm rlet4e) with false in

let c1 = (int_ 1) in
let c2 = (int_ 2) in
let c3 = (true_) in

utest c1 with c1 using eqmexpr in
utest eqmexpr c1 c2 with false in
utest eqmexpr c1 c3 with false in

-- Constructors can have different names, but they must be used in the same
-- positions.
let cda1 =
  bind_ (ucondef_ "App")
    (app_ (conapp_ "App" (int_ 1)) (conapp_ "Other" (int_ 2))) in
let cda2 =
  bind_ (ucondef_ "App2")
    (app_ (conapp_ "App2" (int_ 1)) (conapp_ "Other2" (int_ 2))) in
let cd3e =
  bind_ (ucondef_ "App")
    (app_ (conapp_ "App2" (int_ 1)) (conapp_ "Other2" (int_ 2))) in
utest cda1 with cda2 using eqmexpr in
utest eqmexpr cda1 cd3e with false in

()
