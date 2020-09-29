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

-- The environment used throughout equality checking is a bijective map.
type BiNameMap = [(Name,Name)]

let biEmpty = []

-- 'biInsert (i1,i2) bmap' inserts (i1,i2) in bmap, maintaining bijectivity
-- (destructive).
let biInsert : (Name,Name) -> BiNameMap -> BiNameMap =
  lam i. lam bmap.
    let p = (lam n. if nameEq i.0 n.0 then false else not (nameEq i.1 n.1)) in
    cons i (filter p bmap)

-- 'biMergePreferRight bmapl bmapr' inserts all elements of bmapr into bmapl
-- (destructive).
let biMergePreferRight : BiNameMap -> BiNameMap -> BiNameMap =
  lam bmapl. lam bmapr.
    foldl (lam bmap. lam i. biInsert i bmap) bmapl bmapr

-- 'biLookup (i1,i2) bmap' retrieves either (i1,y) or (x,i2) from bmap
-- (unspecified which), if such an entry exists. If not, returns
-- None ().
let biLookup : (Name,Name) -> BiNameMap -> Option (Name,Name) =
  lam i. lam bmap.
    let pred = (lam n. if nameEq i.0 n.0 then true else nameEq i.1 n.1) in
    find pred bmap

type Env = {
  varEnv : BiNameMap,
  conEnv : BiNameMap
}

-- Checks if the mapping (i1,i2) exists in either the bound or free
-- environments (bound takes precedence). If so, return the given free
-- environment. If (i1,i2) is inconsistent with either environment, return None
-- (). If i1 (lhs) or i2 (rhs) does not exist in any environment, return the
-- free environment with (i1,i2) added.
let _eqCheck : Name -> Name -> NameEnv -> NameEnv -> Option NameEnv =
  lam i1. lam i2. lam env. lam free.
    match biLookup (i1,i2) env with Some (n1,n2) then
      if and (nameEq i1 n1) (nameEq i2 n2) then Some free -- Match in env
      else None () -- i1<->i2 is not consistent with env
    else match biLookup (i1,i2) free with Some (n1,n2) then
      if and (nameEq i1 n1) (nameEq i2 n2) then Some free -- Match in free
      else None () -- i1<->i2 is not consistent with free
    else
      -- Here, we know that neither i1 (lhs) nor i2 (rhs) exists in free.
      -- Hence, the below insert is non-destructive (which makes sense, since
      -- unbound variables cannot shadow one another).
      Some (biInsert (i1,i2) free)


-----------
-- TERMS --
-----------

lang VarEq = VarAst
  sem eqexpr (env : Env) (free : Env) (lhs : Expr) =
  | TmVar {ident = i2} ->
    match lhs with TmVar {ident = i1} then
      match (env,free) with ({varEnv = varEnv},{varEnv = freeVarEnv}) then
        match _eqCheck i1 i2 varEnv freeVarEnv with Some freeVarEnv then
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
        let varEnv = biInsert (i1,i2) varEnv in
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
          let varEnv = biInsert (i1,i2) varEnv in
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
                 biInsert ((t.0).ident,(t.1).ident) varEnv)
              varEnv bszip
          in
          let env = {env with varEnv = varEnv} in
          optionFoldlM
            (lam free. lam t. eqexpr env free (t.0).body (t.1).body)
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
        let conEnv = biInsert (i1,i2) conEnv in
        eqexpr {env with conEnv = conEnv} free ie1 ie2
      else None ()
    else never

  | TmConApp {ident = i2, body = b2} ->
    match lhs with TmConApp {ident = i1, body = b1} then
      match (env,free) with ({conEnv = conEnv},{conEnv = freeConEnv}) then
        match _eqCheck i1 i2 conEnv freeConEnv with Some freeConEnv then
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
          match eqpat env free biEmpty p1 p2 with Some (free,patEnv) then
            match env with {varEnv = varEnv} then
              eqexpr {env with varEnv = biMergePreferRight varEnv patEnv}
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
    match (p1,p2) with (PName i1,PName i2) then
      match biLookup (i1,i2) penv with Some (n1,n2) then
        if and (nameEq i1 n1) (nameEq i2 n2) then
          Some (free,penv) -- Match in env
        else None () -- i1<->i2 is not consistent with penv
      else
        let penv = biInsert (i1,i2) penv in Some (free,penv)

    else match (p1,p2) with (PWildcard _,PWildcard _) then Some (free,penv)
    else None ()

lang VarPatEq = VarPat
  sem eqpat (env : Env) (free : Env) (patEnv : NameEnv) (lhs : Pat) =
  | PVar {ident = p2} ->
    match lhs with PVar {ident = p1} then
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
        match _eqCheck i1 i2 conEnv freeConEnv with Some freeConEnv then
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
    let empty = {varEnv = biEmpty, conEnv = biEmpty} in
    match eqexpr empty empty e1 e2 with Some _ then true else false

-----------
-- TESTS --
-----------

mexpr

use MExprEq in

-- Simple variables
let v1 = var_ "x" in
let v2 = var_ "y" in
utest v1 with v2 using eqmexpr in
utest eqmexpr (int_ 1) v1 with false in

-- Variables are equal as long as they occur in the same positions
let v3 = app_ (var_ "x") (var_ "y") in
let v4 = app_ (var_ "y") (var_ "x") in
let v5e = app_ (var_ "x") (var_ "x") in
utest v3 with v4 using eqmexpr in
utest eqmexpr v3 v5e with false in

-- Lambdas
let lam1 = ulam_ "x" v1 in
let lam2 = ulam_ "y" v2 in
utest lam1 with lam2 using eqmexpr in
utest eqmexpr (int_ 1) lam2 with false in

let lamNested1 = ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y"))) in
let lamNested2 = ulam_ "x" (ulam_ "x" (app_ (var_ "x") (var_ "x"))) in
utest eqmexpr lamNested1 lamNested2 with false in
utest eqmexpr lamNested2 lamNested1 with false in

let lamNested21 = ulam_ "x" (ulam_ "y" (ulam_ "x" (var_ "x"))) in
let lamNested22 = ulam_ "x" (ulam_ "y" (ulam_ "y" (var_ "y"))) in
let lamNested23 =
  ulam_ "x" (ulam_ "y" (ulam_ "x" (app_ (var_ "x") (var_ "y")))) in
let lamNested24 =
  ulam_ "x" (ulam_ "y" (ulam_ "y" (app_ (var_ "y") (var_ "y")))) in
utest lamNested21 with lamNested22 using eqmexpr in
utest eqmexpr lamNested23 lamNested24 with false in

-- Applications
let a1 = app_ lam1 lam2 in
let a2 = app_ lam2 lam1 in
utest a1 with a2 using eqmexpr in
utest eqmexpr a1 lam1 with false in

-- Records
let r1 = record_ [("a",lam1), ("b",a1), ("c",a2)] in
let r2 = record_ [("b",a1), ("a",lam2), ("c",a2)] in
let r3e = record_ [("a",lam1), ("b",a1), ("d",a2)] in
let r4e = record_ [("a",lam1), ("b",a1), ("c",lam2)] in
let r5e = record_ [("a",lam1), ("b",a1), ("c",a2), ("d",lam2)] in
utest r1 with r2 using eqmexpr in
utest eqmexpr r1 r3e with false in
utest eqmexpr r1 r4e with false in
utest eqmexpr r1 r5e with false in

let ru1 = recordupdate_ r1 "b" lam1 in
let ru2 = recordupdate_ r2 "b" lam2 in
let ru3e = recordupdate_ r3e "b" lam2 in
let ru4e = recordupdate_ r2 "c" lam2 in
utest ru1 with ru2 using eqmexpr in
utest eqmexpr ru1 ru3e with false in
utest eqmexpr ru1 ru4e with false in

-- Let and recursive let
let let1 = bind_ (let_ "x" lam1) a1 in
let let2 = bind_ (let_ "y" lam2) a2 in
let let3e = bind_ (let_ "x" (int_ 1)) a1 in
let let4e = bind_ (let_ "x" lam2) lam1 in
utest let1 with let2 using eqmexpr in
utest eqmexpr let1 let3e with false in
utest eqmexpr let1 let4e with false in

let rlet1 = reclets_ [("x", a1), ("y", lam1)] in
let rlet2 = reclets_ [("x", a2), ("y", lam2)] in
let rlet3 = reclets_ [("y", a2), ("x", lam2)] in
let rlet4e = reclets_ [("y", lam1), ("x", a1)] in -- Order matters
utest rlet1 with rlet2 using eqmexpr in
utest rlet1 with rlet3 using eqmexpr in
utest eqmexpr rlet1 rlet4e with false in

-- Constants
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

-- Match and patterns
let m1 = match_ c1 (pint_ 1) cda1 rlet1 in
let m2 = match_ c1 (pint_ 1) cda2 rlet2 in
let m3e = match_ rlet1 (pint_ 1) cda2 rlet2 in
let m4e = match_ c1 (pint_ 1) c1 rlet2 in
let m5e = match_ c1 (pint_ 1) cda2 cda1 in
utest m1 with m2 using eqmexpr in
utest eqmexpr m1 m3e with false in
utest eqmexpr m1 m4e with false in
utest eqmexpr m1 m5e with false in

let pgen = lam p. match_ (int_ 1) p (int_ 2) (int_ 3) in
let pvar1 = pvar_ "x" in
let pvar2 = pvar_ "y" in
utest pgen pvar1 with pgen pvar2 using eqmexpr in
utest eqmexpr (pgen pvar1) (pgen (pint_ 1)) with false in

let prec1 = prec_ [("a",pvar1), ("b",pvar2), ("c",pvar1)] in
let prec2 = prec_ [("a",pvar2), ("b",pvar1), ("c",pvar2)] in
let prec3e = prec_ [("a",pvar2), ("b",pvar2), ("c",pvar1)] in
let prec4e = prec_ [("a",pvar2), ("b",pvar2), ("c",pvar1)] in
utest pgen prec1 with pgen prec2 using eqmexpr in
utest eqmexpr (pgen prec1) (pgen prec3e) with false in

let pdata1 = pcon_ "Const1" (pcon_ "Const2" prec1) in
let pdata2 = pcon_ "Const2" (pcon_ "Const1" prec1) in
let pdata3e = pcon_ "Const1" (pcon_ "Const1" prec1) in
utest pgen pdata1 with pgen pdata2 using eqmexpr in
utest eqmexpr (pgen pdata1) (pgen pdata3e) with false in

let pint1 = pint_ 1 in
let pint2 = pint_ 1 in
let pint3e = pint_ 2 in
utest pgen pint1 with pgen pint2 using eqmexpr in
utest eqmexpr (pgen pint1) (pgen pint3e) with false in

let pchar1 = pchar_ 'a' in
let pchar2 = pchar_ 'a' in
let pchar3e = pchar_ 'b' in
utest pgen pchar1 with pgen pchar2 using eqmexpr in
utest eqmexpr (pgen pchar1) (pgen pchar3e) with false in

let pbool1 = ptrue_ in
let pbool2 = ptrue_ in
let pbool3e = pfalse_ in
utest pgen pbool1 with pgen pbool2 using eqmexpr in
utest eqmexpr (pgen pbool1) (pgen pbool3e) with false in

-- Utest
let ut1 = utest_ lam1 lam2 v3 in
let ut2 = utest_ lam2 lam1 v4 in
let ut3e = utest_ v5e lam2 v3 in
let ut4e = utest_ lam1 v5e v3 in
let ut5e = utest_ lam1 lam2 v5e in
utest ut1 with ut2 using eqmexpr in
utest eqmexpr ut1 ut3e with false in
utest eqmexpr ut1 ut4e with false in
utest eqmexpr ut1 ut5e with false in

-- Sequences
let s1 = seq_ [lam1, lam2, v3] in
let s2 = seq_ [lam2, lam1, v4] in
let s3e = seq_ [lam1, v5e, v3] in
utest s1 with s2 using eqmexpr in
utest eqmexpr s1 s3e with false in

-- Never
utest never_ with never_ using eqmexpr in
utest eqmexpr never_ true_ with false in

-- Symbolized (and partially symbolized) terms are also supported.
let sm = symbolizeMExpr in
utest sm lamNested21 with sm lamNested22 using eqmexpr in
utest lamNested21 with sm lamNested22 using eqmexpr in
utest eqmexpr (sm lamNested23) (sm lamNested24) with false in

()
