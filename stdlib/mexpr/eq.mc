-- Alpha equivalence for MExpr terms and types. Supports both non-symbolized
-- and symbolized terms (including partially symbolized terms). Also supports
-- terms with unbound (free) variables and constructors.

include "assoc-seq.mc"
include "name.mc"
include "bool.mc"
include "map.mc"

include "ast.mc"
include "symbolize.mc"


-----------------
-- ENVIRONMENT --
-----------------

-- The environment used throughout equality checking is a bijective map.
type BiNameMap = [(Name,Name)]

let biEmpty = []

-- 'biInsert (i1,i2) bmap' inserts (i1,i2) in bmap, maintaining bijectivity
-- (destructive).
let biInsert : (Name,Name) -> BiNameMap -> BiNameMap =
  lam i : (Name, Name). lam bmap.
    let p = lam n : (Name, Name).
      if nameEq i.0 n.0 then false else not (nameEq i.1 n.1)
    in
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
  lam i : (Name, Name). lam bmap.
    let pred = lam n : (Name, Name).
      if nameEq i.0 n.0 then true else nameEq i.1 n.1
    in
    find pred bmap

-- 'biMem (i1, i2) bmap' returns true if i1 <-> i2 in the bijective map,
-- or false otherwise.
let biMem : (Name, Name) -> BiNameMap -> Bool =
  lam i : (Name, Name). lam bmap.
  let pred = lam n : (Name, Name).
    if nameEq i.0 n.0 then nameEq i.1 n.1 else false
  in
  optionIsSome (find pred bmap)

type EqEnv = {
  varEnv : BiNameMap,
  conEnv : BiNameMap
}

type EqTypeEnv = {
  tyVarEnv : BiNameMap
}

type EqTypeFreeEnv = {
  freeTyVars : BiNameMap,
  freeTyFlex : BiNameMap
  -- freeTyFlex is only used in `type-check.mc` for unification variables.
  -- It is included here to avoid having to duplicate code, but ideally we
  -- should have some facility to extend the arguments of a semantic function
  -- (e.g. row polymorphism or some way of untying the recursive knot).
}

-- Checks if the mapping (i1,i2) exists in either the bound or free
-- environments (bound takes precedence). If so, return the given free
-- environment. If (i1,i2) is inconsistent with either environment, return None
-- (). If i1 (lhs) or i2 (rhs) does not exist in any environment, return the
-- free environment with (i1,i2) added.
let _eqCheck : Name -> Name -> BiNameMap -> BiNameMap -> Option BiNameMap =
  lam i1. lam i2. lam env. lam free.
    match biLookup (i1,i2) env with Some n then
      let n : (Name, Name) = n in
      if and (nameEq i1 n.0) (nameEq i2 n.1) then Some free -- Match in env
      else None () -- i1<->i2 is not consistent with env
    else match biLookup (i1,i2) free with Some n then
      let n : (Name, Name) = n in
      if and (nameEq i1 n.0) (nameEq i2 n.1) then Some free -- Match in free
      else None () -- i1<->i2 is not consistent with free
    else
      -- Here, we know that neither i1 (lhs) nor i2 (rhs) exists in free.
      -- Hence, the below insert is non-destructive (which makes sense, since
      -- unbound variables cannot shadow one another).
      Some (biInsert (i1,i2) free)

-----------
-- TERMS --
-----------

-- Convenience fragment containing the function eqExpr. Should be included in
-- all fragments below.
lang Eq = ConstAst
  sem eqConst (lhs : Const) =
  | rhs /- : Const -/ -> eqConstH (lhs, rhs)

  sem eqConstH =
  -- Default case for constants that contain no data
  | (lhs, rhs) /- (Const, Const) -/ ->
    eqi (constructorTag lhs) (constructorTag rhs)

  sem eqType (lhs : Type) =
  | rhs ->
    let emptyEnv = {tyVarEnv = biEmpty} in
    let emptyFree = {freeTyVars = biEmpty, freeTyFlex = biEmpty} in
    match eqTypeH emptyEnv emptyFree lhs rhs with Some _ then true else false

  -- eqTypeH env free ty1 ty2 compares ty1 and ty2, returning
  -- + None () if ty1 and ty2 are not alpha equivalent, and
  -- + Some free' if ty1 and ty2 are alpha equivalent, where free' is an
  --   updated bijection between free variables.
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  -- Intentionally left blank

  sem eqKind (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) =
  | (lhs, rhs) ->
    if eqi (constructorTag lhs) (constructorTag rhs) then Some free
    else None ()

  sem eqExpr (e1: Expr) =
  | e2 ->
    let empty = {varEnv = biEmpty, conEnv = biEmpty} in
    match eqExprH empty empty e1 e2 with Some _ then true else false

  -- eqExprH env free lhs rhs compares lhs and rhs, returning
  -- + None () if lhs and rhs are not alpha equivalent, and
  -- + Some free' if lhs and rhs are alpha equivalent, where free' is an
  --   updated bijection between free variables.
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  -- Intentionally left blank
end

lang VarEq = Eq + VarAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmVar r ->
    match lhs with TmVar l then
      match (env,free) with ({varEnv = varEnv},{varEnv = freeVarEnv}) in
      match _eqCheck l.ident r.ident varEnv freeVarEnv with Some freeVarEnv then
        Some {free with varEnv = freeVarEnv}
      else None ()
    else None ()
end

lang AppEq = Eq + AppAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmApp r ->
    match lhs with TmApp l then
      match eqExprH env free l.lhs r.lhs with Some free then
        eqExprH env free l.rhs r.rhs
      else None ()
    else None ()
end

lang LamEq = Eq + LamAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmLam r ->
    match env with {varEnv = varEnv} then
      match lhs with TmLam l then
        let varEnv = biInsert (l.ident,r.ident) varEnv in
        eqExprH {env with varEnv = varEnv} free l.body r.body
      else None ()
    else never
end

lang RecordEq = Eq + RecordAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmRecord r ->
    match lhs with TmRecord l then
      if eqi (mapLength l.bindings) (mapLength r.bindings) then
        mapFoldlOption
          (lam free. lam k1. lam v1.
            match mapLookup k1 r.bindings with Some v2 then
              eqExprH env free v1 v2
            else None ())
          free l.bindings
      else None ()
    else None ()

  | TmRecordUpdate r ->
    match lhs with TmRecordUpdate l then
      if eqSID l.key r.key then
        match eqExprH env free l.rec r.rec with Some free then
          eqExprH env free l.value r.value
        else None ()
      else None ()
    else None ()
end

lang LetEq = Eq + LetAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmLet {ident = i2, body = b2, inexpr = ie2} ->
    match lhs with TmLet {ident = i1, body = b1, inexpr = ie1} then
      match eqExprH env free b1 b2 with Some free then
        match env with {varEnv = varEnv} then
          let varEnv = biInsert (i1,i2) varEnv in
          eqExprH {env with varEnv = varEnv} free ie1 ie2
        else never
      else None ()
    else None ()
end

lang RecLetsEq = Eq + RecLetsAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmRecLets {bindings = bs2, inexpr = ie2} ->
    -- NOTE(dlunde,2020-09-25): This requires the bindings to occur in the same
    -- order. Do we want to allow equality of differently ordered (but equal)
    -- bindings as well?
    match env with {varEnv = varEnv} then
      match lhs with TmRecLets {bindings = bs1, inexpr = ie1} then
        if eqi (length bs1) (length bs2) then
          let bszip = zipWith (lam b1. lam b2. (b1, b2)) bs1 bs2 in
          let varEnv =
            foldl
              (lam varEnv. lam t : (RecLetBinding, RecLetBinding).
                 biInsert ((t.0).ident,(t.1).ident) varEnv)
              varEnv bszip
          in
          let env = {env with varEnv = varEnv} in
          match optionFoldlM
            (lam free. lam t : (RecLetBinding, RecLetBinding).
              eqExprH env free (t.0).body (t.1).body)
            free bszip
          with Some free then
            eqExprH env free ie1 ie2
          else None ()
        else None ()
      else None ()
    else never
end

lang ConstEq = Eq + ConstAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmConst {val = v2} ->
    match lhs with TmConst {val = v1} then
      if eqConst v1 v2 then Some free else None ()
    else None ()
end

lang TypeEq = Eq + TypeAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmType _ -> error "eqExpr not implemented for TmType!"
end

lang DataEq = Eq + DataAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmConDef {ident = i2, inexpr = ie2, ty = ty2} ->
    match env with {conEnv = conEnv} then
      match lhs with TmConDef {ident = i1, inexpr = ie1, ty = ty1} then
        let conEnv = biInsert (i1,i2) conEnv in
        eqExprH {env with conEnv = conEnv} free ie1 ie2
      else None ()
    else never

  | TmConApp {ident = i2, body = b2, ty = ty2} ->
    match lhs with TmConApp {ident = i1, body = b1, ty = ty1} then
      match (env,free) with ({conEnv = conEnv},{conEnv = freeConEnv}) then
        match _eqCheck i1 i2 conEnv freeConEnv with Some freeConEnv then
          eqExprH env {free with conEnv = freeConEnv} b1 b2
        else None ()
      else never
    else None ()
end

lang MatchEq = Eq + MatchAst
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  -- Intentionally left blank

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmMatch {target = t2, pat = p2, thn = thn2, els = els2, ty = ty2} ->
    match lhs with TmMatch {target = t1, pat = p1, thn = thn1, els = els1, ty = ty1} then
      match eqExprH env free t1 t2 with Some free then
        match eqExprH env free els1 els2 with Some free then
          match eqPat env free biEmpty p1 p2 with Some n then
            let n : (EqEnv, BiNameMap) = n in
            match n with (free, patEnv) then
              match env with {varEnv = varEnv} then
                eqExprH {env with varEnv = biMergePreferRight varEnv patEnv}
                  free thn1 thn2
              else never
            else never
          else None ()
        else None ()
      else None ()
    else None ()

end

lang UtestEq = Eq + UtestAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmUtest {test = t2, expected = e2, next = n2, tusing = u2, tonfail = o2} ->
    match lhs with
      TmUtest {test = t1, expected = e1, next = n1, tusing = u1, tonfail = o1}
    then
      match eqExprH env free t1 t2 with Some free then
        match eqExprH env free e1 e2 with Some free then
          match (u1, u2) with (Some tu1, Some tu2) then
            match eqExprH env free tu1 tu2 with Some free then
              match (o1, o2) with (Some to1, Some to2) then
                match eqExprH env free to1 to2 with Some free then
                  eqExprH env free n1 n2
                else None ()
              else
                match (o1, o2) with (None (), None ()) then
                  eqExprH env free n1 n2
                else None ()
            else None ()
          else
            match (u1, u2) with (None (), None ()) then
              match (o1, o2) with (Some to1, Some to2) then
                match eqExprH env free to1 to2 with Some free then
                  eqExprH env free n1 n2
                else None ()
              else
                match (o1, o2) with (None (), None ()) then
                  eqExprH env free n1 n2
                else None ()
            else None ()
        else None ()
      else None ()
    else None ()
end

lang SeqEq = Eq + SeqAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmSeq {tms = ts2, ty = ty2} ->
    match lhs with TmSeq {tms = ts1, ty = ty1} then
      if eqi (length ts1) (length ts2) then
        let z = zipWith (lam t1. lam t2. (t1,t2)) ts1 ts2 in
        optionFoldlM (lam free. lam tp : (Expr, Expr). eqExprH env free tp.0 tp.1) free z
      else None ()
    else None ()
end

lang NeverEq = Eq + NeverAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmNever _ -> match lhs with TmNever _ then Some free else None ()
end

lang ExtEq = Eq + ExtAst
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmExt {ident = i2, inexpr = ie2} ->
    match lhs with TmExt {ident = i1, inexpr = ie1} then
      match env with {varEnv = varEnv} in
      if nameEqStr i1 i2 then -- Externals are a bit special, as the string component of their names are required to be identical
        let varEnv = biInsert (i1,i2) varEnv in
        eqExprH {env with varEnv = varEnv} free ie1 ie2
      else None ()
    else None ()
end

---------------
-- CONSTANTS --
---------------

lang IntEq = Eq + IntAst
  sem eqConstH =
  | (CInt l, CInt r) -> eqi l.val r.val
end

lang FloatEq = Eq + FloatAst
  sem eqConstH =
  | (CFloat l, CFloat r) -> eqf l.val r.val
end

lang BoolEq = Eq + BoolAst
  sem eqConstH =
  | (CBool l, CBool r) -> eqBool l.val r.val
end

lang CharEq = Eq + CharAst
  sem eqConstH =
  | (CChar l, CChar r) -> eqChar l.val r.val
end

lang SymbEq = Eq + SymbAst
  sem eqConstH =
  | (CSymb l, CSymb r) -> eqsym l.val r.val
end

--------------
-- PATTERNS --
--------------

let _eqpatname : BiNameMap -> EqEnv -> PatName -> PatName -> Option (EqEnv, BiNameMap) =
  lam penv. lam free. lam p1. lam p2.
    match (p1,p2) with (PName i1,PName i2) then
      match biLookup (i1,i2) penv with Some n then
        let n : (Name, Name) = n in
        if and (nameEq i1 n.0) (nameEq i2 n.1) then
          Some (free,penv) -- Match in env
        else None () -- i1<->i2 is not consistent with penv
      else
        let penv = biInsert (i1,i2) penv in Some (free,penv)

    else match (p1,p2) with (PWildcard _,PWildcard _) then Some (free,penv)
    else None ()

lang NamedPatEq = MatchEq + NamedPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatNamed {ident = p2} ->
    match lhs with PatNamed {ident = p1} then
      _eqpatname patEnv free p1 p2
    else None ()
end

lang SeqTotPatEq = MatchEq + SeqTotPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatSeqTot {pats = ps2} ->
    match lhs with PatSeqTot {pats = ps1} then
      if eqi (length ps2) (length ps1) then
        let z = zipWith (lam p1. lam p2. (p1,p2)) ps1 ps2 in
        optionFoldlM (lam fpEnv. lam ps : (Pat, Pat).
          match fpEnv with (f,p) then
            eqPat env f p ps.0 ps.1
          else never)
          (free,patEnv) z
      else None ()
    else None ()
end

lang SeqEdgePatEq = MatchEq + SeqEdgePat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatSeqEdge {prefix = pre2, middle = mid2, postfix = post2} ->
    match lhs with PatSeqEdge {prefix = pre1, middle = mid1, postfix = post1} then
      match _eqpatname patEnv free mid1 mid2 with Some n then
        match n with (f,p) then
          if eqi (length pre1) (length pre2) then
            let z1 = zipWith (lam p1. lam p2. (p1,p2)) pre1 pre2 in
            let z2 = zipWith (lam p1. lam p2. (p1,p2)) post1 post2 in
            let fl = optionFoldlM (lam fpEnv. lam ps : (Pat, Pat).
              match fpEnv with (f,p) then
                eqPat env f p ps.0 ps.1
              else never)
              (free,patEnv) z1 in
            match fl with Some envs then
              if eqi (length post1) (length post2) then
                optionFoldlM (lam fpEnv. lam ps : (Pat, Pat).
                  match fpEnv with (f,p) then
                    eqPat env f p ps.0 ps.1
                  else never)
                  envs z2
              else None ()
            else None ()
          else None ()
        else never
      else None ()
    else None ()
end

lang RecordPatEq = MatchEq + RecordPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatRecord {bindings = bs2} ->
    match lhs with PatRecord {bindings = bs1} then
      if eqi (mapLength bs1) (mapLength bs2) then
        mapFoldlOption
          (lam tEnv. lam k1. lam p1.
             match tEnv with (free,patEnv) then
               match mapLookup k1 bs2 with Some p2 then
                 eqPat env free patEnv p1 p2
               else None ()
             else never)
          (free,patEnv) bs1
      else None ()
    else None ()
end

lang DataPatEq = MatchEq + DataPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatCon {ident = i2, subpat = s2} ->
    match lhs with PatCon {ident = i1, subpat = s1} then
      match (env,free) with ({conEnv = conEnv},{conEnv = freeConEnv}) then
        match _eqCheck i1 i2 conEnv freeConEnv with Some freeConEnv then
          eqPat env {free with conEnv = freeConEnv} patEnv s1 s2
        else None ()
      else never
    else None ()
end

lang IntPatEq = MatchEq + IntPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatInt {val = i2} ->
    match lhs with PatInt {val = i1} then
      if eqi i1 i2 then Some (free,patEnv) else None ()
    else None ()
end

lang CharPatEq = MatchEq + CharPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatChar {val = c2} ->
    match lhs with PatChar {val = c1} then
      if eqChar c1 c2 then Some (free,patEnv) else None ()
    else None ()
end

lang BoolPatEq = MatchEq + BoolPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatBool {val = b2} ->
    match lhs with PatBool {val = b1} then
      if eqBool b1 b2 then Some (free,patEnv) else None ()
    else None ()
end

lang AndPatEq = MatchEq + AndPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatAnd {lpat = l2, rpat = r2} ->
    match lhs with PatAnd {lpat = l1, rpat = r1} then
      match eqPat env free patEnv l1 l2 with Some envs then
        let envs : (EqEnv, BiNameMap) = envs in
        match envs with (free, patEnv) then
          eqPat env free patEnv r1 r2
        else never
      else None ()
    else None ()
end

lang OrPatEq = MatchEq + OrPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatOr {lpat = l2, rpat = r2} ->
    match lhs with PatOr {lpat = l1, rpat = r1} then
      match eqPat env free patEnv l1 l2 with Some envs then
        let envs : (EqEnv, BiNameMap) = envs in
        match envs with (free, patEnv) then
          eqPat env free patEnv r1 r2
        else never
      else None ()
    else None ()
end

lang NotPatEq = MatchEq + NotPat
  sem eqPat (env : EqEnv) (free : EqEnv) (patEnv : BiNameMap) (lhs : Pat) =
  | PatNot {subpat = p2} ->
    match lhs with PatNot {subpat = p1} then
      eqPat env free patEnv p1 p2
    else None ()
end

-----------
-- TYPES --
-----------

lang UnknownTypeEq = Eq + UnknownTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyUnknown _ ->
    match unwrapType lhs with TyUnknown _ then Some free
    else None ()
end

lang BoolTypeEq = Eq + BoolTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyBool _ ->
    match unwrapType lhs with TyBool _ then Some free
    else None ()
end

lang IntTypeEq = Eq + IntTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyInt _ ->
    match unwrapType lhs with TyInt _ then Some free
    else None ()
end

lang FloatTypeEq = Eq + FloatTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyFloat _ ->
    match unwrapType lhs with TyFloat _ then Some free
    else None ()
end

lang CharTypeEq = Eq + CharTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyChar _ ->
    match unwrapType lhs with TyChar _ then Some free
    else None ()
end

lang FunTypeEq = Eq + FunTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyArrow r ->
    match unwrapType lhs with TyArrow l then
      match eqTypeH typeEnv free l.from r.from with Some free then
        eqTypeH typeEnv free l.to r.to
      else None ()
    else None ()
end

lang SeqTypeEq = Eq + SeqTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TySeq r ->
    match unwrapType lhs with TySeq l then
      eqTypeH typeEnv free l.ty r.ty
    else None ()
end

lang TensorTypeEq = Eq + TensorTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyTensor r ->
    match unwrapType lhs with TyTensor l then
      eqTypeH typeEnv free l.ty r.ty
    else None ()
end

lang RecordTypeEq = Eq + RecordTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyRecord r ->
    match unwrapType lhs with TyRecord l then
      if eqi (mapLength l.fields) (mapLength r.fields) then
        mapFoldlOption
          (lam free. lam k1. lam v1.
            match mapLookup k1 r.fields with Some v2 then
              eqTypeH typeEnv free v1 v2
            else None ())
          free l.fields
      else None ()
    else None ()
end

lang VariantTypeEq = Eq + VariantTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyVariant r ->
    match unwrapType lhs with TyVariant l then
      if eqi (mapLength l.constrs) (mapLength r.constrs) then
        mapFoldlOption
          (lam free. lam k1. lam v1.
            match mapLookup k1 r.constrs with Some v2 then
              eqTypeH typeEnv free v1 v2
            else None ())
          free l.constrs
      else None ()
    else None ()
end

lang ConTypeEq = Eq + ConTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | rhs & TyCon r ->
    match unwrapType lhs with TyCon l then
      if nameEq l.ident r.ident then eqTypeH typeEnv free l.data r.data
      else None ()
    else None ()
end

lang DataTypeEq = Eq + DataTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | rhs & TyData r ->
    match unwrapType lhs with TyData l then
      if mapEq setEq (computeData l) (computeData r) then Some free
      else None ()
    else None ()
end

lang VarTypeEq = Eq + VarTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyVar r ->
    match lhs with TyVar l then
      optionMap
        (lam freeTyVars. {free with freeTyVars = freeTyVars})
        (_eqCheck l.ident r.ident typeEnv.tyVarEnv free.freeTyVars)
    else None ()
end

lang AllTypeEq = Eq + AllTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyAll r ->
    match unwrapType lhs with TyAll l then
      optionBind (eqKind typeEnv free (l.kind, r.kind))
        (lam free.
          eqTypeH
            {typeEnv with tyVarEnv = biInsert (l.ident, r.ident) typeEnv.tyVarEnv}
            free l.ty r.ty)
    else None ()
end

lang AppTypeEq = Eq + AppTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyApp r ->
    match unwrapType lhs with TyApp l then
      match eqTypeH typeEnv free l.lhs r.lhs with Some free then
        eqTypeH typeEnv free l.rhs r.rhs
      else None ()
    else None ()
end

lang AliasTypeEq = Eq + AliasTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyAlias t -> eqTypeH typeEnv free lhs t.content
end

lang RecordKindEq = Eq + RecordKindAst
  sem eqKind (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) =
  | (Record l, Record r) ->
      if eqi (mapSize l.fields) (mapSize r.fields) then
        mapFoldlOption
          (lam free. lam k1. lam v1.
            match mapLookup k1 r.fields with Some v2 then
              eqTypeH typeEnv free v1 v2
            else None ())
          free l.fields
      else None ()
end

lang DataKindEq = Eq + DataKindAst
  sem eqKind (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) =
  | (Data l, Data r) ->
    let recEq = lam r1. lam r2.
      if setEq r1.lower r2.lower then optionEq setEq r1.upper r2.upper
      else false
    in
    if mapEq recEq l.types r.types then Some free
    else None ()
end


-----------------------------
-- MEXPR ALPHA EQUIVALENCE --
-----------------------------

lang MExprEq =

  MExprSym

  -- Terms
  + VarEq + AppEq + LamEq + RecordEq + LetEq + RecLetsEq + ConstEq + DataEq +
  TypeEq + MatchEq + UtestEq + SeqEq + NeverEq + ExtEq

  -- Constants
  + IntEq + FloatEq + BoolEq + CharEq + SymbEq

  -- Patterns
  + NamedPatEq + SeqTotPatEq + SeqEdgePatEq + RecordPatEq + DataPatEq + IntPatEq +
  CharPatEq + BoolPatEq + AndPatEq + OrPatEq + NotPatEq

  -- Types
  + UnknownTypeEq + BoolTypeEq + IntTypeEq + FloatTypeEq + CharTypeEq +
  FunTypeEq + SeqTypeEq + RecordTypeEq + VariantTypeEq + ConTypeEq + DataTypeEq +
  VarTypeEq + AllTypeEq + AppTypeEq + TensorTypeEq + AliasTypeEq +

  -- Kinds
  RecordKindEq + DataKindEq
end

-----------
-- TESTS --
-----------

mexpr

use MExprEq in

-- Simple variables
let v1 = var_ "x" in
let v2 = var_ "y" in
utest v1 with v2 using eqExpr in
utest eqExpr (int_ 1) v1 with false in

-- Variables are equal as long as they occur in the same positions
let v3 = app_ (var_ "x") (var_ "y") in
let v4 = app_ (var_ "y") (var_ "x") in
let v5e = app_ (var_ "x") (var_ "x") in
utest v3 with v4 using eqExpr in
utest eqExpr v3 v5e with false in

-- Lambdas
let lam1 = ulam_ "x" v1 in
let lam2 = ulam_ "y" v2 in
utest lam1 with lam2 using eqExpr in
utest eqExpr (int_ 1) lam2 with false in

let lamNested1 = ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y"))) in
let lamNested2 = ulam_ "x" (ulam_ "x" (app_ (var_ "x") (var_ "x"))) in
utest eqExpr lamNested1 lamNested2 with false in
utest eqExpr lamNested2 lamNested1 with false in

let lamNested21 = ulam_ "x" (ulam_ "y" (ulam_ "x" (var_ "x"))) in
let lamNested22 = ulam_ "x" (ulam_ "y" (ulam_ "y" (var_ "y"))) in
let lamNested23 =
  ulam_ "x" (ulam_ "y" (ulam_ "x" (app_ (var_ "x") (var_ "y")))) in
let lamNested24 =
  ulam_ "x" (ulam_ "y" (ulam_ "y" (app_ (var_ "y") (var_ "y")))) in
utest lamNested21 with lamNested22 using eqExpr in
utest eqExpr lamNested23 lamNested24 with false in

-- Applications
let a1 = app_ lam1 lam2 in
let a2 = app_ lam2 lam1 in
utest a1 with a2 using eqExpr in
utest eqExpr a1 lam1 with false in

-- Records
let r1 = urecord_ [("a",lam1), ("b",a1), ("c",a2)] in
let r2 = urecord_ [("b",a1), ("a",lam2), ("c",a2)] in
let r3e = urecord_ [("a",lam1), ("b",a1), ("d",a2)] in
let r4e = urecord_ [("a",lam1), ("b",a1), ("c",lam2)] in
let r5e = urecord_ [("a",lam1), ("b",a1), ("c",a2), ("d",lam2)] in
utest r1 with r2 using eqExpr in
utest eqExpr r1 r3e with false in
utest eqExpr r1 r4e with false in
utest eqExpr r1 r5e with false in

let ru1 = recordupdate_ r1 "b" lam1 in
let ru2 = recordupdate_ r2 "b" lam2 in
let ru3e = recordupdate_ r3e "b" lam2 in
let ru4e = recordupdate_ r2 "c" lam2 in
utest ru1 with ru2 using eqExpr in
utest eqExpr ru1 ru3e with false in
utest eqExpr ru1 ru4e with false in

-- Let and recursive let
let let1 = bind_ (ulet_ "x" lam1) a1 in
let let2 = bind_ (ulet_ "y" lam2) a2 in
let let3e = bind_ (ulet_ "x" (int_ 1)) a1 in
let let4e = bind_ (ulet_ "x" lam2) lam1 in
utest let1 with let2 using eqExpr in
utest eqExpr let1 let3e with false in
utest eqExpr let1 let4e with false in

let rlet1 = ureclets_ [("x", a1), ("y", lam1)] in
let rlet2 = ureclets_ [("x", a2), ("y", lam2)] in
let rlet3 = ureclets_ [("y", a2), ("x", lam2)] in
let rlet4e = ureclets_ [("y", lam1), ("x", a1)] in -- Order matters
utest rlet1 with rlet2 using eqExpr in
utest rlet1 with rlet3 using eqExpr in
utest eqExpr rlet1 rlet4e with false in

-- Constants
let c1 = (int_ 1) in
let c2 = (int_ 2) in
let c3 = (true_) in

utest c1 with c1 using eqExpr in
utest eqExpr c1 c2 with false in
utest eqExpr c1 c3 with false in

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
utest cda1 with cda2 using eqExpr in
utest eqExpr cda1 cd3e with false in

-- Match and patterns
let m1 = match_ c1 (pint_ 1) cda1 rlet1 in
let m2 = match_ c1 (pint_ 1) cda2 rlet2 in
let m3e = match_ rlet1 (pint_ 1) cda2 rlet2 in
let m4e = match_ c1 (pint_ 1) c1 rlet2 in
let m5e = match_ c1 (pint_ 1) cda2 cda1 in
utest m1 with m2 using eqExpr in
utest eqExpr m1 m3e with false in
utest eqExpr m1 m4e with false in
utest eqExpr m1 m5e with false in

let pgen = lam p. match_ (int_ 1) p (int_ 2) (int_ 3) in
let pvar1 = pvar_ "x" in
let pvar2 = pvar_ "y" in
utest pgen pvar1 with pgen pvar2 using eqExpr in
utest eqExpr (pgen pvar1) (pgen (pint_ 1)) with false in

let prec1 = prec_ [("a",pvar1), ("b",pvar2), ("c",pvar1)] in
let prec2 = prec_ [("a",pvar2), ("b",pvar1), ("c",pvar2)] in
let prec3e = prec_ [("a",pvar2), ("b",pvar2), ("c",pvar1)] in
let prec4e = prec_ [("a",pvar2), ("b",pvar2), ("c",pvar1)] in
utest pgen prec1 with pgen prec2 using eqExpr in
utest eqExpr (pgen prec1) (pgen prec3e) with false in

let pdata1 = pcon_ "Const1" (pcon_ "Const2" prec1) in
let pdata2 = pcon_ "Const2" (pcon_ "Const1" prec1) in
let pdata3e = pcon_ "Const1" (pcon_ "Const1" prec1) in
utest pgen pdata1 with pgen pdata2 using eqExpr in
utest eqExpr (pgen pdata1) (pgen pdata3e) with false in

let pint1 = pint_ 1 in
let pint2 = pint_ 1 in
let pint3e = pint_ 2 in
utest pgen pint1 with pgen pint2 using eqExpr in
utest eqExpr (pgen pint1) (pgen pint3e) with false in

let pchar1 = pchar_ 'a' in
let pchar2 = pchar_ 'a' in
let pchar3e = pchar_ 'b' in
utest pgen pchar1 with pgen pchar2 using eqExpr in
utest eqExpr (pgen pchar1) (pgen pchar3e) with false in

let pbool1 = ptrue_ in
let pbool2 = ptrue_ in
let pbool3e = pfalse_ in
utest pgen pbool1 with pgen pbool2 using eqExpr in
utest eqExpr (pgen pbool1) (pgen pbool3e) with false in

let pand1 = pand_ pbool1 pbool1 in
let pand2 = pand_ pbool2 pbool2 in
let pand3 = pand_ pbool2 pbool3e in
let pand4 = pand_ pbool3e pbool2 in
let pand5 = pand_ pdata1 pchar1 in
let pand6 = pand_ pdata2 pchar2 in
let pand7 = pand_ pdata2 pchar3e in
let pand8 = pand_ pvar1 pbool1 in
let pand9 = pand_ pvar2 pbool1 in
let pand10 = pand_ pvar1 prec1 in
let pand11 = pand_ pvar2 prec2 in
let pand12 = pand_ pvar1 pdata1 in
let pand13 = pand_ pvar2 pdata2 in
utest pgen (pand_ pand1 pand2) with pgen (pand_ pand1 pand2) using eqExpr in
utest pgen pand5 with pgen pand6 using eqExpr in
utest pgen pand8 with pgen pand9 using eqExpr in
utest pgen pand10 with pgen pand11 using eqExpr in
utest eqExpr (pgen pand1) (pgen pand3) with false in
utest eqExpr (pgen pand3) (pgen pand4) with false in
utest eqExpr (pgen pand6) (pgen pand7) with false in
utest eqExpr (pgen pand12) (pgen pand13) with false in

let por1 = por_ pbool1 pbool1 in
let por2 = por_ pbool2 pbool2 in
let por3 = por_ pbool2 pbool3e in
let por4 = por_ pbool3e pbool2 in
let por5 = por_ pdata1 pchar1 in
let por6 = por_ pdata2 pchar2 in
let por7 = por_ pdata2 pchar3e in
let por8 = por_ pvar1 pbool1 in
let por9 = por_ pvar2 pbool1 in
let por10 = por_ pvar1 prec1 in
let por11 = por_ pvar2 prec2 in
let por12 = por_ pvar1 pdata1 in
let por13 = por_ pvar2 pdata2 in
utest pgen por1 with pgen por2 using eqExpr in
utest pgen por5 with pgen por6 using eqExpr in
utest pgen por8 with pgen por9 using eqExpr in
utest pgen por10 with pgen por11 using eqExpr in
utest eqExpr (pgen por1) (pgen por3) with false in
utest eqExpr (pgen por3) (pgen por4) with false in
utest eqExpr (pgen por6) (pgen por7) with false in
utest eqExpr (pgen por12) (pgen por13) with false in

let pnot1 = pnot_ pbool1 in
let pnot2 = pnot_ pbool2 in
let pnot3 = pnot_ pbool3e in
let pnot4 = pnot_ pdata1 in
let pnot5 = pnot_ pdata2 in
let pnot6 = pnot_ pnot1 in
let pnot7 = pnot_ pnot2 in
let pnot8 = pnot_ pvar1 in
let pnot9 = pnot_ pvar2 in
utest pgen pnot1 with pgen pnot2 using eqExpr in
utest pgen pnot4 with pgen pnot5 using eqExpr in
utest pgen pnot6 with pgen pnot7 using eqExpr in
utest pgen pnot8 with pgen pnot9 using eqExpr in
utest eqExpr (pgen pnot4) (pgen pnot6) with false in
utest eqExpr (pgen pnot3) (pgen pnot6) with false in

let pSeqTot1 = pseqtot_ [ptrue_, pfalse_] in
let pSeqTot2 = pseqtot_ [ptrue_, pfalse_] in
let pSeqTot3 = pseqtot_ [pfalse_, pfalse_] in
let pSeqTot4 = pseqtot_ [pfalse_, pfalse_,pfalse_] in
let pSeqTot5 = pseqtot_ [por1,pfalse_,pfalse_] in
let pSeqTot6 = pseqtot_ [por2,pfalse_,pfalse_] in
let pSeqTot7 = pseqtot_ [pvar1,pfalse_,pfalse_] in
let pSeqTot8 = pseqtot_ [pvar2,pfalse_,pfalse_] in
let pSeqTot9 = pseqtot_ [pvar2,pdata1,pfalse_] in
let pSeqTot10 = pseqtot_ [pvar2,pdata2,pfalse_] in
let pSeqTot11 = pseqtot_ [pvar2,pdata3e,pfalse_] in
let pSeqTot12 = pseqtot_ [pvar1,pdata1,pfalse_] in
utest pgen pSeqTot1 with pgen pSeqTot2 using eqExpr in
utest pgen pSeqTot5 with pgen pSeqTot6 using eqExpr in
utest pgen pSeqTot7 with pgen pSeqTot8 using eqExpr in
utest pgen pSeqTot9 with pgen pSeqTot10 using eqExpr in
utest eqExpr (pgen pSeqTot2) (pgen pSeqTot3) with false in
utest eqExpr (pgen pSeqTot3) (pgen pSeqTot4) with false in
utest eqExpr (pgen pSeqTot8) (pgen pSeqTot9) with false in
utest eqExpr (pgen pSeqTot10) (pgen pSeqTot11) with false in
utest eqExpr (pgen pSeqTot10) (pgen pSeqTot12) with false in

let pSeqEdge1 = pseqedgew_ [pint_ 1, pint_ 2] [pint_ 3] in
let pSeqEdge2 = pseqedgew_ [pint_ 1, pint_ 2] [pint_ 3] in
let pSeqEdge3 = pseqedgew_ [pint_ 2, pint_ 3] [pint_ 4] in
let pSeqEdge4 = pseqedgew_ [pSeqTot1, pint_ 2] [pint_ 3] in
let pSeqEdge5 = pseqedgew_ [pSeqTot2, pint_ 2] [pint_ 3] in
let pSeqEdge6 = pseqedgew_ [pSeqTot2, pint_ 2] [pint_ 3,pint_ 4] in
let pSeqEdge7 = pseqedgew_ [pSeqTot2] [pint_ 3,pint_ 4] in
let pSeqEdge8 = pseqedgew_ [pvar1] [pint_ 3,pint_ 4] in
let pSeqEdge9 = pseqedgew_ [pvar2] [pint_ 3,pint_ 4] in
let pSeqEdge10 = pseqedgew_ [pvar2] [pdata1,pint_ 4] in
let pSeqEdge11 = pseqedgew_ [pvar2] [pdata2,pint_ 4] in
let pSeqEdge12 = pseqedge_ [pvar2] "x" [pdata1,pint_ 4] in
let pSeqEdge13 = pseqedge_ [pvar2] "y" [pdata2,pint_ 4] in
let pSeqEdge14 = pseqedge_ [pvar2] "x" [pdata3e,pint_ 4] in
let pSeqEdge15 = pseqedge_ [pdata3e] "x" [pdata3e,pint_ 4] in
utest pgen pSeqEdge1 with pgen pSeqEdge2 using eqExpr in
utest pgen pSeqEdge4 with pgen pSeqEdge5 using eqExpr in
utest pgen pSeqEdge8 with pgen pSeqEdge9 using eqExpr in
utest pgen pSeqEdge10 with pgen pSeqEdge11 using eqExpr in
utest pgen pSeqEdge12 with pgen pSeqEdge13 using eqExpr in
utest eqExpr (pgen pSeqEdge2) (pgen pSeqEdge3) with false in
utest eqExpr (pgen pSeqEdge3) (pgen pSeqEdge4) with false in
utest eqExpr (pgen pSeqEdge5) (pgen pSeqEdge6) with false in
utest eqExpr (pgen pSeqEdge6) (pgen pSeqEdge7) with false in
utest eqExpr (pgen pSeqEdge11) (pgen pSeqEdge12) with false in
utest eqExpr (pgen pSeqEdge13) (pgen pSeqEdge14) with false in
utest eqExpr (pgen (pand_ (pand_ pSeqEdge14 pSeqEdge3) pSeqEdge3)) (pgen (pand_ (pand_ pSeqEdge15 pSeqEdge3) pSeqEdge3)) with false in

let x = match_ false_ (pand_ (pvar_ "a") (pvar_ "b")) (var_ "a") true_ in
let y = match_ false_ (pand_ (pvar_ "x") (pvar_ "y")) (var_ "x") true_ in
utest x with y using eqExpr in
utest symbolize x with x using eqExpr in
utest symbolize y with y using eqExpr in
let x = match_ false_ (pand_ (pvar_ "a") (pvar_ "a")) (var_ "a") true_ in
let y = match_ false_ (pand_ (pvar_ "x") (pvar_ "x")) (var_ "x") true_ in
utest symbolize x with x using eqExpr in
utest symbolize y with y using eqExpr in
utest x with y using eqExpr in
let x = match_ false_ (pand_ (pvar_ "a") (pvar_ "a")) (var_ "a") true_ in
let y = match_ false_ (pand_ (pvar_ "x") (pvar_ "y")) (var_ "x") true_ in
utest symbolize x with x using eqExpr in
utest symbolize y with y using eqExpr in
utest x with y using lam a. lam b. not (eqExpr a b) in
let x = match_ false_ (pand_ (pvar_ "a") (pvar_ "b")) (var_ "a") true_ in
let y = match_ false_ (pand_ (pvar_ "x") (pvar_ "y")) (var_ "y") true_ in
utest symbolize x with x using eqExpr in
utest symbolize y with y using eqExpr in
utest x with y using lam a. lam b. not (eqExpr a b) in
let x = match_ false_ (por_ (pvar_ "a") (pvar_ "b")) (var_ "a") true_ in
let y = match_ false_ (por_ (pvar_ "x") (pvar_ "y")) (var_ "x") true_ in
utest symbolize x with x using eqExpr in
utest symbolize y with y using eqExpr in
utest x with y using eqExpr in
let x = match_ (var_ "a") (por_ (pvar_ "a") (pvar_ "b")) (var_ "a") true_ in
let y = match_ (var_ "x") (por_ (pvar_ "z") (pvar_ "y")) (var_ "z") true_ in
utest x with y using eqExpr in
let x = match_ false_
  (pand_
    (pseqedge_ [pvar_ "x"] "a" [pvar_ "y", pvar_ "y"])
    (pseqedge_ [pvar_ "x"] "a" [pvar_ "y", pvar_ "y"]))
  (var_ "a") true_ in
let y = match_ false_
  (pand_
    (pseqedge_ [pvar_ "x"] "a" [pvar_ "z", pvar_ "z"])
    (pseqedge_ [pvar_ "x"] "a" [pvar_ "z", pvar_ "z"]))
  (var_ "a") true_ in
utest x with y using eqExpr in
let x = match_ false_
  (pand_
    (pseqedge_ [pvar_ "x"] "x" [pvar_ "x", pvar_ "x"])
    (pseqedge_ [pvar_ "x"] "x" [pvar_ "x", pvar_ "x"]))
  (var_ "a") true_ in
let y = match_ false_
  (pand_
    (pseqedge_ [pvar_ "a"] "a" [pvar_ "a", pvar_ "a"])
    (pseqedge_ [pvar_ "a"] "a" [pvar_ "a", pvar_ "a"]))
  (var_ "a") true_ in
utest x with y using lam a. lam b. not (eqExpr a b) in
let x = match_ false_
  (pand_
    (pseqedge_ [pvar_ "x"] "x" [pvar_ "x", pvar_ "x"])
    (pseqedge_ [pvar_ "x"] "x" [pvar_ "x", pvar_ "x"]))
  (var_ "a") true_ in
let y = match_ false_
  (pand_
    (pseqedge_ [pvar_ "a"] "a" [pvar_ "a", pvar_ "a"])
    (pseqedge_ [pvar_ "a"] "a" [pvar_ "a", pvar_ "a"]))
  (var_ "z") true_ in
utest x with y using eqExpr in
let x = match_ false_
  (por_
    (pseqedge_ [pvar_ "x"] "x" [pvar_ "x", pvar_ "x"])
    (pseqedge_ [pvar_ "x"] "x" [pvar_ "x", pvar_ "x"]))
  (var_ "a") true_ in
let y = match_ false_
  (por_
    (pseqedge_ [pvar_ "a"] "a" [pvar_ "a", pvar_ "a"])
    (pseqedge_ [pvar_ "a"] "a" [pvar_ "a", pvar_ "a"]))
  (var_ "z") true_ in
utest x with y using eqExpr in

-- Types
let x = nameSym "x" in
let y = nameSym "y" in
let f = nameSym "f" in
let t = nameSym "T" in
let letexpr = lam ty.
  nlet_ x ty (app_ (nvar_ f) (nvar_ y))
in

let letu = letexpr tyunknown_ in
let letb = letexpr tybool_ in
let leti = letexpr tyint_ in
let letfl = letexpr tyfloat_ in
let letch = letexpr tychar_ in
utest tyunknown_ with tyunknown_ using eqType in
utest tybool_ with tybool_ using eqType in
utest tyint_ with tyint_ using eqType in
utest tyfloat_ with tyfloat_ using eqType in
utest tychar_ with tychar_ using eqType in
utest eqType tyunknown_ tybool_ with false in
utest eqType tybool_ tyint_ with false in
utest eqType tyint_ tyfloat_ with false in
utest eqType tyint_ tychar_ with false in

let tyarr1 = tyarrow_ tyunknown_ tyunknown_ in
let tyarr2 = tyarrow_ tyint_ tyunknown_ in
let tyarr3 = tyarrow_ tyunknown_ tyint_ in
let tyarr4 = tyarrow_ (tyarrow_ tyint_ tyint_) tyint_ in
let tyseq = lam ty. tyseq_ ty in
let tyrec1 = tyrecord_ [("0", tyint_), ("1", tyunknown_)] in
let tyrec2 = tyrecord_ [("1", tyunknown_), ("0", tyunknown_)] in
let tyrec3 = tytuple_ [tyunknown_, tyunknown_] in
utest tyarr1 with tyarr1 using eqType in
utest tyarr2 with tyarr2 using eqType in
utest tyarr3 with tyarr3 using eqType in
utest tyarr4 with tyarr4 using eqType in
utest eqType tyarr1 tyarr2 with false in
utest eqType tyarr2 tyarr3 with false in
utest eqType tyarr3 tyarr4 with false in
utest tystr_ with tystr_ using eqType in
utest tyseq tyint_ with tyseq tyint_ using eqType in
utest tytensor_ tyint_ with tytensor_ tyint_ using eqType in
utest eqType tystr_ (tyseq tyint_) with false in
utest tyrec1 with tyrec1 using eqType in
utest tyrec2 with tyrec3 using eqType in
utest eqType tyrec1 tyrec2 with false in

utest eqType (ntycon_ t) tyint_ with false in
utest eqType tyint_ (ntycon_ t) with false in
utest tyalias_ (ntycon_ t) tyint_ with tyint_ using eqType in
utest tyint_ with tyalias_ (ntycon_ t) tyint_ using eqType in
utest eqType (tyalias_ (ntycon_ t) tyint_) tybool_ with false in
utest tyalias_ (ntycon_ t) tybool_ with tybool_ using eqType in

let tyApp1 = tyapp_ tyint_ tyint_ in
let tyApp2 = tyapp_ (tyalias_ (ntycon_ t) tyint_) tyint_ in
let tyApp3 = tyapp_ tyint_ (tyalias_ (ntycon_ t) tybool_) in
utest tyApp1 with tyApp1 using eqType in
utest tyApp2 with tyApp2 using eqType in
utest tyApp3 with tyApp3 using eqType in
utest tyApp1 with tyApp2 using eqType in
utest eqType tyApp2 tyApp3 with false in
utest eqType tyApp1 tyApp3 with false in

let tyVar1 = tyarrow_ (tyvar_ "a") (tyvar_ "a") in
let tyVar2 = tyarrow_ (tyvar_ "b") (tyvar_ "b") in
let tyVar3 = tyarrow_ (tyvar_ "a") (tyvar_ "b") in
let tyVar4 = tyarrow_ (tyvar_ "a") (tyvar_ "c") in
let tyAll1 = tyall_ "a" tyVar1 in
let tyAll2 = tyall_ "b" tyVar1 in
let tyAll3 = tyall_ "b" tyVar2 in
let tyAll4 = tyall_ "a" tyVar3 in
let tyAll5 = tyall_ "a" tyVar4 in
let tyAll6 = tyall_ "b" tyVar3 in
let tyAll7 = tyall_ "c" tyVar4 in
utest tyVar1 with tyVar2 using eqType in
utest tyVar3 with tyVar4 using eqType in
utest tyAll1 with tyAll3 using eqType in
utest tyAll4 with tyAll5 using eqType in
utest tyAll6 with tyAll7 using eqType in
utest eqType tyVar1 tyVar3 with false in
utest eqType tyAll1 tyAll2 with false in
utest eqType tyAll1 tyAll4 with false in
utest eqType tyAll2 tyAll4 with false in
utest eqType tyAll4 tyAll6 with false in

-- Utest
let ut1 = utest_ lam1 lam2 v3 in
let ut2 = utest_ lam2 lam1 v4 in
let ut3e = utest_ v5e lam2 v3 in
let ut4e = utest_ lam1 v5e v3 in
let ut5e = utest_ lam1 lam2 v5e in
utest ut1 with ut2 using eqExpr in
utest eqExpr ut1 ut3e with false in
utest eqExpr ut1 ut4e with false in
utest eqExpr ut1 ut5e with false in
let ut1 = utestu_ lam1 lam2 v3 v4 in
let ut2 = utestu_ lam2 lam1 v4 v3 in
utest ut1 with ut2 using eqExpr in
let ut1 = utestuo_ lam1 lam2 v3 v4 v3 in
let ut2 = utestuo_ lam2 lam1 v4 v3 v4 in
utest ut1 with ut2 using eqExpr in

-- Sequences
let s1 = seq_ [lam1, lam2, v3] in
let s2 = seq_ [lam2, lam1, v4] in
let s3e = seq_ [lam1, v5e, v3] in
utest s1 with s2 using eqExpr in
utest eqExpr s1 s3e with false in
utest eqExpr (seq_ [c1]) (seq_ [c2]) with false in

-- Never
utest never_ with never_ using eqExpr in
utest eqExpr never_ true_ with false in

-- Ext
let ext1 = bind_ (ext_ "x" false tyunit_) a1 in
let ext2 = bind_ (ext_ "y" false tyunit_) a2 in
utest ext1 with ext1 using eqExpr in
utest eqExpr ext1 ext2 with false in

-- Symbolized (and partially symbolized) terms are also supported.
let sm = symbolize in
utest sm lamNested21 with sm lamNested22 using eqExpr in
utest lamNested21 with sm lamNested22 using eqExpr in
utest eqExpr (sm lamNested23) (sm lamNested24) with false in

()
