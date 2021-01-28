-- Symbolization of the MExpr ast. Ignores already symbolized variables,
-- constructors, and type variables.
--
-- NOTE(dlunde,2020-09-25):
-- * Add support for unbound variables and constructors (similarly to eq.mc)?

include "name.mc"
include "string.mc"
include "assoc.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

---------------------------
-- SYMBOLIZE ENVIRONMENT --
---------------------------
-- NOTE(dlunde,2020-09-25): The environment differs from boot, since we do not
-- have access to the unique string identifiers from ustring.ml. Instead, we
-- use strings directly.

type SymEnv = {
  varEnv: AssocMap String Name,
  conEnv: AssocMap String Name,
  tyEnv: AssocMap String Name
}

let symEnvEmpty =
  {varEnv = assocEmpty, conEnv = assocEmpty, tyEnv = assocEmpty}

-----------
-- TERMS --
-----------

lang Sym
  sem symbolizeExpr (env : SymEnv) =
  -- Intentionally left blank

  sem symbolize =
  | expr -> symbolizeExpr symEnvEmpty expr

end

lang VarSym = Sym + VarAst
  sem symbolizeExpr (env : SymEnv) =
  | TmVar t & var ->
    match env with {varEnv = varEnv} then
      if nameHasSym t.ident then var
      else
        let str = nameGetStr t.ident in
        match assocLookup {eq=eqString} str varEnv with Some ident then
          TmVar {t with ident = ident}
        else error (concat "Unknown variable in symbolizeExpr: " str)
    else never
end

lang AppSym = Sym + AppAst
  sem symbolizeExpr (env : SymEnv) =
  | TmApp t ->
    TmApp {{t with lhs = symbolizeExpr env lhs}
              with rhs = symbolizeExpr env rhs}
end

lang FunSym = Sym + FunAst + VarSym + AppSym
  sem symbolizeType (env : SymEnv) =
  -- Intentinally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmLam {ident = ident, ty = ty, body = body} ->
    match env with {varEnv = varEnv} then
      let ty = symbolizeType env ty in
      if nameHasSym ident then
        TmLam {ident = ident, ty = ty, body = symbolizeExpr env body}
      else
        let ident = nameSetNewSym ident in
        let str = nameGetStr ident in
        let varEnv = assocInsert {eq=eqString} str ident varEnv in
        let env = {env with varEnv = varEnv} in
        TmLam {ident = ident, ty = ty, body = symbolizeExpr env body}
    else never
end

lang RecordSym = Sym + RecordAst
  sem symbolizeExpr (env : SymEnv) =
  | TmRecord {bindings = bindings} ->
    TmRecord {bindings = assocMap {eq=eqString} (symbolizeExpr env) bindings}

  | TmRecordUpdate {rec = rec, key = key, value = value} ->
    TmRecordUpdate {rec = symbolizeExpr env rec, key = key,
                    value = symbolizeExpr env value}
end

lang LetSym = Sym + LetAst
  sem symbolizeType (env : SymEnv) =
  -- Intentinally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmLet {ident = ident, ty = ty, body = body, inexpr = inexpr} ->
    match env with {varEnv = varEnv} then
      let ty = symbolizeType env ty in
      let body = symbolizeExpr env body in
      if nameHasSym ident then
        TmLet {ident = ident, ty = ty, body = body,
               inexpr = symbolizeExpr env inexpr}
      else
        let ident = nameSetNewSym ident in
        let str = nameGetStr ident in
        let varEnv = assocInsert {eq=eqString} str ident varEnv in
        let env = {env with varEnv = varEnv} in
        TmLet {ident = ident, ty = ty, body = body,
               inexpr = symbolizeExpr env inexpr}
    else never
end

lang TypeSym = Sym + TypeAst
  sem symbolizeType (env : SymEnv) =
  -- Intentinally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmType {ident = ident, ty = ty, inexpr = inexpr} ->
    match env with {tyEnv = tyEnv} then
      let ty = symbolizeType env ty in
      if nameHasSym ident then
        TmType {ident = ident, ty = ty, inexpr = symbolizeExpr env inexpr}
      else
        let ident = nameSetNewSym ident in
        let str = nameGetStr ident in
        let tyEnv = assocInsert {eq=eqString} str ident tyEnv in
        let env = {env with tyEnv = tyEnv} in
        TmType {ident = ident, ty = ty, inexpr = symbolizeExpr env inexpr}
    else never
end

lang RecLetsSym = Sym + RecLetsAst
  sem symbolizeExpr (env : SymEnv) =
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    match env with {varEnv = varEnv} then

    -- Generate fresh symbols for all identifiers
    let bindings =
      map (lam bind.
             if nameHasSym bind.ident then bind
             else {bind with ident = nameSetNewSym bind.ident})
        bindings in

    -- Add all identifiers to environment
    let varEnv =
      foldl
        (lam varEnv. lam bind.
           assocInsert {eq=eqString} (nameGetStr bind.ident) bind.ident varEnv)
        varEnv bindings in
    let env = {env with varEnv = varEnv} in

    -- Symbolize all bodies with the new environment
    let bindings =
      map (lam bind. {bind with body = symbolizeExpr env bind.body})
        bindings in

    TmRecLets {bindings = bindings, inexpr = symbolizeExpr env inexpr}

    else never
end

lang ConstSym = Sym + ConstAst
  sem symbolizeExpr (env : SymEnv) =
  | TmConst t -> TmConst t
end

lang DataSym = Sym + DataAst
  sem symbolizeType (env : SymEnv) =
  -- Intentinally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmConDef {ident = ident, ty = ty, inexpr = inexpr} ->
    match env with {conEnv = conEnv} then
      let ty = symbolizeType env ty in
      if nameHasSym ident then
        TmConDef {ident = ident, ty = ty, inexpr = symbolizeExpr env inexpr}
      else
        let str = nameGetStr ident in
        let ident = nameSetNewSym ident in
        let conEnv = assocInsert {eq=eqString} str ident conEnv in
        let env = {env with conEnv = conEnv} in
        TmConDef {ident = ident, ty = ty, inexpr = symbolizeExpr env inexpr}
    else never

  | TmConApp {ident = ident, body = body} ->
    match env with {conEnv = conEnv} then
      if nameHasSym ident then
        TmConApp {ident = ident, body = symbolizeExpr env body}
      else
        let str = nameGetStr ident in
        match assocLookup {eq=eqString} str conEnv with Some ident then
          TmConApp {ident = ident, body = symbolizeExpr env body}
        else error (concat "Unknown constructor in symbolizeExpr: " str)
    else never
end

lang MatchSym = Sym + MatchAst
  -- TODO(vipa, 2020-09-23): env is constant throughout symbolizePat,
  -- so it would be preferrable to pass it in some other way, a reader
  -- monad or something. patEnv on the other hand changes, it would be
  -- nice to pass via state monad or something.  env is the
  -- environment from the outside, plus the names added thus far in
  -- the pattern patEnv is only the newly added names
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  -- Intentionally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    match symbolizePat env assocEmpty pat
    with (thnVarEnv, pat) then
      let m = assocMergePreferRight {eq=eqString} in
      let thnPatEnv = {env with varEnv = m env.varEnv thnVarEnv} in
      TmMatch {target = symbolizeExpr env target,
               pat = pat, thn = symbolizeExpr thnPatEnv thn,
               els = symbolizeExpr env els}
    else never
end

lang UtestSym = Sym + UtestAst
  sem symbolizeExpr (env : SymEnv) =
  | TmUtest {test = test, expected = expected, next = next} ->
    TmUtest {test = symbolizeExpr env test,
             expected = symbolizeExpr env expected,
             next = symbolizeExpr env next}
end

lang SeqSym = Sym + SeqAst
  sem symbolizeExpr (env : SymEnv) =
  | TmSeq {tms = tms} -> TmSeq {tms = map (symbolizeExpr env) tms}
end

lang NeverSym = Sym + NeverAst
  sem symbolizeExpr (env : SymEnv) =
  | TmNever {} -> TmNever {}
end

-----------
-- TYPES --
-----------

lang UnknownTypeSym = UnknownTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyUnknown _ & ty -> ty
end

lang BoolTypeSym = BoolTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyBool {} & ty -> ty
end

lang IntTypeSym = IntTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyInt {} & ty -> ty
end

lang FloatTypeSym = FloatTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyFloat {} & ty -> ty
end

lang CharTypeSym = CharTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyChar {} & ty -> ty
end

lang FunTypeSym = FunTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyArrow {from = from, to = to} ->
    TyArrow {from = symbolizeType env from, to = symbolizeType env to}
end

lang SeqTypeSym = SeqTypeAst
  sem symbolizeType (env : SymEnv) =
  | TySeq {ty = ty} -> TySeq {ty = symbolizeType env ty}
end

lang RecordTypeSym = RecordTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyRecord {fields = fields} ->
    TyRecord {fields = assocMap {eq=eqString} (symbolizeType env) fields}
end

lang VariantTypeSym = VariantTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyVariant {constrs = []} & ty -> ty
  | TyVariant t -> error "Symbolizing non-empty variant types not yet supported"
end

lang VarTypeSym = VarTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyVar {ident = ident} & ty ->
    match env with {tyEnv = tyEnv} then
      if nameHasSym ident then ty
      else
        let str = nameGetStr ident in
        match assocLookup {eq=eqString} str tyEnv with Some ident then
          TyVar {ident = ident}
        else error (concat "Unknown type variable in symbolizeExpr: " str)
    else never
end

lang AppTypeSym = AppTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyApp {lhs = lhs, rhs = rhs} ->
    TyApp {lhs = symbolizeType env lhs, rhs = symbolizeType env rhs}
end

--------------
-- PATTERNS --
--------------

let _symbolize_patname: SymEnv -> PatName -> (SymEnv, PatName) =
  lam varEnv. lam pname.
    match pname with PName name then
      if nameHasSym name then (varEnv, PName name)
      else
        let str = nameGetStr name in
        let res = assocLookup {eq=eqString} str varEnv in
        match res with Some name then (varEnv, PName name)
        else match res with None () then
          let name = nameSetNewSym name in
          let varEnv = assocInsert {eq=eqString} str name varEnv in
          (varEnv, PName name)
        else never
    else match pname with PWildcard () then (varEnv, PWildcard ())
    else never

lang NamedPatSym = NamedPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PNamed p ->
    match _symbolize_patname patEnv p.ident with (patEnv, patname) then
      (patEnv, PNamed {p with ident = patname})
    else never
end

lang SeqTotPatSym = SeqTotPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PSeqTot p ->
    let res = mapAccumL (symbolizePat env) patEnv p.pats in
    (res.0, PSeqTot {p with pats = res.1})
end

lang SeqEdgePatSym = SeqEdgePat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PSeqEdge p ->
    let preRes = mapAccumL (symbolizePat env) patEnv p.prefix in
    let midRes = _symbolize_patname preRes.0 p.middle in
    let postRes = mapAccumL (symbolizePat env) midRes.0 p.postfix in
    (postRes.0, PSeqEdge
      {{{p with prefix = preRes.1} with middle = midRes.1} with postfix = postRes.1})
end

lang RecordPatSym = RecordPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PRecord {bindings = bindings} ->
    match assocMapAccum {eq=eqString}
            (lam patEnv. lam _. lam p. symbolizePat env patEnv p) patEnv bindings
    with (env,bindings) then
      (env, PRecord {bindings = bindings})
    else never
end

lang DataPatSym = DataPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PCon {ident = ident, subpat = subpat} ->
    match env with {conEnv = conEnv} then
      let ident =
        if nameHasSym ident then ident
        else
          let str = nameGetStr ident in
          match assocLookup {eq=eqString} str conEnv with Some ident then ident
          else error (concat "Unknown constructor in symbolizeExpr: " str)
      in
      match symbolizePat env patEnv subpat with (patEnv, subpat) then
        (patEnv, PCon {ident = ident, subpat = subpat})
      else never
    else never
end

lang IntPatSym = IntPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PInt i -> (patEnv, PInt i)
end

lang CharPatSym = CharPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PChar c -> (patEnv, PChar c)
end

lang BoolPatSym = BoolPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PBool b -> (patEnv, PBool b)
end

lang AndPatSym = AndPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PAnd p ->
    let lRes = symbolizePat env patEnv p.lpat in
    let rRes = symbolizePat env lRes.0 p.rpat in
    (rRes.0, PAnd {{p with lpat = lRes.1} with rpat = rRes.1})
end

lang OrPatSym = OrPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | POr p ->
    let lRes = symbolizePat env patEnv p.lpat in
    let rRes = symbolizePat env lRes.0 p.rpat in
    (rRes.0, POr {{p with lpat = lRes.1} with rpat = rRes.1})
end

lang NotPatSym = NotPat
  sem symbolizePat (env : SymEnv) (patEnv : AssocMap String Name) =
  | PNot p ->
    -- NOTE(vipa, 2020-09-23): new names in a not-pattern do not
    -- matter since they will never bind (it should probably be an
    -- error to bind a name inside a not-pattern, but we're not doing
    -- that kind of static checks yet.  Note that we still need to run
    -- symbolizeExpr though, constructors must refer to the right symbol.
    let res = symbolizePat env patEnv p.subpat in
    (patEnv, PNot {p with subpat = res.1})
end

------------------------------
-- MEXPR SYMBOLIZE FRAGMENT --
------------------------------

lang MExprSym =

  -- Terms
  VarSym + AppSym + FunSym + RecordSym + LetSym + TypeSym + RecLetsSym +
  ConstSym + DataSym + MatchSym + UtestSym + SeqSym + NeverSym +

  -- Types
  UnknownTypeSym + BoolTypeSym + IntTypeSym + FloatTypeSym + CharTypeSym +
  FunTypeSym + SeqTypeSym + RecordTypeSym + VariantTypeSym + VarTypeSym +
  AppTypeSym +

  -- Patterns
  NamedPatSym + SeqTotPatSym + SeqEdgePatSym + RecordPatSym + DataPatSym +
  IntPatSym + CharPatSym + BoolPatSym + AndPatSym + OrPatSym + NotPatSym

-----------
-- TESTS --
-----------
-- It is difficult to directly do unit testing for the above due to the nature
-- of symbols, so we are just evaluating the below for errors. Unit
-- testing in eval.mc also implicitly covers symbolizeExpr.

lang TestLang = MExprSym + MExprPrettyPrint

mexpr

use TestLang in

let base = (ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y")))) in

let rec = record_ [("k1", base), ("k2", (int_ 1)), ("k3", (int_ 2))] in

let letin = bind_ (ulet_ "x" rec) (app_ (var_ "x") base) in

let lettypein = bindall_ [
  type_ "Type" tystr_,
  type_ "Type" (tyvar_ "Type"),
  lam_ "Type" (tyvar_ "Type") (var_ "Type")
] in

let rlets =
  bind_ (ureclets_ [("x", (var_ "y")), ("y", (var_ "x"))])
    (app_ (var_ "x") (var_ "y")) in

let const = int_ 1 in

let data = bind_ (ucondef_ "Test") (conapp_ "Test" base) in

let varpat = match_ unit_ (pvar_ "x") (var_ "x") base in

let recpat =
  match_ base
    (prec_ [("k1", (pvar_ "x")), ("k2", pvarw_), ("k3", (pvar_ "x"))])
    (var_ "x") unit_ in

let datapat =
  bind_ (ucondef_ "Test")
    (match_ unit_ (pcon_ "Test" (pvar_ "x")) (var_ "x") unit_) in

let litpat =
  match_ unit_ (pint_ 1)
    (match_ unit_ (pchar_ 'c')
       (match_ unit_ (ptrue_)
            base
          unit_)
       unit_)
    unit_ in

let ut = utest_ base base base in

let seq = seq_ [base, data, const] in

let nev = never_ in

let matchand = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (pand_ (pint_ 1) (pvar_ "a")) (var_ "a") (never_)) in

let matchor = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pvar_ "a") (pvar_ "a")) (var_ "a") (never_)) in

-- NOTE(vipa, 2020-09-23): (var_ "a") should refer to the "a" from ulet_, not the pattern, that's intended, in case someone happens to notice and finds it odd
let matchnot = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (pnot_ (pvar_ "a")) (var_ "a") (never_)) in

let matchoredge = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pseqedge_ [pchar_ 'a'] "a" []) (pseqedge_ [pchar_ 'b'] "a" [])) (var_ "a") (never_)) in

let debug = false in

let debugPrint = lam i. lam t.
  let r = symbolize t in
  if debug then
    let _ = printLn (join ["--- ", int2string i, " BEFORE SYMBOLIZE ---"]) in
    let _ = printLn (expr2str t) in
    let _ = print "\n" in
    let _ = printLn "--- AFTER SYMBOLIZE ---" in
    let _ = printLn (expr2str r) in
    let _ = print "\n" in
    ()
  else ()
in

let _ =
  mapi debugPrint [
    base,
    rec,
    letin,
    lettypein,
    rlets,
    const,
    data,
    varpat,
    recpat,
    datapat,
    litpat,
    ut,
    seq,
    nev,
    matchand,
    matchor,
    matchnot,
    matchoredge
  ]
in

()
