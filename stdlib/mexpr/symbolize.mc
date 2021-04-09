-- Symbolization of the MExpr ast. Ignores already symbolized variables,
-- constructors, and type variables.
--
-- NOTE(dlunde,2020-09-25):
-- * Add support for unbound variables and constructors (similarly to eq.mc)?

include "common.mc"
include "map.mc"
include "name.mc"
include "string.mc"

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
  varEnv: Map String Name,
  conEnv: Map String Name,
  tyEnv: Map String Name
}

let symEnvEmpty =
  {varEnv = mapEmpty cmpString, conEnv = mapEmpty cmpString, tyEnv = mapEmpty cmpString}

-----------
-- TERMS --
-----------

lang Sym
  sem symbolizeType (env : SymEnv) =
  -- Intentionally left blank

  -- Symbolize with an environment
  sem symbolizeExpr (env : SymEnv) =

  -- Symbolize with builtin environment
  sem symbolize =
  | expr ->
    let env = {symEnvEmpty with varEnv = builtinNameMap} in
    symbolizeExpr env expr
end

lang VarSym = Sym + VarAst
  sem symbolizeExpr (env : SymEnv) =
  | TmVar t ->
    match env with {varEnv = varEnv} then
      if nameHasSym t.ident then TmVar t
      else
        let str = nameGetStr t.ident in
        match mapLookup str varEnv with Some ident then
          TmVar {{t with ident = ident}
                    with ty = symbolizeType env t.ty}
        else error (concat "Unknown variable in symbolizeExpr: " str)
    else never
end

lang AppSym = Sym + AppAst
  sem symbolizeExpr (env : SymEnv) =
  | TmApp t ->
    TmApp {{{t with lhs = symbolizeExpr env t.lhs}
               with rhs = symbolizeExpr env t.rhs}
               with ty = symbolizeType env t.ty}
end

lang LamSym = Sym + LamAst + VarSym + AppSym
  sem symbolizeExpr (env : SymEnv) =
  | TmLam t ->
    match env with {varEnv = varEnv} then
      let ty = symbolizeType env t.ty in
      let tyIdent = symbolizeType env t.tyIdent in
      if nameHasSym t.ident then
        TmLam {{{t with tyIdent = tyIdent}
                   with body = symbolizeExpr env t.body}
                   with ty = ty}
      else
        let ident = nameSetNewSym t.ident in
        let str = nameGetStr ident in
        let varEnv = mapInsert str ident varEnv in
        let env = {env with varEnv = varEnv} in
        TmLam {{{{t with ident = ident}
                    with tyIdent = tyIdent}
                    with body = symbolizeExpr env t.body}
                    with ty = ty}
    else never
end

lang RecordSym = Sym + RecordAst
  sem symbolizeExpr (env : SymEnv) =
  | TmRecord t ->
    TmRecord {{t with bindings = mapMap (symbolizeExpr env) t.bindings}
                 with ty = symbolizeType env t.ty}

  | TmRecordUpdate t ->
    TmRecordUpdate {{{t with rec = symbolizeExpr env t.rec}
                        with value = symbolizeExpr env t.value}
                        with ty = symbolizeType env t.ty}
end

lang LetSym = Sym + LetAst
  sem symbolizeType (env : SymEnv) =
  -- Intentinally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmLet t ->
    match env with {varEnv = varEnv} then
      let tyBody = symbolizeType env t.tyBody in
      let ty = symbolizeType env t.ty in
      let body = symbolizeExpr env t.body in
      if nameHasSym t.ident then
        TmLet {{{{t with tyBody = tyBody}
                    with body = body}
                    with inexpr = symbolizeExpr env t.inexpr}
                    with ty = ty}
      else
        let ident = nameSetNewSym t.ident in
        let str = nameGetStr ident in
        let varEnv = mapInsert str ident varEnv in
        let env = {env with varEnv = varEnv} in
        TmLet {{{{{t with ident = ident}
                     with tyBody = tyBody}
                     with body = body}
                     with inexpr = symbolizeExpr env t.inexpr}
                     with ty = ty}
    else never
end

lang TypeSym = Sym + TypeAst
  sem symbolizeType (env : SymEnv) =
  -- Intentinally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmType t ->
    match env with {tyEnv = tyEnv} then
      let tyIdent = symbolizeType env t.tyIdent in
      let ty = symbolizeType env t.ty in
      if nameHasSym t.ident then
        TmType {{{t with tyIdent = tyIdent}
                    with inexpr = symbolizeExpr env t.inexpr}
                    with ty = ty}
      else
        let ident = nameSetNewSym t.ident in
        let str = nameGetStr ident in
        let tyEnv = mapInsert str ident tyEnv in
        let env = {env with tyEnv = tyEnv} in
        TmType {{{{t with ident = ident}
                     with tyIdent = tyIdent}
                     with inexpr = symbolizeExpr env t.inexpr}
                     with ty = ty}
    else never
end

lang RecLetsSym = Sym + RecLetsAst
  sem symbolizeType (env : SymEnv) =
  -- Intentionally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmRecLets t ->
    match env with {varEnv = varEnv} then

    -- Generate fresh symbols for all identifiers
    let bindings =
      map (lam bind : RecLetBinding.
             if nameHasSym bind.ident then bind
             else {bind with ident = nameSetNewSym bind.ident})
        t.bindings in

    -- Add all identifiers to environment
    let varEnv =
      foldl
        (lam varEnv. lam bind : RecLetBinding.
           mapInsert (nameGetStr bind.ident) bind.ident varEnv)
        varEnv bindings in
    let env = {env with varEnv = varEnv} in

    -- Symbolize all bodies with the new environment
    let bindings =
      map (lam bind : RecLetBinding.
        {{{bind with body = symbolizeExpr env bind.body}
                with tyBody = symbolizeType env bind.tyBody}
                with ty = symbolizeType env bind.ty})
        bindings in

    TmRecLets {{t with bindings = bindings}
                  with inexpr = symbolizeExpr env t.inexpr}

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
  | TmConDef t ->
    match env with {conEnv = conEnv} then
      let tyIdent = symbolizeType env t.tyIdent in
      let ty = symbolizeType env t.ty in
      if nameHasSym t.ident then
        TmConDef {{{t with tyIdent = tyIdent}
                      with inexpr = symbolizeExpr env t.inexpr}
                      with ty = ty}
      else
        let str = nameGetStr t.ident in
        let ident = nameSetNewSym t.ident in
        let conEnv = mapInsert str ident conEnv in
        let env = {env with conEnv = conEnv} in
        TmConDef {{{{t with ident = ident}
                       with tyIdent = tyIdent}
                       with inexpr = symbolizeExpr env t.inexpr}
                       with ty = ty}
    else never

  | TmConApp t ->
    match env with {conEnv = conEnv} then
      let ty = symbolizeType env t.ty in
      if nameHasSym t.ident then
        TmConApp {{t with body = symbolizeExpr env t.body}
                     with ty = ty}
      else
        let str = nameGetStr t.ident in
        match mapLookup str conEnv with Some ident then
          TmConApp {{{t with ident = ident}
                        with body = symbolizeExpr env t.body}
                        with ty = ty}
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
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  -- Intentionally left blank

  sem symbolizeExpr (env : SymEnv) =
  | TmMatch t ->
    match symbolizePat env (mapEmpty cmpString) t.pat
    with (thnVarEnv, pat) then
      let thnPatEnv = {env with varEnv = mapUnion env.varEnv thnVarEnv} in
      TmMatch {{{{{t with target = symbolizeExpr env t.target}
                     with pat = pat}
                     with thn = symbolizeExpr thnPatEnv t.thn}
                     with els = symbolizeExpr env t.els}
                     with ty = symbolizeType env t.ty}
    else never
end

lang UtestSym = Sym + UtestAst
  sem symbolizeExpr (env : SymEnv) =
  | TmUtest t ->
    let tusing = optionMap (symbolizeExpr env) t.tusing in
    TmUtest {{{{{t with test = symbolizeExpr env t.test}
                   with expected = symbolizeExpr env t.expected}
                   with next = symbolizeExpr env t.next}
                   with tusing = tusing}
                   with ty = symbolizeType env t.ty}
end

lang SeqSym = Sym + SeqAst
  sem symbolizeExpr (env : SymEnv) =
  | TmSeq t ->
    TmSeq {{t with tms = map (symbolizeExpr env) t.tms}
              with ty = symbolizeType env t.ty}
end

lang NeverSym = Sym + NeverAst
  sem symbolizeExpr (env : SymEnv) =
  | TmNever t -> TmNever {t with ty = symbolizeType env t.ty}
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
  | TyBool _ & ty -> ty
end

lang IntTypeSym = IntTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyInt _ & ty -> ty
end

lang FloatTypeSym = FloatTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyFloat _ & ty -> ty
end

lang CharTypeSym = CharTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyChar _ & ty -> ty
end

lang FunTypeSym = FunTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyArrow t ->
    TyArrow {{t with from = symbolizeType env t.from}
                with to = symbolizeType env t.to}
end

lang SeqTypeSym = SeqTypeAst
  sem symbolizeType (env : SymEnv) =
  | TySeq t -> TySeq {t with ty = symbolizeType env t.ty}
end

lang RecordTypeSym = RecordTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyRecord t ->
    TyRecord {t with fields = mapMap (symbolizeType env) t.fields}
end

lang VariantTypeSym = VariantTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyVariant t & ty ->
    if eqi (mapLength t.constrs) 0 then ty
    else error "Symbolizing non-empty variant types not yet supported"
end

lang VarTypeSym = VarTypeAst + UnknownTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyVar t & ty ->
    match env with {tyEnv = tyEnv} then
      if nameHasSym t.ident then ty
      else
        let str = nameGetStr t.ident in
        match mapLookup str tyEnv with Some ident then
          TyVar {t with ident = ident}
        else
          -- NOTE(larshum, 2021-03-24): Unknown type variables are symbolized
          -- as TyUnknown for now.
          TyUnknown {info = t.info}
    else never
end

lang AppTypeSym = AppTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyApp t ->
    TyApp {{t with lhs = symbolizeType env t.lhs}
              with rhs = symbolizeType env t.rhs}
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
        let res = mapLookup str varEnv in
        match res with Some name then
          let name : Name = name in
          (varEnv, PName name)
        else match res with None () then
          let name = nameSetNewSym name in
          let varEnv = mapInsert str name varEnv in
          (varEnv, PName name)
        else never
    else match pname with PWildcard () then (varEnv, PWildcard ())
    else never

lang NamedPatSym = NamedPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatNamed p ->
    match _symbolize_patname patEnv p.ident with (patEnv, patname) then
      (patEnv, PatNamed {p with ident = patname})
    else never
end

lang SeqTotPatSym = SeqTotPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatSeqTot p ->
    let res = mapAccumL (symbolizePat env) patEnv p.pats in
    (res.0, PatSeqTot {p with pats = res.1})
end

lang SeqEdgePatSym = SeqEdgePat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatSeqEdge p ->
    let preRes = mapAccumL (symbolizePat env) patEnv p.prefix in
    let midRes = _symbolize_patname preRes.0 p.middle in
    let postRes = mapAccumL (symbolizePat env) midRes.0 p.postfix in
    (postRes.0, PatSeqEdge
      {{{p with prefix = preRes.1} with middle = midRes.1} with postfix = postRes.1})
end

lang RecordPatSym = RecordPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatRecord {bindings = bindings, info = info} ->
    match mapMapAccum
            (lam patEnv. lam. lam p. symbolizePat env patEnv p) patEnv bindings
    with (env,bindings) then
      (env, PatRecord {bindings = bindings, info = info})
    else never
end

lang DataPatSym = DataPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatCon {ident = ident, subpat = subpat, info = info} ->
    match env with {conEnv = conEnv} then
      let ident =
        if nameHasSym ident then ident
        else
          let str = nameGetStr ident in
          match mapLookup str conEnv with Some ident then ident
          else error (concat "Unknown constructor in symbolizeExpr: " str)
      in
      match symbolizePat env patEnv subpat with (patEnv, subpat) then
        (patEnv, PatCon {ident = ident, subpat = subpat, info = info})
      else never
    else never
end

lang IntPatSym = IntPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatInt i -> (patEnv, PatInt i)
end

lang CharPatSym = CharPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatChar c -> (patEnv, PatChar c)
end

lang BoolPatSym = BoolPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatBool b -> (patEnv, PatBool b)
end

lang AndPatSym = AndPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatAnd p ->
    let lRes : (SymEnv, Pat) = symbolizePat env patEnv p.lpat in
    let rRes : (SymEnv, Pat) = symbolizePat env lRes.0 p.rpat in
    (rRes.0, PatAnd {{p with lpat = lRes.1} with rpat = rRes.1})
end

lang OrPatSym = OrPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatOr p ->
    let lRes : (SymEnv, Pat) = symbolizePat env patEnv p.lpat in
    let rRes : (SymEnv, Pat) = symbolizePat env lRes.0 p.rpat in
    (rRes.0, PatOr {{p with lpat = lRes.1} with rpat = rRes.1})
end

lang NotPatSym = NotPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatNot p ->
    -- NOTE(vipa, 2020-09-23): new names in a not-pattern do not
    -- matter since they will never bind (it should probably be an
    -- error to bind a name inside a not-pattern, but we're not doing
    -- that kind of static checks yet.  Note that we still need to run
    -- symbolizeExpr though, constructors must refer to the right symbol.
    let res : (SymEnv, Pat) = symbolizePat env patEnv p.subpat in
    (patEnv, PatNot {p with subpat = res.1})
end

------------------------------
-- MEXPR SYMBOLIZE FRAGMENT --
------------------------------

lang MExprSym =

  -- Terms
  VarSym + AppSym + LamSym + RecordSym + LetSym + TypeSym + RecLetsSym +
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

let utu = utestu_ base base base (const_ (CEqi{})) in

let seq = seq_ [base, data, const, utu] in

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
    printLn (join ["--- ", int2string i, " BEFORE SYMBOLIZE ---"]);
    printLn (expr2str t);
    print "\n";
    printLn "--- AFTER SYMBOLIZE ---";
    printLn (expr2str r);
    print "\n";
    ()
  else ()
in

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
  ];


()
