-- Symbolization of the MExpr ast. Ignores already symbolized variables,
-- constructors, and type variables.
--
-- NOTE(dlunde,2020-09-25):
-- * Add support for unbound variables and constructors (similarly to eq.mc)?

include "common.mc"
include "map.mc"
include "name.mc"
include "string.mc"

include "ast.mc"
include "ast-builder.mc"
include "builtin.mc"
include "info.mc"
include "error.mc"
include "pprint.mc"

---------------------------
-- SYMBOLIZE ENVIRONMENT --
---------------------------
-- The environment differs from boot in that we use strings directly (we do
-- have SIDs available, however, if needed).

type SymEnv = {
  varEnv: Map String Name,
  conEnv: Map String Name,
  tyVarEnv: Map String (Name, Level),
  tyConEnv: Map String Name,
  currentLvl : Level,
  strictTypeVars: Bool,
  allowFree: Bool,
  ignoreExternals: Bool
}

let symEnvEmpty = {
  varEnv = mapEmpty cmpString,
  conEnv = mapEmpty cmpString,
  tyVarEnv = mapEmpty cmpString,

  -- Built-in type constructors
  tyConEnv = mapFromSeq cmpString (
    map (lam t: (String, [String]). (t.0, nameNoSym t.0)) builtinTypes
  ),

  currentLvl = 1,
  strictTypeVars = true,
  allowFree = false,
  ignoreExternals = false
}

-----------
-- TERMS --
-----------

lang Sym = Ast
  sem symbolizeType (env : SymEnv) =
  | t -> smap_Type_Type (symbolizeType env) t

  -- Symbolize with an environment
  sem symbolizeExpr (env : SymEnv) =
  | t ->
    let t = smap_Expr_Expr (symbolizeExpr env) t in
    withType (symbolizeType env (tyTm t)) t

  -- Same as symbolizeExpr, but also return an env with all names bound at the
  -- top-level
  sem symbolizeTopExpr (env : SymEnv) =
  | t ->
    let t = symbolizeExpr env t in
    addTopNames env t

  sem addTopNames (env : SymEnv) =
  | t -> env

  -- TODO(vipa, 2020-09-23): env is constant throughout symbolizePat,
  -- so it would be preferrable to pass it in some other way, a reader
  -- monad or something. patEnv on the other hand changes, it would be
  -- nice to pass via state monad or something.  env is the
  -- environment from the outside, plus the names added thus far in
  -- the pattern patEnv is only the newly added names
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | t -> smapAccumL_Pat_Pat (symbolizePat env) patEnv t

  -- Symbolize with builtin environment
  sem symbolize =
  | expr ->
    let env = symEnvEmpty in
    symbolizeExpr env expr

  sem symbolizeTop =
  | expr ->
    let env = symEnvEmpty in
    symbolizeTopExpr env expr

  -- Symbolize with builtin environment and ignore errors
  sem symbolizeAllowFree =
  | expr ->
    let env = { symEnvEmpty with allowFree = true } in
    symbolizeExpr env expr

end

lang VarSym = Sym + VarAst
  sem symbolizeExpr (env : SymEnv) =
  | TmVar t ->
    match env with {varEnv = varEnv} then
      if nameHasSym t.ident then TmVar t
      else
        let str = nameGetStr t.ident in
        let ident =
          match mapLookup str varEnv with Some ident then ident
          else if env.allowFree then t.ident
          else errorSingle [t.info] (concat "Unknown variable in symbolizeExpr: " str)
        in
        TmVar {{t with ident = ident}
                  with ty = symbolizeType env t.ty}
    else never
end

lang LamSym = Sym + LamAst + VarSym
  sem symbolizeExpr (env : SymEnv) =
  | TmLam t ->
    match env with {varEnv = varEnv} then
      let ty = symbolizeType env t.ty in
      let tyAnnot = symbolizeType env t.tyAnnot in
      if nameHasSym t.ident then
        TmLam {{{t with tyAnnot = tyAnnot}
                   with body = symbolizeExpr env t.body}
                   with ty = ty}
      else
        let ident = nameSetNewSym t.ident in
        let str = nameGetStr ident in
        let varEnv = mapInsert str ident varEnv in
        let env = {env with varEnv = varEnv} in
        TmLam {{{{t with ident = ident}
                    with tyAnnot = tyAnnot}
                    with body = symbolizeExpr env t.body}
                    with ty = ty}
    else never
end

lang LetSym = Sym + LetAst + AllTypeAst
  sem symbolizeExpr (env : SymEnv) =
  | TmLet t ->
    match env with {varEnv = varEnv} then
      let tyAnnot = symbolizeType env t.tyAnnot in
      let ty = symbolizeType env t.ty in
      let body =
        match stripTyAll tyAnnot with (vars, _) in
        let tyVarEnv =
          foldr (lam v: (Name, VarSort).
              mapInsert (nameGetStr v.0) (v.0, env.currentLvl))
            env.tyVarEnv vars in
        symbolizeExpr {{env with tyVarEnv = tyVarEnv}
                            with currentLvl = addi 1 env.currentLvl} t.body
      in
      if nameHasSym t.ident then
        TmLet {{{{t with tyAnnot = tyAnnot}
                    with body = body}
                    with inexpr = symbolizeExpr env t.inexpr}
                    with ty = ty}
      else
        let ident = nameSetNewSym t.ident in
        let str = nameGetStr ident in
        let varEnv = mapInsert str ident varEnv in
        let env = {env with varEnv = varEnv} in
        TmLet {{{{{t with ident = ident}
                     with tyAnnot = tyAnnot}
                     with body = body}
                     with inexpr = symbolizeExpr env t.inexpr}
                     with ty = ty}
    else never

  sem addTopNames (env : SymEnv) =
  | TmLet t ->
    let str = nameGetStr t.ident in
    let varEnv = mapInsert str t.ident env.varEnv in
    addTopNames {env with varEnv = varEnv} t.inexpr
end

lang ExtSym = Sym + ExtAst
  sem symbolizeExpr (env : SymEnv) =
  | TmExt t ->
    match env with {varEnv = varEnv} then
      let tyIdent = symbolizeType env t.tyIdent in
      if or env.ignoreExternals (nameHasSym t.ident) then
        TmExt {{t with inexpr = symbolizeExpr env t.inexpr}
                  with tyIdent = tyIdent}
      else
        let ident = nameSetNewSym t.ident in
        let str = nameGetStr ident in
        let varEnv = mapInsert str ident varEnv in
        let env = {env with varEnv = varEnv} in
        TmExt {{{t with ident = ident}
                   with inexpr = symbolizeExpr env t.inexpr}
                   with tyIdent = tyIdent}
    else never

  sem addTopNames (env : SymEnv) =
  | TmExt t ->
    let str = nameGetStr t.ident in
    let varEnv = mapInsert str t.ident env.varEnv in
    addTopNames {env with varEnv = varEnv} t.inexpr
end

lang TypeSym = Sym + TypeAst
  sem symbolizeExpr (env : SymEnv) =
  | TmType t ->
    match env with {tyConEnv = tyConEnv, tyVarEnv = tyVarEnv} in
    let ty = symbolizeType env t.ty in
    if nameHasSym t.ident then
      TmType {{{t with tyIdent = symbolizeType env t.tyIdent}
                  with inexpr = symbolizeExpr env t.inexpr}
                  with ty = ty}
    else
      let params = map nameSetNewSym t.params in
      let paramStrs = map nameGetStr params in
      let tyVarEnv =
        foldl2 (lam e. lam s. lam i. mapInsert s (i, env.currentLvl) e) tyVarEnv paramStrs params
      in
      let paramEnv = {env with tyVarEnv = tyVarEnv} in
      let tyIdent = symbolizeType paramEnv t.tyIdent in
      let ident = nameSetNewSym t.ident in
      let str = nameGetStr ident in
      let tyConEnv = mapInsert str ident tyConEnv in
      let env = {env with tyConEnv = tyConEnv} in
      TmType {{{{{t with ident = ident}
                    with params = params}
                    with tyIdent = tyIdent}
                    with inexpr = symbolizeExpr env t.inexpr}
                    with ty = ty}

  sem addTopNames (env : SymEnv) =
  | TmType t ->
    let str = nameGetStr t.ident in
    let tyConEnv = mapInsert str t.ident env.tyConEnv in
    addTopNames {env with tyConEnv = tyConEnv} t.inexpr
end

lang RecLetsSym = Sym + RecLetsAst + AllTypeAst
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
        let tyAnnot = symbolizeType env bind.tyAnnot in
        match stripTyAll tyAnnot with (vars, _) in
        let tyVarEnv =
          foldr (lam v: (Name, VarSort).
              mapInsert (nameGetStr v.0) (v.0, env.currentLvl))
            env.tyVarEnv vars in
        {{bind with body = symbolizeExpr
                             {{env with tyVarEnv = tyVarEnv}
                                   with currentLvl = addi 1 env.currentLvl} bind.body}
               with tyAnnot = tyAnnot})
        bindings in

    TmRecLets {{t with bindings = bindings}
                  with inexpr = symbolizeExpr env t.inexpr}

    else never

  sem addTopNames (env : SymEnv) =
  | TmRecLets t ->
    let varEnv =
      foldl
        (lam varEnv. lam bind : RecLetBinding.
           mapInsert (nameGetStr bind.ident) bind.ident varEnv)
        env.varEnv t.bindings
    in
    addTopNames {env with varEnv = varEnv} t.inexpr
end

lang DataSym = Sym + DataAst
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
        let ident =
          match mapLookup str conEnv with Some ident then ident
          else if env.allowFree then t.ident
          else errorSingle [t.info] (concat "Unknown constructor in symbolizeExpr: " str)
        in
        TmConApp {{{t with ident = ident}
                      with body = symbolizeExpr env t.body}
                      with ty = ty}
    else never

  sem addTopNames (env : SymEnv) =
  | TmConDef t ->
    let str = nameGetStr t.ident in
    let conEnv = mapInsert str t.ident env.conEnv in
    addTopNames {env with conEnv = conEnv} t.inexpr
end

lang MatchSym = Sym + MatchAst
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

-----------
-- TYPES --
-----------

lang VariantTypeSym = VariantTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyVariant t & ty ->
    if eqi (mapLength t.constrs) 0 then ty
    else errorSingle [t.info] "Symbolizing non-empty variant types not yet supported"
end

lang ConTypeSym = ConTypeAst + UnknownTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyCon t & ty ->
    match env with {tyConEnv = tyConEnv} then
      if nameHasSym t.ident then ty
      else
        let str = nameGetStr t.ident in
        match mapLookup str tyConEnv with Some ident then
          TyCon {t with ident = ident}
        else if env.strictTypeVars then
          if env.allowFree then TyCon t
          else errorSingle [t.info] (concat "Unknown type constructor in symbolizeExpr: " str)
        else
          TyUnknown {info = t.info}
    else never
end

lang VarTypeSym = VarTypeAst + UnknownTypeAst
  sem symbolizeType (env : SymEnv) =
  | TyVar t & ty ->
    if nameHasSym t.ident then ty
    else
      let str = nameGetStr t.ident in
      match mapLookup str env.tyVarEnv with Some (ident, lvl) then
        TyVar {{t with ident = ident}
                  with level = lvl}
      else if env.strictTypeVars then
        if env.allowFree then TyVar t
        else errorSingle [t.info] (concat "Unknown type variable in symbolizeExpr: " str)
      else
        TyUnknown {info = t.info}
end

lang AllTypeSym = AllTypeAst + VarSortAst
  sem symbolizeType (env : SymEnv) =
  | TyAll t & ty ->
      let sort = smap_VarSort_Type (symbolizeType env) t.sort in
      if nameHasSym t.ident then
        TyAll {{t with ty = symbolizeType env t.ty}
                  with sort = sort}
      else
        let str = nameGetStr t.ident in
        let ident = nameSetNewSym t.ident in
        let env = {env with tyVarEnv = mapInsert str (ident, env.currentLvl) env.tyVarEnv} in
        TyAll {{{t with ident = ident}
                   with ty = symbolizeType env t.ty}
                   with sort = sort}
end

--------------
-- PATTERNS --
--------------

let _symbolize_patname: Map String Name -> PatName -> (Map String Name, PatName) =
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

lang SeqEdgePatSym = SeqEdgePat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatSeqEdge p ->
    let preRes = mapAccumL (symbolizePat env) patEnv p.prefix in
    let midRes = _symbolize_patname preRes.0 p.middle in
    let postRes = mapAccumL (symbolizePat env) midRes.0 p.postfix in
    (postRes.0, PatSeqEdge
      {{{p with prefix = preRes.1} with middle = midRes.1} with postfix = postRes.1})
end

lang DataPatSym = DataPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatCon r ->
    match env with {conEnv = conEnv} then
      let ident =
        if nameHasSym r.ident then r.ident
        else
          let str = nameGetStr r.ident in
          match mapLookup str conEnv with Some ident then ident
          else errorSingle [r.info] (concat "Unknown constructor in symbolizeExpr: " str)
      in
      match symbolizePat env patEnv r.subpat with (patEnv, subpat) then
        (patEnv, PatCon {{r with ident = ident} with subpat = subpat})
      else never
    else never
end

lang NotPatSym = NotPat
  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | PatNot p ->
    -- NOTE(vipa, 2020-09-23): new names in a not-pattern do not
    -- matter since they will never bind (it should probably be an
    -- error to bind a name inside a not-pattern, but we're not doing
    -- that kind of static checks yet.  Note that we still need to run
    -- symbolizeExpr though, constructors must refer to the right symbol.
    let res : (Map String Name, Pat) = symbolizePat env patEnv p.subpat in
    (patEnv, PatNot {p with subpat = res.1})
end

------------------------------
-- MEXPR SYMBOLIZE FRAGMENT --
------------------------------

lang MExprSym =

  -- Default implementations (Terms)
  RecordAst + ConstAst + UtestAst + SeqAst + NeverAst +

  -- Default implementations (Types)
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  FunTypeAst + SeqTypeAst + TensorTypeAst + RecordTypeAst + AppTypeAst +

  -- Default implementations (Patterns)
  SeqTotPat + RecordPat + IntPat + CharPat + BoolPat + AndPat + OrPat +

  -- Non-default implementations (Terms)
  VarSym + LamSym + LetSym + ExtSym + TypeSym + RecLetsSym + DataSym +
  MatchSym +

  -- Non-default implementations (Types)
  VariantTypeSym + ConTypeSym + VarTypeSym + AllTypeSym +

  -- Non-default implementations (Patterns)
  NamedPatSym + SeqEdgePatSym + DataPatSym + NotPatSym
end

-----------
-- TESTS --
-----------
-- It is difficult to directly do unit testing for the above due to the nature
-- of symbols, so we are just evaluating the below for errors. Unit
-- testing in eval.mc also implicitly covers symbolizeExpr.

lang TestLang = MExprSym + MExprPrettyPrint
end

mexpr

use TestLang in

let base = (ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y")))) in

let rec = urecord_ [("k1", base), ("k2", (int_ 1)), ("k3", (int_ 2))] in

let letin = bind_ (ulet_ "x" rec) (app_ (var_ "x") base) in

let lettypein = bindall_ [
  type_ "Type" tystr_,
  type_ "Type" (tycon_ "Type"),
  lam_ "Type" (tycon_ "Type") (var_ "Type")
] in

let rlets =
  bind_ (ureclets_ [("x", (var_ "y")), ("y", (var_ "x"))])
    (app_ (var_ "x") (var_ "y")) in

let const = int_ 1 in

let data = bind_ (ucondef_ "Test") (conapp_ "Test" base) in

let varpat = match_ uunit_ (pvar_ "x") (var_ "x") base in

let recpat =
  match_ base
    (prec_ [("k1", (pvar_ "x")), ("k2", pvarw_), ("k3", (pvar_ "x"))])
    (var_ "x") uunit_ in

let datapat =
  bind_ (ucondef_ "Test")
    (match_ uunit_ (pcon_ "Test" (pvar_ "x")) (var_ "x") uunit_) in

let litpat =
  match_ uunit_ (pint_ 1)
    (match_ uunit_ (pchar_ 'c')
       (match_ uunit_ (ptrue_)
            base
          uunit_)
       uunit_)
    uunit_ in

let ut = utest_ base base base in

let utu = utestu_ base base base (uconst_ (CEqi{})) in

let seq = seq_ [base, data, const, utu] in

let nev = never_ in

let matchand = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (pand_ (pint_ 1) (pvar_ "a")) (var_ "a") (never_)) in

let matchor = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pvar_ "a") (pvar_ "a")) (var_ "a") (never_)) in

-- NOTE(vipa, 2020-09-23): (var_ "a") should refer to the "a" from ulet_, not the pattern, that's intended, in case someone happens to notice and finds it odd
let matchnot = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (pnot_ (pvar_ "a")) (var_ "a") (never_)) in

let matchoredge = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pseqedge_ [pchar_ 'a'] "a" []) (pseqedge_ [pchar_ 'b'] "a" [])) (var_ "a") (never_)) in

let lettyvar = let_ "f" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")))
                        (lam_ "x" (tyvar_ "a") (var_ "x")) in

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
    matchoredge,
    lettyvar
  ];


()
