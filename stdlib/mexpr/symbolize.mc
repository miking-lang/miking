-- Symbolization of the MExpr ast. Ignores already symbolized variables,
-- constructors, and type variables.
--
-- NOTE(aathn, 2023-05-10): Add support for symbolizing and returning the
-- free variables of an expression (similarly to eq.mc)?

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
include "type.mc"

---------------------------
-- SYMBOLIZE ENVIRONMENT --
---------------------------
-- The environment differs from boot in that we use strings directly (we do
-- have SIDs available, however, if needed).

-- Poor man's row polymorphism: ext represents an arbitrary extension of the environment
type SymEnvBase ext = {
  varEnv: Map String Name,
  conEnv: Map String Name,
  tyVarEnv: Map String Name,
  tyConEnv: Map String Name,
  allowFree: Bool,
  ignoreExternals: Bool,
  ext: ext
}

type SymEnv = SymEnvBase ()

let mkSymEnvEmpty = lam ext. {
  varEnv = mapEmpty cmpString,
  conEnv = mapEmpty cmpString,
  tyVarEnv = mapEmpty cmpString,

  -- Built-in type constructors
  tyConEnv =
  mapFromSeq cmpString (map (lam t. (t.0, nameNoSym t.0)) builtinTypes),

  allowFree = false,
  ignoreExternals = false,
  ext = ext
}

let symEnvEmpty = mkSymEnvEmpty ()

type LookupParams = {kind : String, info : [Info], allowFree : Bool}

let _handleUnbound : LookupParams -> Name -> () -> Name
  = lam lkup. lam ident. lam.
    if lkup.allowFree then ident
    else
      errorSingle lkup.info
        (join ["Unknown ", lkup.kind, " in symbolizeExpr: ", nameGetStr ident])

let _lookupName : LookupParams -> Name -> Map String Name -> Name
  = lam lkup. lam ident. lam env.
    optionGetOrElse (_handleUnbound lkup ident)
      (mapLookup (nameGetStr ident) env)

let _getName : LookupParams -> Name -> Map String Name -> Name
  = lam lkup. lam ident. lam env.
    if nameHasSym ident then ident
    else _lookupName lkup ident env

let _setName : Map String Name -> Name -> (Map String Name, Name)
  = lam env. lam ident.
    if nameHasSym ident then (env, ident)
    else
      let ident = nameSetNewSym ident in
      (mapInsert (nameGetStr ident) ident env, ident)

-----------
-- TERMS --
-----------

lang Sym = Ast
  -- Symbolize with an environment
  sem symbolizeExpr : SymEnv -> Expr -> Expr
  sem symbolizeExpr (env : SymEnv) =
  | t -> symbolizeExprBase symbolizeExpr env t

  -- Extensible symbolization function: the argument function should be used in
  -- place of all recursive calls.
  sem symbolizeExprBase
    : all ext. (SymEnvBase ext -> Expr -> Expr) -> SymEnvBase ext -> Expr -> Expr
  sem symbolizeExprBase symbolize env =
  | t -> smap_Expr_Expr (symbolize env) t

  sem symbolizeType : all ext. SymEnvBase ext -> Type -> Type
  sem symbolizeType env =
  | t -> smap_Type_Type (symbolizeType env) t

  -- TODO(vipa, 2020-09-23): env is constant throughout symbolizePat,
  -- so it would be preferrable to pass it in some other way, a reader
  -- monad or something. patEnv on the other hand changes, it would be
  -- nice to pass via state monad or something.  env is the
  -- environment from the outside, plus the names added thus far in
  -- the pattern patEnv is only the newly added names
  sem symbolizePat
    : all ext. SymEnvBase ext -> Map String Name -> Pat -> (Map String Name, Pat)
  sem symbolizePat env patEnv =
  | t -> smapAccumL_Pat_Pat (symbolizePat env) patEnv t

  -- Symbolize with builtin environment
  sem symbolize =
  | expr ->
    let env = symEnvEmpty in
    symbolizeExpr env expr

  -- Symbolize with builtin environment and ignore errors
  sem symbolizeAllowFree =
  | expr ->
    let env = { symEnvEmpty with allowFree = true } in
    symbolizeExpr env expr
end

lang VarSym = Sym + VarAst
  sem symbolizeExprBase symbolize env =
  | TmVar t ->
    let ident =
      _getName {kind = "variable",
                info = [t.info],
                allowFree = env.allowFree}
        t.ident env.varEnv
    in
    TmVar {t with ident = ident}
end

lang LamSym = Sym + LamAst + VarSym
  sem symbolizeExprBase symbolize env =
  | TmLam t ->
    match _setName env.varEnv t.ident with (varEnv, ident) in
    TmLam {t with ident = ident,
                  tyAnnot = symbolizeType env t.tyAnnot,
                  body = symbolize {env with varEnv = varEnv} t.body}
end

lang LetSym = Sym + LetAst + AllTypeAst
  sem symbolizeExprBase symbolize env =
  | TmLet t ->
    match symbolizeTyAnnot env t.tyAnnot with (tyVarEnv, tyAnnot) in
    match _setName env.varEnv t.ident with (varEnv, ident) in
    TmLet {t with ident = ident,
                  tyAnnot = tyAnnot,
                  body = symbolize {env with tyVarEnv = tyVarEnv} t.body,
                  inexpr = symbolize {env with varEnv = varEnv} t.inexpr}

  sem symbolizeTyAnnot : all ext. SymEnvBase ext -> Type -> (Map String Name, Type)
  sem symbolizeTyAnnot env =
  | tyAnnot ->
    let setNameFirst = lam env. lam vs.
      match _setName env vs.0 with (env, v) in
      (env, (v, vs.1))
    in
    match stripTyAll tyAnnot with (vars, stripped) in
    match mapAccumL setNameFirst env.tyVarEnv vars with (tyVarEnv, vars) in
    (tyVarEnv,
     foldr (lam vs. lam ty. TyAll {info = infoTy tyAnnot,
                                   ident = vs.0, sort = vs.1, ty = ty})
       (symbolizeType {env with tyVarEnv = tyVarEnv} stripped) vars)
end

lang RecLetsSym = Sym + RecLetsAst + LetSym
  sem symbolizeExprBase symbolize env =
  | TmRecLets t ->
    -- Generate fresh symbols for all identifiers and add to the environment
    let setNameIdent = lam env. lam b.
      match _setName env b.ident with (env, ident) in
      (env, {b with ident = ident})
    in
    match mapAccumL setNameIdent env.varEnv t.bindings with (varEnv, bindings) in
    let newEnv = {env with varEnv = varEnv} in

    -- Symbolize all bodies with the new environment
    let bindings =
      map (lam b. match symbolizeTyAnnot env b.tyAnnot with (tyVarEnv, tyAnnot) in
                  {b with body = symbolize {newEnv with tyVarEnv = tyVarEnv} b.body,
                          tyAnnot = tyAnnot})
        bindings in

    TmRecLets {t with bindings = bindings,
                      inexpr = symbolize newEnv t.inexpr}
end

lang ExtSym = Sym + ExtAst
  sem symbolizeExprBase symbolize env =
  | TmExt t ->
    let setName = if env.ignoreExternals then lam x. lam y. (x, y) else _setName in
    match setName env.varEnv t.ident with (varEnv, ident) in
    TmExt {t with ident = ident,
                  inexpr = symbolize {env with varEnv = varEnv} t.inexpr,
                  tyIdent = symbolizeType env t.tyIdent}
end

lang TypeSym = Sym + TypeAst
  sem symbolizeExprBase symbolize env =
  | TmType t ->
    match _setName env.tyConEnv t.ident with (tyConEnv, ident) in
    match mapAccumL _setName env.tyVarEnv t.params with (tyVarEnv, params) in
    TmType {t with ident = ident,
                   params = params,
                   tyIdent = symbolizeType {env with tyVarEnv = tyVarEnv} t.tyIdent,
                   inexpr = symbolize {env with tyConEnv = tyConEnv} t.inexpr}
end

lang DataSym = Sym + DataAst
  sem symbolizeExprBase symbolize env =
  | TmConDef t ->
    match _setName env.conEnv t.ident with (conEnv, ident) in
    TmConDef {t with ident = ident,
                     tyIdent = symbolizeType env t.tyIdent,
                     inexpr = symbolize {env with conEnv = conEnv} t.inexpr}
  | TmConApp t ->
    let ident =
      _getName {kind = "constructor",
                info = [t.info],
                allowFree = env.allowFree}
        t.ident env.conEnv
    in
    TmConApp {t with ident = ident,
                     body = symbolize env t.body}
end

lang MatchSym = Sym + MatchAst
  sem symbolizeExprBase symbolize env =
  | TmMatch t ->
    match symbolizePat env (mapEmpty cmpString) t.pat with (thnVarEnv, pat) in
    let thnPatEnv = {env with varEnv = mapUnion env.varEnv thnVarEnv} in
    TmMatch {t with target = symbolize env t.target,
                    pat = pat,
                    thn = symbolize thnPatEnv t.thn,
                    els = symbolize env t.els}
end

-----------
-- TYPES --
-----------

lang VariantTypeSym = Sym + VariantTypeAst
  sem symbolizeType env =
  | TyVariant t & ty ->
    if eqi (mapLength t.constrs) 0 then ty
    else errorSingle [t.info] "Symbolizing non-empty variant types not yet supported"
end

lang ConTypeSym = Sym + ConTypeAst
  sem symbolizeType env =
  | TyCon t ->
    let ident =
      _getName {kind = "type constructor",
                info = [t.info],
                allowFree = env.allowFree}
        t.ident env.tyConEnv
    in
    TyCon {t with ident = ident}
end

lang VarTypeSym = VarTypeAst + UnknownTypeAst
  sem symbolizeType env =
  | TyVar t ->
    let ident =
      _getName {kind = "type variable",
                info = [t.info],
                allowFree = env.allowFree}
        t.ident env.tyVarEnv
    in
    TyVar {t with ident = ident}
end

lang AllTypeSym = AllTypeAst + VarSortAst
  sem symbolizeType env =
  | TyAll t ->
    let sort = smap_VarSort_Type (symbolizeType env) t.sort in
    match _setName env.tyVarEnv t.ident with (tyVarEnv, ident) in
    TyAll {t with ident = ident,
                  ty = symbolizeType {env with tyVarEnv = tyVarEnv} t.ty,
                  sort = sort}
end

--------------
-- PATTERNS --
--------------

let _symbolizePatName: Map String Name -> PatName -> (Map String Name, PatName) =
  lam patEnv. lam pname.
    match pname with PName name then
      if nameHasSym name then (patEnv, PName name)
      else
        match mapLookup (nameGetStr name) patEnv
          with Some name then (patEnv, PName name)
        else
          let name = nameSetNewSym name in
          (mapInsert (nameGetStr name) name patEnv, PName name)
    else (patEnv, pname)

lang NamedPatSym = NamedPat
  sem symbolizePat env patEnv =
  | PatNamed p ->
    match _symbolizePatName patEnv p.ident with (patEnv, patname) in
    (patEnv, PatNamed {p with ident = patname})
end

lang SeqEdgePatSym = SeqEdgePat
  sem symbolizePat env patEnv =
  | PatSeqEdge p ->
    match mapAccumL (symbolizePat env) patEnv p.prefix with (patEnv, prefix) in
    match _symbolizePatName patEnv p.middle with (patEnv, middle) in
    match mapAccumL (symbolizePat env) patEnv p.postfix with (patEnv, postfix) in
    (patEnv, PatSeqEdge {p with prefix = prefix,
                                middle = middle,
                                postfix = postfix})
end

lang DataPatSym = DataPat
  sem symbolizePat env patEnv =
  | PatCon r ->
    let ident =
      _getName {kind = "constructor",
                info = [r.info],
                allowFree = env.allowFree}
        r.ident env.conEnv
    in
    match symbolizePat env patEnv r.subpat with (patEnv, subpat) in
    (patEnv, PatCon {r with ident = ident,
                            subpat = subpat})
end

lang NotPatSym = NotPat
  sem symbolizePat env patEnv =
  | PatNot p ->
    -- NOTE(vipa, 2020-09-23): new names in a not-pattern do not
    -- matter since they will never bind (it should probably be an
    -- error to bind a name inside a not-pattern, but we're not doing
    -- that kind of static checks yet.  Note that we still need to run
    -- symbolizePat though, constructors must refer to the right symbol.
    match symbolizePat env patEnv p.subpat with (_, subpat) in
    (patEnv, PatNot {p with subpat = subpat})
end

------------------------------
-- MEXPR SYMBOLIZE FRAGMENT --
------------------------------

lang MExprSym =

  -- Default implementations (Terms)
  RecordAst + ConstAst + UtestAst + SeqAst + NeverAst + AppAst +

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

let _and = lam cond. lam f. lam. if cond () then f () else false
let _andFold = lam f. lam acc. lam e. _and acc (f e)

-- To test that the symbolization works as expected, we define functions that
-- verify all names in the AST have been symbolized.
lang TestLang = MExprSym + MExprPrettyPrint
  sem isFullySymbolized : Expr -> Bool
  sem isFullySymbolized =
  | ast -> isFullySymbolizedExpr ast ()

  sem isFullySymbolizedExpr : Expr -> () -> Bool
  sem isFullySymbolizedExpr =
  | TmVar t -> lam. nameHasSym t.ident
  | TmLam t ->
    _and (lam. nameHasSym t.ident)
      (_and
         (isFullySymbolizedType t.tyAnnot)
         (isFullySymbolizedExpr t.body))
  | TmLet t ->
    _and (lam. nameHasSym t.ident)
      (_and (isFullySymbolizedType t.tyAnnot)
         (_and
            (isFullySymbolizedExpr t.body)
            (isFullySymbolizedExpr t.inexpr)))
  | TmRecLets t ->
    let isFullySymbolizedBinding = lam b.
      _and (lam. nameHasSym b.ident)
        (_and
           (isFullySymbolizedType b.tyAnnot)
           (isFullySymbolizedExpr b.body))
    in
    _and
      (foldl (_andFold isFullySymbolizedBinding) (lam. true) t.bindings)
      (isFullySymbolizedExpr t.inexpr)
  | TmType t ->
    _and (lam. forAll nameHasSym t.params)
      (_and
         (isFullySymbolizedType t.tyIdent)
         (isFullySymbolizedExpr t.inexpr))
  | TmConDef t ->
    _and (lam. nameHasSym t.ident)
      (_and
         (isFullySymbolizedType t.tyIdent)
         (isFullySymbolizedExpr t.inexpr))
  | TmConApp t ->
    _and (lam. nameHasSym t.ident) (isFullySymbolizedExpr t.body)
  | TmExt t ->
    _and (lam. nameHasSym t.ident)
      (_and
         (isFullySymbolizedType t.tyIdent)
         (isFullySymbolizedExpr t.inexpr))
  | t ->
    _and (sfold_Expr_Expr (_andFold isFullySymbolizedExpr) (lam. true) t)
      (_and
         (sfold_Expr_Type (_andFold isFullySymbolizedType) (lam. true) t)
         (sfold_Expr_Pat (_andFold isFullySymbolizedPat) (lam. true) t))

  sem isFullySymbolizedPat : Pat -> () -> Bool
  sem isFullySymbolizedPat =
  | PatNamed {ident = PName id} -> lam. nameHasSym id
  | PatCon t ->
    _and (lam. nameHasSym t.ident) (isFullySymbolizedPat t.subpat)
  | p ->
    _and
      (sfold_Pat_Pat (_andFold isFullySymbolizedPat) (lam. true) p)
      (sfold_Pat_Type (_andFold isFullySymbolizedType) (lam. true) p)

  sem isFullySymbolizedType : Type -> () -> Bool
  sem isFullySymbolizedType =
  | TyCon {ident = ident} | TyVar {ident = ident} -> lam. nameHasSym ident
  | TyAll t ->
    _and (lam. nameHasSym t.ident) (isFullySymbolizedType t.ty)
  | ty ->
    sfold_Type_Type (_andFold isFullySymbolizedType) (lam. true) ty
end

mexpr

use TestLang in

let x = nameSym "x" in
utest isFullySymbolized (ulam_ "x" (var_ "x")) with false in
utest isFullySymbolized (nulam_ x (var_ "x")) with false in
utest isFullySymbolized (nulam_ x (nvar_ x)) with true in

let testSymbolize = lam ast. lam testEqStr.
  let symbolizeCalls =
    [ symbolize
    , symbolizeExpr {symEnvEmpty with allowFree = true}] in
  foldl
    (lam acc. lam symb.
      if acc then
        let symAst = symb ast in
        isFullySymbolized symAst
      else false)
    true symbolizeCalls
in

let base = (ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y")))) in
utest testSymbolize base false with true in

let rec = urecord_ [("k1", base), ("k2", (int_ 1)), ("k3", (int_ 2))] in
utest testSymbolize rec false with true in

let letin = bind_ (ulet_ "x" rec) (app_ (var_ "x") base) in
utest testSymbolize letin false with true in

let lettypein = bindall_ [
  type_ "Type" [] tystr_,
  type_ "Type" [] (tycon_ "Type"),
  lam_ "Type" (tycon_ "Type") (var_ "Type")
] in
utest testSymbolize lettypein false with true in

let rlets =
  bind_ (ureclets_ [("x", (var_ "y")), ("y", (var_ "x"))])
    (app_ (var_ "x") (var_ "y")) in
utest testSymbolize rlets false with true in

let const = int_ 1 in
utest testSymbolize const false with true in

let data = bind_ (ucondef_ "Test") (conapp_ "Test" base) in
utest testSymbolize data false with true in

let varpat = match_ uunit_ (pvar_ "x") (var_ "x") base in
utest testSymbolize varpat false with true in

let recpat =
  match_ base
    (prec_ [("k1", (pvar_ "x")), ("k2", pvarw_), ("k3", (pvar_ "x"))])
    (var_ "x") uunit_ in
utest testSymbolize recpat false with true in

let datapat =
  bind_ (ucondef_ "Test")
    (match_ uunit_ (pcon_ "Test" (pvar_ "x")) (var_ "x") uunit_) in
utest testSymbolize datapat false with true in

let litpat =
  match_ uunit_ (pint_ 1)
    (match_ uunit_ (pchar_ 'c')
       (match_ uunit_ (ptrue_)
            base
          uunit_)
       uunit_)
    uunit_ in
utest testSymbolize litpat false with true in

let ut = utest_ base base base in
utest testSymbolize ut false with true in

let utu = utestu_ base base base (uconst_ (CEqi{})) in
utest testSymbolize utu false with true in

let seq = seq_ [base, data, const, utu] in
utest testSymbolize seq false with true in

let nev = never_ in
utest testSymbolize nev false with true in

let matchand = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (pand_ (pint_ 1) (pvar_ "a")) (var_ "a") (never_)) in
utest testSymbolize matchand false with true in

let matchor = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pvar_ "a") (pvar_ "a")) (var_ "a") (never_)) in
utest testSymbolize matchor false with true in

-- NOTE(vipa, 2020-09-23): (var_ "a") should refer to the "a" from ulet_, not the pattern, that's intended, in case someone happens to notice and finds it odd
let matchnot = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (pnot_ (pvar_ "a")) (var_ "a") (never_)) in
utest testSymbolize matchnot false with true in

let matchoredge = bind_ (ulet_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pseqedge_ [pchar_ 'a'] "a" []) (pseqedge_ [pchar_ 'b'] "a" [])) (var_ "a") (never_)) in
utest testSymbolize matchoredge false with true in

let lettyvar = let_ "f" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")))
                        (lam_ "x" (tyvar_ "a") (var_ "x")) in
utest testSymbolize lettyvar false with true in

-- NOTE(larshum, 2023-01-20): This test checks that the type parameters of a
-- type application are not erased when the constructor is a free variable.
let tyconApps = bindall_ [
  let_ "f"
    (tyall_ "a" (tyarrow_ (tyapp_ (tycon_ "Con") (tyvar_ "a")) (tyvar_ "a")))
    (ulam_ "x" never_)
] in
utest expr2str (symbolizeAllowFree tyconApps) with expr2str tyconApps using eqString in

()
