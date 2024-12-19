include "mexpr/symbolize.mc"

include "mlang/symbolize.mc"

include "ast.mc"
include "ast-builder.mc"

include "name.mc"
include "option.mc"

lang ExtRecordSym = Sym + ExtRecordAst
  sem symbolizeExpr env =
  | TmRecType t ->
    match setSymbol env.currentEnv.tyConEnv t.ident with (tyConEnv, ident) in
    let env = symbolizeUpdateTyConEnv env tyConEnv in

    let params = map (setSymbol env.currentEnv.tyVarEnv) t.params in
    let params = map snd params in

    TmRecType {t with ident = ident,
                      params = params,
                      inexpr = symbolizeExpr env t.inexpr}
  | TmRecField t ->
    TmRecField {t with inexpr = symbolizeExpr env t.inexpr,
                       tyIdent = symbolizeType env t.tyIdent}
  | TmExtRecord t ->
    let ident = getSymbol {kind = "type constructor",
                           info = [t.info],
                           allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in
    let bindings = mapMap (symbolizeExpr env) t.bindings in
    TmExtRecord {t with ident = ident, bindings = bindings}
  | TmExtExtend t ->
    let e = symbolizeExpr env t.e in
    let bindings = mapMap (symbolizeExpr env) t.bindings in
    TmExtExtend {t with bindings = bindings, e = e}
end

lang QualifiedNameSym = Sym + QualifiedTypeAst
  sem symbolizeType env =
  | TyQualifiedName t ->
      let lhs = getSymbol {kind = "language",
                           info = [t.info],
                           allowFree = false}
                          env.namespaceEnv
                          t.lhs in

      let langEnv = match mapLookup (nameGetStr lhs) env.langEnv with Some langEnv then langEnv else env.currentEnv in
      let rhs = match mapLookup (nameGetStr t.rhs) langEnv.tyConEnv with Some symbRhs
                then symbRhs
                else t.rhs in

      -- TODO(28/11/2024), voorberg): Add support for using fields on the
      -- right hand side of a qualified name.
      let symbolizePair = lam p.
        match p with (lhs, rhs) in
        let lhs = getSymbol
          {kind = "type", info = [t.info], allowFree = false}
          env.currentEnv.tyConEnv lhs in
        let rhs = getSymbol
          {kind = "constructor", info = [t.info], allowFree = false}
          env.currentEnv.conEnv rhs in
        (lhs, rhs) in

      TyQualifiedName {t with lhs = lhs,
                              rhs = rhs,
                              plus = map symbolizePair t.plus,
                              minus = map symbolizePair t.minus}
end

lang CopatSym = Sym + CopatAst
  sem symbolizeCopat : SymEnv -> Copat -> Copat
  sem symbolizeCopat env =
end

lang RecordCopatSym = CopatSym + RecordCopatAst
  sem symbolizeCopat env =
  | c & (RecordCopat _)  -> c
end

lang DeclCosynSym = Sym + CosynDeclAst
  sem symbolizeCosynStep1 env langEnv =
  | DeclCosyn s ->
    let env = updateEnv env langEnv in

    let ident = if s.isBase then
      nameSym (nameGetStr s.ident)
    else
      getSymbol {kind = "Type Constructor", info = [s.info], allowFree = false} env.currentEnv.tyConEnv s.ident
    in
    match mapAccumL setSymbol env.currentEnv.tyVarEnv s.params with (_, params) in

    let synn = DeclCosyn {s with params = params,
                                  ident = ident} in

    let tyConEnv = if s.isBase then
      mapInsert (nameGetStr ident) ident langEnv.tyConEnv
    else
      langEnv.tyConEnv
    in

    ({langEnv with tyConEnv = tyConEnv}, synn)

  sem symbolizeCosynStep2 env langEnv =
  | DeclCosyn s ->
    let env = updateEnv env langEnv in

    let paramPairs = map (lam p. (nameGetStr p, p)) s.params in
    let paramMap = mapFromSeq cmpString paramPairs in

    let env = updateEnv env langEnv in
    let m = mapUnion env.currentEnv.tyVarEnv paramMap in
    let env = symbolizeUpdateTyVarEnv env m in

    let synn = DeclCosyn {s with ty = symbolizeType env s.ty} in

    (langEnv, synn)
end

lang DeclProdExtSym = Sym + SynProdExtDeclAst
  sem symbProdExtDef env params langEnv =
  | def ->
    let ident = getSymbol
      {kind = "Syn Type", info = [NoInfo ()], allowFree = false}
      langEnv.conEnv
      def.ident in

    -- Add syn params and syn idents to tyVarEnv
    let paramPairs = map (lam p. (nameGetStr p, p)) params in
    let paramMap = mapFromSeq cmpString paramPairs in

    -- Find the name of the associated extensible product type
    let tyName = getSymbol
      {kind = "Type Constructor", info = [NoInfo ()], allowFree = false}
      langEnv.tyConEnv
      def.tyName in

    let env = updateEnv env langEnv in
    let m = mapUnion env.currentEnv.tyVarEnv paramMap in
    let env = symbolizeUpdateTyVarEnv env m in

    let tyIdent = symbolizeType env def.tyIdent in

    (langEnv, {ident = ident, tyIdent = tyIdent, tyName = tyName})

  sem symbolizeProdExt env langEnv =
  | SynDeclProdExt s ->
    match mapAccumL (symbProdExtDef env s.params) langEnv s.individualExts with (langEnv, exts) in
    let decl = SynDeclProdExt {s with individualExts = exts,
                                      ident = nameSym (nameGetStr s.ident)} in
    (langEnv, decl)
end

lang DeclCosemSym = Sym + CosemDeclAst + LetSym
  sem symbolizeCosemStep1 env langEnv =
  | DeclCosem s ->
    match setSymbol langEnv.varEnv s.ident with (varEnv, ident) in

    let langEnv = {langEnv with varEnv = varEnv} in
    let decl = DeclCosem {s with ident = ident} in

    (langEnv, decl)

  sem symbolizeCosemStep2 env langEnv =
  | DeclCosem s ->
    let env = updateEnv env langEnv in

    match symbolizeTyAnnot env s.tyAnnot with (tyVarEnv, tyAnnot) in
    let env = symbolizeUpdateTyVarEnv env tyVarEnv in

    let symbArgTy = lam env : SymEnv. lam arg : {ident : Name, tyAnnot : Type}.
        match setSymbol env.currentEnv.varEnv arg.ident with (varEnv, ident) in
        let env = symbolizeUpdateVarEnv env varEnv in

        match symbolizeTyAnnot env arg.tyAnnot with (tyVarEnv, tyAnnot) in
        let env = symbolizeUpdateTyVarEnv env tyVarEnv in

        (env, {ident = ident, tyAnnot = tyAnnot})
    in
    match mapAccumL symbArgTy env s.args with (env, args) in

    let symbCases = lam cas : (Copat, Expr).
        -- let copat = symbolizeCopat env cas.0 in
        let copat = cas.0 in
        let thn = symbolizeExpr env cas.1 in
        (copat, thn)
    in
    let cases = map symbCases s.cases in

    DeclCosem {s with cases = cases,
                      args = args,
                      tyAnnot = tyAnnot}
end

lang DeclExtRecLangSym = DeclSym + LangDeclAst + TypeDeclAst + SemDeclAst +
                         SynDeclAst + LetSym + SynProdExtDeclAst + CosynDeclAst +
                         CosemDeclAst + RecordCopatAst + DeclSynSym +
                         InnerDeclTypeSym + DeclSemSym + DeclCosynSym +
                         DeclProdExtSym + DeclCosemSym
  -- TODO(25-09-2024, voorberg): A bunch of symbols are created manually
  -- through `nameSym`. These should probably be replaced with calls to
  -- `setSymbol` to detect duplicates and provide standardized error messages.
  sem symbolizeDecl env =
  | DeclLang t ->
    -- Symbolize the name of the language
    match setSymbol env.namespaceEnv t.ident with (namespaceEnv, ident) in
    let env = {env with namespaceEnv = namespaceEnv} in

    -- Symbolize included languages
    let includes = map (getSymbol {kind = "language", info = [t.info], allowFree = false} env.namespaceEnv) t.includes in

    -- Create new langEnv and include the names defined in the included languages
    let includedLangEnvs = map
      (lam incl. match mapLookup (nameGetStr incl) env.langEnv
                 with Some langEnv then langEnv
                 else errorMulti
                   [(t.info, nameGetStr incl)]
                   "The included language can not be found!")
    t.includes in

    let langEnv : NameEnv = foldl mergeNameEnv _nameEnvEmpty includedLangEnvs in

    let isSynDecl = lam d. match d with DeclSyn _ then true else false in
    let synDecls = filter isSynDecl t.decls in

    let isProdDecl = lam d. match d with SynDeclProdExt _ then true else false in
    let prodDecls = filter isProdDecl t.decls in

    let isSemDecl = lam d. match d with DeclSem _ then true else false in
    let semDecls = filter isSemDecl t.decls in

    let isTypeDecl = lam d. match d with DeclType _ then true else false in
    let typeDecls = filter isTypeDecl t.decls in

    let isCosynDecl = lam d. match d with DeclCosyn _ then true else false in
    let cosynDecls = filter isCosynDecl t.decls in

    let isCosemDecl = lam d. match d with DeclCosem _ then true else false in
    let cosemDecls = filter isCosemDecl t.decls in

    match mapAccumL (symbolizeSynStep1 env) langEnv synDecls
    with (langEnv, synDecls) in

    match mapAccumL (symbolizeCosynStep1 env) langEnv cosynDecls
    with (langEnv, cosynDecls) in

    match mapAccumL (symbolizeDeclType env) langEnv typeDecls
    with (langEnv, typeDecls) in

    match mapAccumL (symbolizeSynStep2 env) langEnv synDecls
    with (langEnv, synDecls) in

    match mapAccumL (symbolizeCosynStep2 env) langEnv cosynDecls
    with (langEnv, cosynDecls) in

    match mapAccumL (symbolizeProdExt env) langEnv prodDecls
    with (langEnv, prodDecls) in

    match mapAccumL (symbolizeSemStep1 env) langEnv semDecls
    with (langEnv, semDecls) in

    match mapAccumL (symbolizeCosemStep1 env) langEnv cosemDecls
    with (langEnv, cosemDecls) in

    let semDecls = map (symbolizeSemStep2 env langEnv) semDecls in
    let cosemDecls = map (symbolizeCosemStep2 env langEnv) cosemDecls in


    let env = {env with langEnv = mapInsert (nameGetStr t.ident) langEnv env.langEnv} in
    let t = {t with decls = join [typeDecls, synDecls, cosynDecls, semDecls, prodDecls, cosemDecls],
                    includes = includes,
                    ident = ident} in

    (env, DeclLang t)
end

lang ExtRecSym = ExtRecordSym + QualifiedNameSym + RecordCopatSym +
                 DeclExtRecLangSym + MLangSymWihoutLang
end

lang ExtRecTestLang = TestLangWithoutLang + ExtRecSym
  sem isFullySymbolizedExpr =
  | TmRecType t ->
    foldl _and (lam. true) [
      lam. nameHasSym t.ident,
      lam. forAll nameHasSym t.params,
      isFullySymbolizedExpr t.inexpr
    ]
  | TmRecField t ->
    _and (isFullySymbolizedExpr t.inexpr) (isFullySymbolizedType t.tyIdent)
  | TmExtRecord t ->
    foldl _and (lam. true) [
      lam. nameHasSym t.ident,
      foldl (_andFold isFullySymbolizedExpr) (lam. true) (mapValues t.bindings)
    ]
  | TmExtExtend t ->
    _and (isFullySymbolizedExpr t.e)
         (foldl (_andFold isFullySymbolizedExpr) (lam. true) (mapValues t.bindings))

  sem isFullySymbolizedType =
  | TyQualifiedName t ->
    let fullySymbolizedPair = lam p. and (nameHasSym p.0) (nameHasSym p.1) in
    foldl _and (lam. true) [
      lam. nameHasSym t.lhs,
      lam. nameHasSym t.rhs,
      lam. forAll fullySymbolizedPair t.plus,
      lam. forAll fullySymbolizedPair t.minus
    ]

  sem isFullySymbolizedCopat =
  | RecordCopat _ -> lam. true

  sem isFullySymbolizedDecl =
  | DeclCosyn s ->
    _and (lam. and (nameHasSym s.ident) (forAll nameHasSym s.params))
         (isFullySymbolizedType s.ty)
  | DeclCosem s ->
    let isFullySymbolizedArg = lam arg.
      _and (lam. nameHasSym arg.ident) (isFullySymbolizedType arg.tyAnnot) in

    let isFullySymbolizedCase = lam cas.
      _and (isFullySymbolizedCopat cas.0) (isFullySymbolizedExpr cas.1) in

    foldl _and (lam. true) [
      lam. nameHasSym s.ident,
      foldl (_andFold isFullySymbolizedArg) (lam. true) s.args,
      foldl (_andFold isFullySymbolizedCase) (lam. true) s.cases
    ]
  | SynDeclProdExt s ->
    let isSymbolizedExt = lam ext.
      _and (lam. nameHasSym ext.ident) (isFullySymbolizedType ext.tyIdent) in

    let isSymbolizedGlobalExt = lam ext.
      optionMapOrElse (lam. lam. true) (isFullySymbolizedType) ext in

    foldl _and (lam. true) [
      lam. nameHasSym s.ident,
      lam. forAll nameHasSym s.params,
      foldl (_andFold isSymbolizedExt) (lam. true) s.individualExts,
      isSymbolizedGlobalExt s.globalExt
    ]
end

mexpr
use ExtRecTestLang in
use MLangPrettyPrint in
use LanguageComposer in

-- Cosyn Symbolization
let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_cosyn_ "Foo" [] true (tyrecord_ [("x", tyint_)])
    ]
  ],
  expr = uunit_
} in

let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in
utest length p.decls with 1 in
utest isFullySymbolizedProgram p () with true in

-- Cosyn Symbolization with params
let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_cosyn_ "Foo" ["a"] true (tyrecord_ [("x", tyvar_ "a")])
    ]
  ],
  expr = uunit_
} in

let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in
utest length p.decls with 1 in
utest isFullySymbolizedProgram p () with true in

-- Test symbolization of prodext
let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_syn_ "Expr" [("TmInt", tyrecord_ [("val", tyint_)])]
    ]
    ,
    decl_langi_ "L1" ["L0"] [
      decl_syn_prodext_ "Expr" (None ()) [("TmInt", (tyrecord_ [("val2", tyint_)]))]
    ]
  ],
  expr = uunit_
} in

let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in
utest isFullySymbolizedProgram p () with true in

-- Test symbolization of cosem
let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_cosem_ "foo" [("x", tyint_)] [(record_copat_  ["x"], uunit_)] false
    ]
  ],
  expr = uunit_
} in

let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in
utest isFullySymbolizedProgram p () with true in

()