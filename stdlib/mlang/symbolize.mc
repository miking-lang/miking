-- Symbolization for MLang programs:
-- (1) Assign names to all names introduced in MLang such as
--     let-bindings, language fragments, syntax definitions, etc.
-- (2) Desugar `TmUse` and `TyUse` by bringing the symbols defined in
--     the specified langauge fragment into scope. 

include "bool.mc"
include "error.mc"
include "map.mc"
include "name.mc"
include "set.mc"

include "pprint.mc"
include "ast.mc"
include "language-composer.mc"

include "mexpr/symbolize.mc"
include "mexpr/ast-builder.mc"

let fst : all a. all b. (a, b) -> a = lam p.
  match p with (res, _) in res

let snd : all a. all b. (a, b) -> b = lam p.
  match p with (_, res) in res

let sem2ident = lam d.
  use MLangAst in 
  match d with DeclSem d in d.ident

let syn2ident = lam d.
  use MLangAst in  
  match d with DeclSyn d in d.ident

let type2ident = lam d.
  use MLangAst in 
  match d with DeclType d in d.ident 

let name2pair : Name -> (String, Name) = lam n.
  (nameGetStr n, n)

let updateEnv : SymEnv -> NameEnv -> SymEnv = lam symEnv. lam langEnv.
  {symEnv with currentEnv = mergeNameEnv (symEnv.currentEnv) langEnv}

lang TmUseSym = Sym + UseAst
  sem symbolizeExpr env = 
  | TmUse t -> 
    -- TODO: Prevent TmUse <lang> in that specific lang.
    match mapLookup (nameGetStr t.ident) env.langEnv with Some langEnv 
      then 
        symbolizeExpr (updateEnv env langEnv) t.inexpr
      else 
        symLookupError 
          {kind = "language", info = [t.info], allowFree = false}
          t.ident
end

lang TyUseSym = Sym + TyUseAst
  sem symbolizeType env = 
  | TyUse t -> 
    match mapLookup (nameGetStr t.ident) env.langEnv with Some langEnv 
      then 
        symbolizeType (updateEnv env langEnv) t.inty
      else 
        symLookupError 
          {kind = "language", info = [t.info], allowFree = false}
          t.ident
end

lang DeclSym = DeclAst + Sym
  sem symbolizeDecl : SymEnv -> Decl -> (SymEnv, Decl)
end

lang DeclLetSym = DeclSym + LetDeclAst + LetSym
  sem symbolizeDecl env = 
  | DeclLet t ->  
    match symbolizeTyAnnot env t.tyAnnot with (tyVarEnv, tyAnnot) in
    match setSymbol env.currentEnv.varEnv t.ident with (varEnv, ident) in
    let env = symbolizeUpdateVarEnv env varEnv in 
    let env = symbolizeUpdateTyVarEnv env tyVarEnv in 
    let decl = DeclLet {t with ident = ident,
                        tyAnnot = tyAnnot,
                        body = symbolizeExpr env t.body} in 
    (env, decl)
end

lang DeclTypeSym = DeclSym + TypeDeclAst
  sem symbolizeDecl env = 
  | DeclType t -> 
    match setSymbol env.currentEnv.tyConEnv t.ident with (tyConEnv, ident) in
    let env = symbolizeUpdateTyConEnv env tyConEnv in 
    match mapAccumL setSymbol env.currentEnv.tyVarEnv t.params with (tyVarEnv, params) in
    let decl = DeclType {t with ident = ident,
                                params = params,
                                tyIdent = symbolizeType (symbolizeUpdateTyVarEnv env tyVarEnv) t.tyIdent} in 
    let env = symbolizeUpdateTyVarEnv env tyVarEnv in 
    (env, decl)
end


lang DeclRecLetsSym = DeclSym + RecLetsDeclAst + LetSym
  sem symbolizeDecl env = 
  | DeclRecLets t -> 
    -- Generate fresh symbols for all identifiers and add to the environment
    let setSymbolIdent = lam env. lam b.
      match setSymbol env b.ident with (env, ident) in
      (env, {b with ident = ident})
    in

    match mapAccumL setSymbolIdent env.currentEnv.varEnv t.bindings with (varEnv, bindings) in
    let newEnv = symbolizeUpdateVarEnv env varEnv in

    -- Symbolize all bodies with the new environment
    let bindings =
    map (lam b. match symbolizeTyAnnot env b.tyAnnot with (tyVarEnv, tyAnnot) in
                {b with body = symbolizeExpr (symbolizeUpdateTyVarEnv newEnv tyVarEnv) b.body,
                        tyAnnot = tyAnnot})  bindings in

    (newEnv, DeclRecLets {t with bindings = bindings})
end

lang DeclConDefSym = DeclSym + DataDeclAst
  sem symbolizeDecl env = 
  | DeclConDef t -> 
    match setSymbol env.currentEnv.conEnv t.ident with (conEnv, ident) in

    let decl = DeclConDef {t with ident = ident,
                                  tyIdent = symbolizeType env t.tyIdent} in 
    let env = symbolizeUpdateConEnv env conEnv in 
    (env, decl)
end

lang DeclUtestSym = DeclSym + UtestDeclAst 
  sem symbolizeDecl env = 
  | DeclUtest t -> 
    -- This can be rewritten to use a shallow map on declarations. E.g.
    -- smap (symbolizeExpr env) (DeclUtest t) 
    let decl = DeclUtest {t with test = symbolizeExpr env t.test,
                                  expected = symbolizeExpr env t.expected,
                                  tusing = optionMap (symbolizeExpr env) t.tusing} in 
    (env, decl)
end

lang DeclExtSym = DeclSym + ExtDeclAst 
  sem symbolizeDecl env = 
  | DeclExt t & d-> 
    if env.ignoreExternals then
      (env, d)
    else 
      match setSymbol env.currentEnv.varEnv t.ident with (varEnv, ident) in
      let decl = DeclExt {t with ident = ident,
                                 tyIdent = symbolizeType env t.tyIdent} in 
      let env = symbolizeUpdateVarEnv env varEnv in 
      (env, decl)
end

lang DeclLangSym = DeclSym + LangDeclAst + TypeDeclAst + SemDeclAst + 
                   SynDeclAst + LetSym
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

    let isSemDecl = lam d. match d with DeclSem _ then true else false in 
    let semDecls = filter isSemDecl t.decls in 

    let isTypeDecl = lam d. match d with DeclType _ then true else false in 
    let typeDecls = filter isTypeDecl t.decls in 

    -- 1. Symbolize ident and params of SynDecls in this langauge
    let symbSynStep1 = lam langEnv : NameEnv. lam synDecl.
      match synDecl with DeclSyn s in
      let env = updateEnv env langEnv in 

      let ident = nameSym (nameGetStr s.ident) in 
      match mapAccumL setSymbol env.currentEnv.tyVarEnv s.params with (_, params) in

      let synn = DeclSyn {s with params = params,
                                  ident = ident} in 

      let tyConEnv = if eqi 0 (length s.includes) then
        mapInsert (nameGetStr ident) ident langEnv.tyConEnv
      else 
        langEnv.tyConEnv
      in

      ({langEnv with tyConEnv = tyConEnv}, synn)
    in
    match mapAccumL symbSynStep1 langEnv synDecls with (langEnv, synDecls) in 

    -- 2. Symbolize DeclType, params, and body.
    let symbDeclType = lam langEnv : NameEnv. lam typeDecl. 
      match typeDecl with DeclType t in 

      -- Symbolize ident
      let ident = nameSym (nameGetStr t.ident) in 

      -- -- Check for name conflicts with syns and other types.
      -- -- Throw an error if DeclType is included with the same identifier
      -- errorOnNameConflict includedTypes ident langIdent t.info ;
      -- -- Throw an error if a DeclSyn is  or defined with the same identifier
      -- errorOnNameConflict langEnv.syns ident langIdent t.info ; 

      -- Symbolize parameters
      let env = updateEnv env langEnv in 
      match mapAccumL setSymbol env.currentEnv.tyVarEnv t.params with (tyVarEnv, params) in

      -- Symbolize type annotation
      let tyAnnot = symbolizeType (symbolizeUpdateTyVarEnv env tyVarEnv) t.tyIdent in

      let decl = DeclType {t with ident = ident,
                                  tyIdent = tyAnnot,
                                  params = params} in 

      let langEnv = {langEnv with tyConEnv = mapInsert (nameGetStr t.ident) ident langEnv.tyConEnv} in

      (langEnv, decl)
    in 
    match mapAccumL symbDeclType langEnv typeDecls with (langEnv, typeDecls) in 

    -- 3. Symbolize syntax constructors (add defs to conEnv)
    let symbDef = lam params : [Name]. lam langEnv : NameEnv. lam def : {ident : Name, tyIdent : Type}. 
      match setSymbol langEnv.conEnv def.ident with (conEnv, ident) in 
      let langEnv = {langEnv with conEnv = conEnv} in 

      let env = updateEnv env langEnv in 

      -- Add syn params and syn idents to tyVarEnv
      let paramPairs = map (lam p. (nameGetStr p, p)) params in 
      let paramMap = mapFromSeq cmpString paramPairs in 

      let m = mapUnion env.currentEnv.tyVarEnv paramMap in 
      let env = symbolizeUpdateTyVarEnv env m in 

      let tyIdent = symbolizeType env def.tyIdent in

      (langEnv, {ident = ident, tyIdent = tyIdent})
    in
    let symbSynConstructors = lam langEnv. lam synDecl. 
      match synDecl with DeclSyn s in 
      match mapAccumL (symbDef s.params) langEnv s.defs with (langEnv, defs) in 
      let decl = DeclSyn {s with defs = defs} in
      (langEnv, decl)
    in 
    match mapAccumL symbSynConstructors langEnv synDecls with (langEnv, synDecls) in 

    -- 4. Assign names to semantic functions
    let symbSem = lam langEnv : NameEnv. lam declSem. 
      match declSem with DeclSem s in 
      match setSymbol langEnv.varEnv s.ident with (varEnv, ident) in 

      let langEnv = {langEnv with varEnv = varEnv} in 
      let decl = DeclSem {s with ident = ident} in 
  
      (langEnv, decl)
    in 
    match mapAccumL symbSem langEnv semDecls with (langEnv, semDecls) in 

    -- 5. Assign names to semantic bodies, params, and types
    let symbSem2 = lam langEnv : NameEnv. lam declSem. 
      match declSem with DeclSem s in 

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
      let result = match optionMap (lam a. mapAccumL symbArgTy env a) s.args with Some (env, args) 
                    then (env, Some args) else (env, None ()) in 
      match result with (env, args) in 


      let symbCases = lam cas : {pat : Pat, thn : Expr}. 
          match symbolizePat env (mapEmpty cmpString) cas.pat with (thnVarEnv, pat) in
          let varEnv = mapUnion env.currentEnv.varEnv thnVarEnv in 
          let thn = symbolizeExpr (symbolizeUpdateVarEnv env varEnv) cas.thn in
          {pat = pat, thn = thn}
      in
      let cases = map symbCases s.cases in

      let decl = DeclSem {s with cases = cases, 
                                  tyAnnot = tyAnnot,
                                  args = args} in 

      decl
    in
    let semDecls = map (symbSem2 langEnv) semDecls in

    let env = {env with langEnv = mapInsert (nameGetStr t.ident) langEnv env.langEnv} in 
    let t = {t with decls = join [typeDecls, synDecls, semDecls],
                    includes = includes,
                    ident = ident} in

    (env, DeclLang t)
end

lang MLangProgramSym = MLangTopLevel + DeclSym
  sem symbolizeMLang : SymEnv -> MLangProgram -> (SymEnv, MLangProgram)
  sem symbolizeMLang env =| prog -> 
    match mapAccumL symbolizeDecl env prog.decls with (env, decls) in
    let expr = symbolizeExpr env prog.expr in 
    (env, {
      decls = decls,
      expr = expr
    })
end

lang MLangSym = MLangAst + MExprSym + 
                TmUseSym + TyUseSym + 
                DeclLetSym + DeclTypeSym + DeclRecLetsSym +
                DeclConDefSym + DeclUtestSym + DeclExtSym +
                DeclLangSym + MLangProgramSym
end

lang TestLang = MLangSym + SymCheck + MLangPrettyPrint
  sem isFullySymbolizedExpr = 
  | TmUse t -> 
    error "Symbolization should get rid of all occurrences of TmUse!"

  sem isFullySymbolizedDecl : Decl -> () -> Bool
  sem isFullySymbolizedDecl =
  | DeclLang l -> 
    _and (lam. nameHasSym l.ident) (_and 
        (lam. forAll nameHasSym l.includes)
        (foldl (_andFold isFullySymbolizedDecl) (lam. true) l.decls)
    )
  | DeclSyn l -> 
    _and (lam. nameHasSym l.ident) (_and 
        (lam. (forAll nameHasSym l.params))
        (lam. (forAll nameHasSym (map (lam d. d.ident) l.defs)))
    )
  | DeclSem l -> 
    let args = optionGetOrElse (lam. []) l.args in 
    let argIdents = map (lam a. a.ident) args in 
    let argTys = map (lam a. a.tyAnnot) args in 
    let casePats = map (lam c. c.pat) l.cases in 
    let caseThns = map (lam c. c.thn) l.cases in 

    foldl _and (lam. true) [
      lam. nameHasSym l.ident,
      isFullySymbolizedType l.tyAnnot,
      isFullySymbolizedType l.tyBody,
      lam. forAll nameHasSym argIdents,
      foldl (_andFold isFullySymbolizedType) (lam. true) argTys,
      foldl (_andFold isFullySymbolizedPat) (lam. true) casePats, 
      foldl (_andFold isFullySymbolizedExpr) (lam. true) caseThns
    ]
  | DeclLet l ->
    foldl _and (lam. true) [
      lam. nameHasSym l.ident,
      isFullySymbolizedType l.tyAnnot,
      isFullySymbolizedExpr l.body
    ]
  | DeclType l -> 
    _and (lam. nameHasSym l.ident) (_and 
          (lam. (forAll nameHasSym l.params))
          (isFullySymbolizedType l.tyIdent))
  | DeclConDef l ->
    _and (lam. nameHasSym l.ident) (isFullySymbolizedType l.tyIdent)

  sem isFullySymbolizedType =
  | TyUse _ -> error "Symbolization should get rid of TyUse!"

  sem isFullySymbolizedProgram : MLangProgram -> () -> Bool
  sem isFullySymbolizedProgram =
  | prog -> 
    _and 
      (isFullySymbolizedExpr prog.expr)
      (foldl (_andFold isFullySymbolizedDecl) (lam. true) prog.decls)
end

let synDeclIdentHasSymbolized = lam decl. 
  use MLangAst in 
  match decl with DeclSyn t then
    (if nameHasSym t.ident then
      ()
    else error (join [
      "SynDecl '",
      nameGetStr t.ident,
      "' has not been symbolized!"
    ])) ;
    let defHasName = lam def : {ident : Name, tyIdent : Type}. 
      if nameHasSym def.ident then
        ()
      else error (join [
        "Syntax constructor '",
        nameGetStr def.ident,
        "' has not been symbolized!"
      ])
    in 
    iter defHasName t.defs
  else 
    ()
    

let typeDeclIdentHasSymbolized = lam decl. 
  use MLangAst in 
  -- Check syn ident has been symbolized
  match decl with DeclType t then
    if nameHasSym t.ident then
        ()
    else error (join [
        "TypeDecl '",
        nameGetStr t.ident,
        "' has not been symbolized!"
    ])
  else 
    ()

let semDeclIdentHasSymbolized = lam decl. 
  use MLangAst in 
  -- Check syn ident has been symbolized
  match decl with DeclSem t then
    if nameHasSym t.ident then
      ()
    else error (join [
      "SemDecl '",
      nameGetStr t.ident,
      "' has not been symbolized!"
    ])
  else 
    ()


mexpr
use TestLang in 
use LanguageComposer in 
let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_syn_ "Foo" [("Baz", tyint_), ("BazBaz", tychar_)],
      decl_type_ "Bar" [] tyint_,
      decl_sem_ "f" [] []
    ]
  ],
  expr = bind_ (use_ "L1") (var_ "f")
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in 
let l1 = head p.decls in 
match l1 with DeclLang l in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolized p.expr with true in 
utest nameHasSym l.ident with true in

-- Test DeclType wand DeclConDef with polymorhpic parameters
let p : MLangProgram = {
  decls = [
    decl_type_ "Option" ["a"] (tyvariant_ []),
    decl_condef_ "None" (tyall_ "a" (tyarrow_ tyunit_ (tyapp_ (tycon_ "Option") (tyvar_ "a")))),
    decl_condef_ "Some" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyapp_ (tycon_ "Option") (tyvar_ "a"))))
  ],
  expr = uunit_
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_syn_ "Foo" [("Baz", tyint_), ("BazBaz", tychar_)],
      decl_type_ "Bar" [] tyint_,
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L2" ["L1"] [
      decl_syn_ "Foo" [],
      decl_sem_ "f" [] []
    ]
  ],
  expr = bind_ (use_ "L2") (var_ "f")
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in 
let l1 = head p.decls in 
let l2 = head (tail p.decls) in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolizedDecl l2 () with true in 
match l2 with DeclLang ld in 
match head (tail ld.decls) with DeclSem f in 
utest length f.includes with 1 in 
utest isFullySymbolized p.expr with true in 
match head ld.decls with DeclSyn foo in 
utest length foo.includes with 1 in

let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_syn_ "Foo" [("Baz", tyint_)]
    ],
    decl_lang_ "L2" [
      decl_syn_ "Foo" [("BazBaz", tychar_)]
    ],
    decl_langi_ "L12" ["L1", "L2"] []
  ],
  expr = bind_ (use_ "L2") (int_ 10)
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in 
let l1 = head p.decls in 
let l2 = get p.decls 1 in 
let l12 = get p.decls 2 in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolizedDecl l2 () with true in 
utest isFullySymbolizedDecl l12 () with true in

let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_sem_ "f" [] []
    ],
    decl_lang_ "L2" [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L12" ["L1", "L2"] []
  ],
  expr = bind_ (use_ "L12") (appf1_ (var_ "f") (int_ 10))
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in 
match l12 with DeclLang l in
utest length l.decls with 1 in 
match head l.decls with DeclSyn synDecl in 
utest length synDecl.includes with 2 in 
-- utest foldl and true (map nameHasSym synDecl.includes) with true in 

let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_syn_ "Foo" []
    ],
    decl_langi_ "L2" ["L1"] []
  ],
  expr = uunit_
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in 
let l1 = head p.decls in 
match l1 with DeclLang l in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolized p.expr with true in 
utest nameHasSym l.ident with true in
let l2 = head (tail p.decls) in 
match l2 with DeclLang l in 
utest isFullySymbolizedDecl l2 () with true in
utest length l.decls with 1 in 

-- Test that variable symbolization within semantic case bodies
let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_sem_ 
        "f"
        [("x", tyint_)]
        [(pvar_ "y", addi_ (var_ "x") (var_ "y"))]
    ]
  ],
  expr = bind_ (use_ "L1") (appf1_ (var_ "f") (int_ 10))
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in 

-- Test that symbolization of semantic function points to the correct
-- semantic function under language composition
-- Also test that symbolization removes occurrences of TmUse.
let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L2" ["L1"] [
      decl_sem_ "f" [] []
    ]
  ],
  expr = (bind_) (use_ "L2") (var_ "f")
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in 
match get p.decls 1 with DeclLang l2 in 
match head l2.decls with DeclSem f2 in
match p.expr with TmVar v in 
utest nameEqSym v.ident f2.ident with true in 

-- Test that constructors can be used in the langauge that they are defined
let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_syn_ "Foo" [("Bar", tyint_)]
    ]
  ],
  expr = (bind_) (use_ "L1") (conapp_ "Bar" (int_ 10))
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test that constructors that are defined in an included langauge can be used 
let p : MLangProgram = {
  decls = [
    decl_lang_ "L1" [
      decl_syn_ "Foo" [("Bar", tyint_)]
    ],
    decl_langi_ "L2" ["L1"] []
  ],
  expr = (bind_) (use_ "L2") (conapp_ "Bar" (int_ 10))
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
match get p.decls 1 with DeclLang l2 in 
utest length (l2.decls) with 1 in
utest isFullySymbolizedProgram p () with true in

-- Sum Extension Test Case
let baseSyn = decl_syn_ "Expr" [("IntExpr", tyint_), 
                                ("AddExpr", tytuple_ [tycon_ "Expr", tycon_ "Expr"])] in 
let baseSem = decl_sem_ "eval" [] [(pcon_ "IntExpr" (pvar_ "i"), var_ "i"),
                                   (pcon_ "AddExpr" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]), 
                                    addi_ (appf1_ (var_ "eval") (var_ "lhs")) (appf1_ (var_ "eval") (var_ "rhs")))] in 
let sugarSyn = decl_syn_ "Expr" [("IncrExpr", tycon_ "Expr")] in 
let sugarEval = decl_sem_ "eval" [] [(pcon_ "IncrExpr" (pvar_ "e"), addi_ (int_ 1) (appf1_ (var_ "eval") (var_ "e")))] in 
let p : MLangProgram = {
  decls = [
    decl_lang_ "MyIntArith" [baseSyn, baseSem],
    decl_langi_ "SugaredIntArith" ["MyIntArith"] [sugarSyn, sugarEval]
  ],
  -- expr = uunit_ 
  expr = bind_ (use_ "SugaredIntArith") 
               (appf1_ (var_ "eval") 
                       (conapp_ "AddExpr" (utuple_ [(conapp_ "IncrExpr" (conapp_ "IntExpr" (int_ 21))),
                                                    (conapp_ "IntExpr" (int_ 1))])))
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test type variable, 'all', and let type annotations
let p : MLangProgram = {
  decls = [decl_let_ "id" 
                     (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a"))) 
                     (lam_ "x" (tyvar_ "a") (var_ "x"))],
  expr = appf1_ (var_ "id") (int_ 1)
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test syn with type variable
-- Test type variable, 'all', and let type annotations
let p : MLangProgram = {
  decls = [decl_lang_ "SomeListLang" [
    decl_syn_params_ "MyList" ["a"] [("Nil", tyunit_), ("Cons", tytuple_ [tyvar_ "a", tycon_ "MyList"])] 
  ]],
  expr = uunit_
} in 
let p = composeProgram p in 
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test sem with type variable
let p = {
  decls = [decl_lang_ "SomeLang" [
    decl_semty_ "id" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a"))) 
  ]],
  expr = uunit_
} in
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test usage of type defined outside of language used in language
let p : MLangProgram = {
  decls = [
    decl_type_ "Foo" [] tyint_,
    decl_lang_ "SomeListLang" [
      decl_syn_ "MyList" [("Nil", tycon_ "Foo")] 
    ]
  ],
  expr = uunit_
} in 
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test desugaring of TyUse
let p : MLangProgram = {
  decls = [
    decl_lang_ "SomeLang" [
      decl_type_ "Foo" [] tyint_
    ],
    decl_type_ "Bar" [] (tyuse_ "SomeLang" (tycon_ "Foo"))
  ],
  expr = uunit_
} in 
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test that type declarations in a language are usuably in langauges that 
-- extend said language.
let p : MLangProgram = {
  decls = [
    decl_lang_ "SomeLang" [
      decl_type_ "Foo" [] tyint_
    ],
    decl_langi_ "OtherLang" ["SomeLang"] [
      decl_syn_ "Baz" [("Bar", tycon_ "Foo")] 
    ]
  ],
  expr = uunit_
} in 
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test transitive dependencies. In this case, L2 uses symbols that are 
-- defined in L0. These should still be in scope in L2 because L1 extends L0. 
let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_syn_ "Foo" [("Bar", tyint_)]
    ],
    decl_langi_ "L1" ["L0"] [],
    decl_langi_ "L2" ["L1"] [
      decl_sem_ "f" [] [(pcon_ "Bar" pvarw_, int_ 1)]
    ]
  ],
  expr = uunit_
} in 
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test that a type parameter introduced in a semantic function type
-- annotation can be used in the body of that semantic function.
let p : MLangProgram = {
  decls = [
    decl_lang_ "L" [
      decl_semty_cases_ "f" 
                        (tyall_ "a" (tyarrow_ (tyvar_ "a") tyint_))
                        [(pvarw_, let_ "x" 
                                        (tyarrow_ (tyvar_ "a") tyint_)
                                        (int_ 10))]
      ]
  ],
  expr = uunit_
} in 
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test case related to type definitions in language fragments
let p : MLangProgram = {
  decls = [
    decl_lang_ "L" [
      decl_type_ "T" ["a"] (tyarrow_ (tyvar_ "a") tyint_),
      decl_semty_cases_ "f" 
                        (tyall_ "a" (tyarrow_ (tyvar_ "a") tyint_))
                        [(pvarw_, let_ "x" 
                                        (tyarrow_ (tyvar_ "a") (tyapp_ (tycon_ "T") (tyvar_ "a")))
                                        (int_ 10))]
      ]
  ],
  expr = uunit_
} in 
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
utest isFullySymbolizedProgram p () with true in

-- Test case related to type definitions in language fragments
let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_semty_cases_ 
        "f" 
        (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")))
        [(pvar_ "y", bind_ (let_ "x" (tyvar_ "a") uunit_) (var_ "y"))]
    ],
    decl_langi_ "L1" ["L0"] []
  ],
  expr = uunit_
} in 
let p = composeProgram p in  
match symbolizeMLang symEnvDefault p with (_, p) in 
-- printLn (mlang2str p);
utest isFullySymbolizedProgram p () with true in

()