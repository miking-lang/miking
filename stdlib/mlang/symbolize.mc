include "bool.mc"
include "error.mc"
include "map.mc"
include "name.mc"
include "set.mc"

include "./pprint.mc"
include "./ast.mc"

include "mexpr/symbolize.mc"

let mapDisjoint : all a. all b. (Map String a) -> (Map String b) -> Bool = lam l. lam r.
    let leftKeys = setOfSeq cmpString (mapKeys l) in 
    let rightKeys = setOfSeq cmpString (mapKeys r) in 
    setDisjoint leftKeys rightKeys

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

let convertLangEnv : LangEnv -> NameEnv = lam langEnv. 
    use MLangAst in 
    let semIdents = map sem2ident (mapValues langEnv.sems) in 
    let semPairs = map name2pair semIdents in 
    let varEnv = mapFromSeq cmpString semPairs in 

    let synIdents = map syn2ident (mapValues langEnv.syns) in 
    let synPairs = map name2pair synIdents in 
    let tyConEnv = mapFromSeq cmpString synPairs in

    -- Todo: Detect duplicates in declared types, defined types and syns!
    let typeIdents = map 
        type2ident
        (mapValues (mapUnion langEnv.includedTypes langEnv.definedTypes))
    in
    let typePairs = map name2pair typeIdents in
    let tyConEnv = mapUnion tyConEnv (mapFromSeq cmpString typePairs) in

    let conIdents = map
        (lam d. match d with DeclSyn s in map (lam def. def.ident) s.defs)
        (mapValues langEnv.syns)
    in 
    let conPairs = map name2pair (join conIdents) in 
    let conEnv = mapFromSeq cmpString conPairs in 
    
    {_nameEnvEmpty with varEnv = varEnv,
                        conEnv = conEnv,
                        tyConEnv = tyConEnv}

let convertNameEnv : NameEnv -> SymEnv = lam env.
    {_symEnvEmpty with currentEnv = env}


let combineMaps : all a. [Map String a] -> Map String [a] = lam maps. 
    let addMap = lam acc : Map String [a]. lam m : Map String a. 
        let pairs = mapToSeq m in 
        let addPair = lam acc. lam pair : (String, a).
            match pair with (s, n) in 
            let newValue = match mapLookup s acc with Some names then
                cons n names
            else 
                [n]
            in 
            mapInsert s newValue acc
        in 
        foldl addPair acc pairs
    in
    foldl addMap (mapEmpty cmpString) maps

lang MLangSym = MLangAst + MExprSym 
    sem symbolizeMLang : SymEnv -> MLangProgram -> (SymEnv, MLangProgram)
    sem symbolizeMLang env =| prog -> 
        match mapAccumL symbolizeDecl env prog.decls with (env, decls) in
        let expr = symbolizeExpr env prog.expr in 
        (env, {
            decls = decls,
            expr = expr
        })

    sem symbolizeExpr env = 
    | TmUse t -> 
        match mapLookup (nameGetStr t.ident) env.langEnv with Some langEnv 
            then 
                let langNameEnv = convertLangEnv langEnv in 
                let env = {env with currentEnv = mergeNameEnv env.currentEnv langNameEnv} in 
                symbolizeExpr env t.inexpr
            else 
                symLookupError 
                    {kind = "language", info = [t.info], allowFree = false}
                    t.ident

    sem symbolizeDecl : SymEnv -> Decl -> (SymEnv, Decl)
    sem symbolizeDecl env = 
    | DeclInclude r ->
        error "Symbolization expects all DeclInclude to have been removed!"
    | DeclLet t ->  
        match symbolizeTyAnnot env t.tyAnnot with (tyVarEnv, tyAnnot) in
        match setSymbol env.currentEnv.varEnv t.ident with (varEnv, ident) in
        let env = updateVarEnv env varEnv in 
        let decl = DeclLet {t with ident = ident,
                            tyAnnot = tyAnnot,
                            body = symbolizeExpr env t.body} in 
        (env, decl)
    | DeclType t -> 
        match setSymbol env.currentEnv.tyConEnv t.ident with (tyConEnv, ident) in
        match mapAccumL setSymbol env.currentEnv.tyVarEnv t.params with (tyVarEnv, params) in
        let decl = DeclType {t with ident = ident,
                             params = params,
                             tyIdent = symbolizeType (updateTyVarEnv env tyVarEnv) t.tyIdent} in 
        let env = updateTyConEnv env tyConEnv in 
        (env, decl)
    | DeclRecLets t -> 
        -- Generate fresh symbols for all identifiers and add to the environment
        let setSymbolIdent = lam env. lam b.
            match setSymbol env b.ident with (env, ident) in
            (env, {b with ident = ident})
        in

        match mapAccumL setSymbolIdent env.currentEnv.varEnv t.bindings with (varEnv, bindings) in
        let newEnv = updateVarEnv env varEnv in

        -- Symbolize all bodies with the new environment
        let bindings =
        map (lam b. match symbolizeTyAnnot env b.tyAnnot with (tyVarEnv, tyAnnot) in
                    {b with body = symbolizeExpr (updateTyVarEnv newEnv tyVarEnv) b.body,
                            tyAnnot = tyAnnot})  bindings in

        (newEnv, DeclRecLets {t with bindings = bindings})
    | DeclConDef t -> 
        match setSymbol env.currentEnv.conEnv t.ident with (conEnv, ident) in

        let decl = DeclConDef {t with ident = ident,
                                      tyIdent = symbolizeType env t.tyIdent} in 
        let env = updateConEnv env conEnv in 
        (env, decl)
    | DeclUtest t -> 
        -- This can be rewritten to use a shallow map on declarations. E.g.
        -- smap (symbolizeExpr env) (DeclUtest t) 
        let decl = DeclUtest {t with test = symbolizeExpr env t.test,
                                     expected = symbolizeExpr env t.expected,
                                     tusing = optionMap (symbolizeExpr env) t.tusing} in 
        (env, decl)
    | DeclExt t -> 
        -- When ignoreExternals is set, the DeclExt should have been filtered
        -- out of the program before attempting to symbolize the declarations.
        if env.ignoreExternals then
            error "DeclExt should have been removed when 'ignoreExternals' is true!"
        else 
            match setSymbol env.currentEnv.varEnv t.ident with (varEnv, ident) in
            let decl = DeclExt {t with ident = ident,
                                       tyIdent = symbolizeType env t.tyIdent} in 
            let env = updateVarEnv env varEnv in 
            (env, decl)
    | DeclLang t -> 
        let langStr = nameGetStr t.ident in 

        let ident = nameSym (nameGetStr t.ident) in 
        let langEnv = _langEnvEmpty ident in 

        let isSynDecl = lam d. match d with DeclSyn _ then true else false in 
        let synDecls = filter isSynDecl t.decls in 

        let isSemDecl = lam d. match d with DeclSem _ then true else false in 
        let semDecls = filter isSemDecl t.decls in 

        let isTypeDecl = lam d. match d with DeclType _ then true else false in 
        let typeDecls = filter isTypeDecl t.decls in 

        let symbIncludes = lam langEnvs : [LangEnv]. lam n : Name. 
            match mapLookup (nameGetStr n) env.langEnv with Some langEnv then 
                ((cons langEnv langEnvs), langEnv.ident)
            else 
                symLookupError 
                    {kind = "language", info = [t.info], allowFree = false}
                    t.ident
        in
        match mapAccumL symbIncludes [] t.includes with (includedLangEnvs, includes) in 

        let includedSyns = combineMaps (map (lam env. env.syns) includedLangEnvs) in 
        let includedSems = combineMaps (map (lam env. env.sems) includedLangEnvs) in 

        let accIncludedTypes : Map String Decl -> LangEnv -> Map String Decl = lam acc. lam env. 
            if mapDisjoint env.includedTypes env.definedTypes then
                mapUnion acc (mapUnion env.includedTypes env.definedTypes)
            else
                error (join [
                    "Illegal state during symbolization! ",
                    "The langauge '",
                    nameGetStr env.ident,
                    "' includes and defines a type with the same name!"
                ])
        in
        let includedTypes = foldl accIncludedTypes (mapEmpty cmpString) includedLangEnvs in 

        -- 1. Symbolize ident and params of SynDecls in this langauge
        let symSynIdentParams = lam langEnv : LangEnv. lam synDecl.
            match synDecl with DeclSyn s in
            let ident = nameSym (nameGetStr s.ident) in 

            -- Throw an error if DeclType is included with the same identifier
            (match mapLookup (nameGetStr s.ident) includedTypes with Some decl then
                match decl with DeclType t in 
                errorMulti 
                    [(s.info, ""), (t.info, "")] 
                    (join [
                        "A name conflict was found during symbolization in language '",
                        langStr,
                        "' for the name '",
                        nameGetStr t.ident,
                        "'!"
                    ])
            else ()) ;

            (match mapLookup (nameGetStr ident) langEnv.syns with Some synDecl then
                match synDecl with DeclSyn decl in 
                errorMulti 
                    [(s.info, ""), (decl.info, "")] 
                    (join [
                        "A name conflict was found during symbolization in language '",
                        langStr,
                        "' for the name '",
                        nameGetStr ident,
                        "'!"
                    ])
                else ()) ;

            let env : SymEnv = convertNameEnv (convertLangEnv langEnv) in 
            match mapAccumL setSymbol env.currentEnv.tyVarEnv s.params with (_, params) in
            let included : [Decl] = match mapLookup (nameGetStr ident) includedSyns 
                                    with Some xs then xs else [] in  

            let includes = join
                (map (lam d. match d with DeclSyn s in s.defs) included) in

            let synn = DeclSyn {s with params = params,
                                       ident = ident,
                                       includes = includes} in 

            let langEnv = {langEnv with 
                syns = mapInsert (nameGetStr ident) synn langEnv.syns} in

            (langEnv, synn)
        in
        match mapAccumL symSynIdentParams langEnv synDecls with (langEnv, synDecls) in 

        -- 1.5 Merge syns from included languages that have not explicitly
        -- been extending by this langauge fragment. 
        let isDeclaredInLang : all a. (String -> a -> Bool) = lam s. lam v.
            let hasStringIdent = lam decl. 
                match decl with DeclSyn d in 
                if eqString (nameGetStr d.ident) s then true else false
            in
            match find hasStringIdent synDecls with Some _ then false else true
        in 
        let includedSyns = mapFilterWithKey isDeclaredInLang includedSyns in 
        let includedSynsPairs = mapToSeq includedSyns in 

        let symbPairs : LangEnv -> (String, [Decl]) -> (LangEnv, Decl) = lam langEnv. lam pair. 
            match pair with (ident, includedSyns) in 
            let ident = nameSym ident in 

            let includes = join (map 
                (lam d. match d with DeclSyn s in s.defs) includedSyns) in 

            let decl = DeclSyn {ident = ident,
                                params = [],
                                defs = [],
                                includes = includes,
                                info = NoInfo ()} in
        
            let langEnv = {langEnv with 
                syns = mapInsert (nameGetStr ident) decl langEnv.syns} in

            (langEnv, decl)
        in

        match mapAccumL symbPairs langEnv includedSynsPairs with (langEnv, includedSyns) in
        let synDecls = concat synDecls includedSyns in

        -- 2. Symbolize DeclType and params
        let symbDeclType = lam langEnv : LangEnv. lam typeDecl. 
            match typeDecl with DeclType t in 
            let ident = nameSym (nameGetStr t.ident) in 

            -- Throw an error if DeclType is included with the same identifier
            (match mapLookup (nameGetStr ident) includedTypes with Some decl then
                match decl with DeclType declType in 
                errorMulti 
                    [(t.info, ""), (declType.info, "")] 
                    (join [
                        "A name conflict was found during symbolization in language '",
                        langStr,
                        "' for the name '",
                        nameGetStr ident,
                        "'!"
                    ])
            else ()) ;

            -- Throw an error if a DeclSyn is  or defined with the same identifier
            (match mapLookup (nameGetStr ident) langEnv.syns with Some synDecl then
                match synDecl with DeclSyn decl in 
                errorMulti 
                    [(t.info, ""), (decl.info, "")] 
                    (join [
                        "A name conflict was found during symbolization in language '",
                        langStr,
                        "' for the name '",
                        nameGetStr ident,
                        "'!"
                    ])
                else ());

            let env = convertNameEnv (convertLangEnv langEnv) in 
            match mapAccumL setSymbol env.currentEnv.tyVarEnv t.params with (_, params) in

            let decl = DeclType {t with ident = ident,
                                        params = params} in 

            let langEnv = {langEnv with 
                definedTypes = mapInsert (nameGetStr ident) decl langEnv.definedTypes} in

            (langEnv, decl)
        in 
        match mapAccumL symbDeclType langEnv typeDecls with (langEnv, typeDecls) in 

        -- 3. Symbolize syntax constructors (add defs to conEnv)
        let symbDef = lam langEnv : LangEnv. lam def : {ident : Name, tyIdent : Type}. 
            let ident = nameSym (nameGetStr ident) in

            let env = convertNameEnv (convertLangEnv langEnv) in 
            let tyIdent = symbolizeType env def.tyIdent in

            (langEnv, {ident = ident, tyIdent = tyIdent})
        in
        let symbSynConstructors = lam langEnv. lam synDecl. 
            match synDecl with DeclSyn s in 
            match mapAccumL symbDef langEnv s.defs with (langEnv, defs) in 
            let decl = DeclSyn {s with defs = defs} in
            let langEnv = {langEnv with 
                syns = mapInsert (nameGetStr s.ident) decl langEnv.syns} in
            (langEnv, decl)
        in 
        match mapAccumL symbSynConstructors langEnv synDecls with (langEnv, synDecls) in 

        -- 4. Assign names to semantic functions
        let symbSem = lam langEnv : LangEnv. lam declSem. 
            match declSem with DeclSem s in 

            let ident = nameSym (nameGetStr s.ident) in 

            let env = convertNameEnv (convertLangEnv langEnv) in

            let tyAnnot = symbolizeType env s.tyAnnot in 
            let tyBody = symbolizeType env s.tyBody in 

            let includedSems = match mapLookup (nameGetStr s.ident) includedSems 
                               with Some xs then xs else [] in 
            
            let includedCases = join (map 
                (lam decl. match decl with DeclSem s in s.cases)
                includedSems) in

            let decl = DeclSem {s with ident = ident,
                                tyAnnot = tyAnnot,
                                tyBody = tyBody,
                                includes = includedCases} in 

            let langEnv = {langEnv with 
                sems = mapInsert (nameGetStr s.ident) decl langEnv.sems} in

            (langEnv, decl)
        in 
        match mapAccumL symbSem langEnv semDecls with (langEnv, semDecls) in 

        -- 5. Assign names to semantic bodies.
        -- TODO: We must resymbolize the included cases as any recursive calls
        -- now need to point to the new symbols.
        let symbSem2 = lam langEnv : LangEnv. lam declSem. 
            match declSem with DeclSem s in 

            let env = convertNameEnv (convertLangEnv langEnv) in
            
            let symbArg = lam env : SymEnv. lam arg : {ident : Name, tyAnnot : Type}. 
                match setSymbol env.currentEnv.varEnv arg.ident with (varEnv, ident) in 
                let env = updateVarEnv env varEnv in 
                let tyAnnot = symbolizeType env arg.tyAnnot in 
                (env, {ident = ident, tyAnnot = tyAnnot})
            in
            
            match mapAccumL symbArg env s.args with (env, args) in 

            let symbCases = lam cas : {pat : Pat, thn : Expr}. 
                match symbolizePat env (mapEmpty cmpString) cas.pat with (thnVarEnv, pat) in
                let thn = symbolizeExpr (updateVarEnv env thnVarEnv) cas.thn in
                {pat = pat, thn = thn}
            in

            let cases = map symbCases s.cases in

            let decl = DeclSem {s with args = args,
                                cases = cases} in 

            let langEnv = {langEnv with 
                sems = mapInsert (nameGetStr s.ident) decl langEnv.sems} in

            (langEnv, decl)
        in
        match mapAccumL symbSem2 langEnv semDecls with (langEnv, semDecls) in 

        let env = {env with langEnv = mapInsert (nameGetStr t.ident) langEnv env.langEnv} in 
        let t = {t with decls = join [typeDecls, synDecls, semDecls],
                        includes = includes,
                        ident = ident} in

        (env, DeclLang t)
end

-- let _and = lam cond. lam f. lam. if cond () then f () else false
-- let _andFold = lam f. lam acc. lam e. _and acc (f e)

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
        let argIdents = map (lam a. a.ident) l.args in 
        let argTys = map (lam a. a.tyAnnot) l.args in 
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
    | DeclType l -> 
        _and (lam. nameHasSym l.ident) (_and 
             (lam. (forAll nameHasSym l.params))
             (isFullySymbolizedType l.tyIdent))
        
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
match symbolizeMLang symEnvDefault p with (_, p) in 
let l1 = head p.decls in 
match l1 with DeclLang l in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolized p.expr with true in 
utest nameHasSym l.ident with true in

let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [
            decl_syn_ "Foo" [("Baz", tyint_), ("BazBaz", tychar_)],
            decl_type_ "Bar" [] tyint_,
            decl_sem_ "f" [] []
        ],
        decl_langi_ "L2" ["L1"] [
            -- decl_type_ "Foo" [] tychar_,
            decl_syn_ "Foo" [],
            decl_sem_ "f" [] []
        ]
    ],
    expr = bind_ (use_ "L2") (var_ "f")
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
let l1 = head p.decls in 
let l2 = head (tail p.decls) in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolizedDecl l2 () with true in 
match l2 with DeclLang ld in 
match head (tail ld.decls) with DeclSem f in 
utest length f.includes with 0 in 
utest isFullySymbolized p.expr with true in 
match head ld.decls with DeclSyn foo in 
utest length foo.includes with 2 in

let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [
            decl_syn_ "Foo" [("Baz", tyint_)]
        ],
        decl_lang_ "L2" [
            -- decl_type_ "Foo" [] tychar_,
            decl_syn_ "Foo" [("BazBaz", tychar_)]
        ],
        decl_langi_ "L12" ["L1", "L2"] []
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
let l1 = head p.decls in 
let l2 = get p.decls 1 in 
let l12 = get p.decls 2 in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolizedDecl l2 () with true in 
utest isFullySymbolizedDecl l12 () with true in

match l12 with DeclLang l in
utest length l.decls with 1 in 

let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [
            decl_syn_ "Foo" []
        ],
        decl_langi_ "L2" ["L1"] []
    ],
    expr = uunit_
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
let l1 = head p.decls in 
match l1 with DeclLang l in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolized p.expr with true in 
utest nameHasSym l.ident with true in
let l2 = head (tail p.decls) in 
match l2 with DeclLang l in 
utest isFullySymbolizedDecl l2 () with true in
utest length l.decls with 1 in 

let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [

        ],
        decl_langi_ "L2" ["L1"] [
            decl_syn_ "Foo" [],
            decl_syn_ "Foo" []
        ]
    ],
    expr = uunit_
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 


()