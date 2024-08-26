-- Establishes an inclusion relationship between the declarations of semantic 
-- functions and syntax fragments.
--
-- The first purpose of this transformation is is to find any included syn or sem
-- declarations when we have an explicit declaration. In the program below, 
-- this transformation will establish the fact that L1.f and L2.f both 
-- include L0.f and that L12.f includes both L1.f and L2.f. 
-- ```
-- lang L0 = 
--   sem f = ...
-- end
-- lang L1 = L0
--   sem f = ...
-- end
-- lang L2 = L0
--   sem f = ...
-- end
-- lang L12 = L1 + L2 
--   sem f = ...
-- end
-- ```
-- 
-- The second purpose of this transformation is to create explicit declarations
-- for semantic functions and syntax fragements that are implicitly extended 
-- through language composition. In the program below, this transformation
-- will generate a semantic function declaration called L12.f that includes 
-- L1.f and L2.f.
-- lang L0 = 
--   sem f = ...
-- end
-- lang L1 = L0
--   sem f = ...
-- end
-- lang L2 = L0
--   sem f = ...
-- end
-- lang L12 = L1 + L2 
-- end
-- ```

include "ast.mc"
include "ast-builder.mc"

include "mexpr/info.mc"

-- include "set.mc"
include "bool.mc"
include "common.mc"
include "error.mc"
include "tuple.mc"
include "name.mc"
include "seq.mc"
include "map.mc"

-- This info type contains a subset of the data in a DeclSem, DeclSyn, or DeclType.\
-- Specifically, they contain the data required for the creation of explicit
-- declarations for implicitly included syns and sems. We create a special
-- DeclInfo type for this so that we do not have to carry around the constructors
-- and cases.
type DeclInfo
con TypeInfo : use MLangAst in {ident : Name,
                                orig : String,
                                info : Info} -> DeclInfo
con SemInfo : use MLangAst in {ident : Name,
                               info : Info,
                               orig : String,
                               ty : Type,
                               args : Option [{ident : Name, tyAnnot: Type}]} -> DeclInfo
con SynInfo : use MLangAst in {ident : Name,
                               info : Info,
                               orig : String,
                               params : [Name]} -> DeclInfo

let decl2info = lam orig. lam d.
  use MLangAst in 
  switch d
    case DeclSem s then SemInfo {ident = s.ident,
                                 info = s.info,
                                 orig = orig,
                                 ty = s.tyAnnot,
                                 args = s.args}
    case DeclSyn s then SynInfo {ident = s.ident,
                                 info = s.info,
                                 orig = orig,
                                 params = s.params}
    case DeclType t then TypeInfo {ident = t.ident,
                                   orig = orig,
                                   info = t.info}     
  end                     

let isTypeInfo = lam i. match i with TypeInfo _ then true else false
let isSemInfo = lam i. match i with SemInfo _ then true else false
let isSynInfo = lam i. match i with SynInfo _ then true else false

let extractInfoName : DeclInfo -> (Info, String) = lam info.
  switch info 
    case TypeInfo t then (t.info, nameGetStr t.ident)
    case SemInfo s then (s.info, nameGetStr s.ident)
    case SynInfo s then (s.info, nameGetStr s.ident)
  end

let projIdent = lam info. 
  switch info 
    case TypeInfo t then (t.orig, nameGetStr t.ident)
    case SemInfo t then (t.orig, nameGetStr t.ident)
    case SynInfo t then (t.orig, nameGetStr t.ident)
  end

type ComposerContext = {
  langMap : Map (String, String) DeclInfo
}

let emptyComposerContext : ComposerContext = {
  langMap = mapEmpty (tupleCmp2 cmpString cmpString)
}  

let ctxWithDeclInfo = lam ctx. lam s. lam declInfo.
  {ctx with langMap = mapInsert s declInfo ctx.langMap}

lang LanguageComposer = MLangAst
  sem composeProgram : MLangProgram -> MLangProgram 
  sem composeProgram =| p ->
    let ctx = emptyComposerContext in 
    match mapAccumL composeLang ctx p.decls with (_, decls) in 
    {p with decls = decls}

  sem composeLang : ComposerContext -> Decl -> (ComposerContext, Decl)
  sem composeLang ctx =
  | DeclLang l -> 
    let includes = map nameGetStr l.includes in 
    match mapAccumL (handleDecl (nameGetStr l.ident) includes) ctx l.decls with (ctx, decls) in 

    let synOrSemNames = mapOption 
      (lam d. match d with DeclSem {ident = ident} then Some ident 
              else match d with DeclSyn {ident = ident} then Some ident
              else None ()) decls in 
    let synOrSemStrings = map nameGetStr synOrSemNames in 

    match addImplicitIncludes (nameGetStr l.ident) includes synOrSemStrings ctx 
    with (ctx, generatedDecls) in 

    (ctx, DeclLang {l with decls = concat decls generatedDecls})
  | other -> (ctx, other)

  sem handleDecl : String -> [String] -> ComposerContext -> Decl -> (ComposerContext, Decl)
  sem handleDecl langStr includes ctx = 
  | decl & DeclSem d ->
    let identStr = nameGetStr d.ident in 
    let findMatchingInfo : String -> Option DeclInfo = lam incl.
      mapLookup (incl, identStr) ctx.langMap in 
    let foundIncludes : [DeclInfo] = mapOption findMatchingInfo includes in 
    
    let conflicts = filter (lam i. or (isTypeInfo i) (isSynInfo i)) foundIncludes in 
    let errors = cons (d.info, nameGetStr d.ident) (map extractInfoName conflicts) in 

    if not (null conflicts) then
      errorMulti errors "The declared sem has an identifier that conflicts with included types!"
    else
      let includedSems = filter isSemInfo foundIncludes in 

      let includes = map projIdent includedSems in 
      (ctxWithDeclInfo ctx (langStr, nameGetStr d.ident) (decl2info langStr decl), 
       DeclSem {d with includes = includes})
  | decl & DeclSyn d ->
    let identStr = nameGetStr d.ident in 
    let findMatchingInfo : String -> Option DeclInfo = lam incl.
      mapLookup (incl, identStr) ctx.langMap in 
    let foundIncludes : [DeclInfo] = mapOption findMatchingInfo includes in 
    
    let conflicts = filter isTypeInfo foundIncludes in 

    let errors = cons (d.info, nameGetStr d.ident) (map extractInfoName conflicts) in 

    if not (null conflicts) then
      errorMulti errors "The declared syn has an identifier that conflicts with included types!"
    else
      let includedSyns = filter isSynInfo foundIncludes in 

      let includes = map projIdent includedSyns in 
      let info = {ident = d.ident, info = d.info} in 
      (ctxWithDeclInfo ctx (langStr, nameGetStr d.ident) (decl2info langStr decl), 
       DeclSyn {d with includes = includes})
  | decl & DeclType d -> 
    let identStr = nameGetStr d.ident in 
    let findMatchingInfo : String -> Option DeclInfo = lam incl.
      mapLookup (incl, identStr) ctx.langMap in 
    let conflicts : [DeclInfo] = mapOption findMatchingInfo includes in 

    let errors = cons (d.info, nameGetStr d.ident) (map extractInfoName conflicts) in 

    if not (null conflicts) then
      errorMulti errors "The declared type has an identifier that conflicts with included types or syns!"
    else
      let info = decl2info langStr decl in 
      (ctxWithDeclInfo ctx (langStr, nameGetStr d.ident) info, decl)
  | _ -> error "Only Type, Syn, and Sem declarations can be contained inside of a langauge!"

  sem addImplicitIncludes langStr includes definedSynsSems =
  | ctx ->
    let includeSet = setOfSeq cmpString includes in 

    -- We are going to include elements from ctx.langMap that
    -- (1) that are not Type declarations.
    -- (2) belong to an included langauge
    -- (3) that have not already been included explicitly through a syn or sem
    let pred = lam k. lam v. 
      match k with (origLang, ident) in 
        (and (not (isTypeInfo v))
             (and (setMem origLang includeSet)
                  (not (seqMem eqString definedSynsSems ident))))
    in       
    let filteredCtx = mapFilterWithKey pred ctx.langMap in 

    -- Group the filtered element by the identifiers and put the results in the
    -- toBeGenerated map
    let f = lam acc. lam pair. 
      match pair with ((origLang, ident), info) in 
      let l = mapLookupOrElse (lam. []) ident acc in 
      mapInsert ident (cons ((origLang, ident), info) l) acc
    in 
    let toBeGenerated = foldl f (mapEmpty cmpString) (mapToSeq filteredCtx) in 

    -- Iterate over the the toBeGenerated map and add the newly generated
    -- sem or syn to the context and list of decls.
    let gen = lam ctx. lam pairs : [((String, String), DeclInfo)].
      let includes = map (lam p. match p with ((orig, ident), _) in (orig, ident)) pairs in 


      let pair = head pairs in 
      match pair with ((origLang, ident), info) in

      switch info 
        case SynInfo s then 
          let decl = DeclSyn {ident = s.ident,
                              params = s.params,
                              defs = [],
                              includes = includes,
                              info = s.info} in 
          let info = decl2info langStr decl in 
          (ctxWithDeclInfo ctx (langStr, nameGetStr s.ident) info, decl)
        case SemInfo s then
          let include2args = lam incl.
            match mapLookup incl ctx.langMap with Some info in 
            match info with SemInfo semInfo in
            semInfo.args
          in 
          let args = mapOption include2args includes in 
          let args = if null args then None () else Some (head args) in 
          let decl = DeclSem {ident = s.ident,
                              tyAnnot = s.ty,
                              tyBody = tyunknown_,
                              args = args,
                              cases = [],
                              includes = includes,
                              info = s.info} in 
          let info = decl2info langStr decl in 
          (ctxWithDeclInfo ctx (langStr, nameGetStr s.ident) info, decl)
        case _ then never
      end 
    in 
    mapAccumL gen ctx (mapValues toBeGenerated)


end

mexpr 
use MLangAst in
use LanguageComposer in 

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L1" ["L0"] [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L2" ["L0"] [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L12" ["L1", "L2"] [
      decl_sem_ "f" [] []
    ]
  ],
  expr = uunit_
} in 
let p = composeProgram p in 
match get p.decls 0 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f0 in 
utest length f0.includes with 0 in 

match get p.decls 1 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f1 in 
utest length f1.includes with 1 in 

match get p.decls 2 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f2 in 
utest length f2.includes with 1 in 

match get p.decls 3 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f12 in 
utest length f12.includes with 2 in 

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_syn_ "S" []
    ],
    decl_langi_ "L1" ["L0"] [
      decl_syn_ "S" []
    ],
    decl_langi_ "L2" ["L0"] [
      decl_syn_ "S" []
    ],
    decl_langi_ "L12" ["L1", "L2"] [
      decl_syn_ "S" []
    ]
  ],
  expr = uunit_
} in 
let p = composeProgram p in 
match get p.decls 0 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f0 in 
utest length f0.includes with 0 in 

match get p.decls 1 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f1 in 
utest length f1.includes with 1 in 

match get p.decls 2 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f2 in 
utest length f2.includes with 1 in 

match get p.decls 3 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f12 in 
utest length f12.includes with 2 in 

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L1" ["L0"] [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L2" ["L0"] [
      decl_sem_ "f" [] []
    ],
    decl_langi_ "L12" ["L1", "L2"] []
  ],
  expr = uunit_
} in 
let p = composeProgram p in 
match get p.decls 0 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f0 in 
utest length f0.includes with 0 in 

match get p.decls 1 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f1 in 
utest length f1.includes with 1 in 

match get p.decls 2 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f2 in 
utest length f2.includes with 1 in 

match get p.decls 3 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSem f12 in 
utest length f12.includes with 2 in 
utest nameGetStr f12.ident with "f" in 

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_syn_ "S" []
    ],
    decl_langi_ "L1" ["L0"] [
      decl_syn_ "S" []
    ],
    decl_langi_ "L2" ["L0"] [
      decl_syn_ "S" []
    ],
    decl_langi_ "L12" ["L1", "L2"] []
  ],
  expr = uunit_
} in 
let p = composeProgram p in 
match get p.decls 0 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f0 in 
utest length f0.includes with 0 in 

match get p.decls 1 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f1 in 
utest length f1.includes with 1 in 

match get p.decls 2 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f2 in 
utest length f2.includes with 1 in 

match get p.decls 3 with DeclLang {decls = innerDecls} in 
match head innerDecls with DeclSyn f12 in 
utest length f12.includes with 2 in 
utest nameGetStr f12.ident with "S" in 

()




