include "./ast.mc"
include "./ast-builder.mc"
include "./pprint.mc"
include "./symbolize.mc"

include "common.mc"
include "name.mc"
include "set.mc"
include "result.mc"

type CompositionCheckEnv = {
  baseMap : Map Name Name
}

let _emptyCompositionCheckEnv = {
  baseMap = mapEmpty nameCmp
}

let insertBaseMap : CompositionCheckEnv -> Name -> Name -> CompositionCheckEnv = 
  lam env. lam k. lam v. 
    {env with baseMap = mapInsert k v env.baseMap}

lang MLangCompositionCheck = MLangAst
  syn CompositionError =
  | DifferentBaseSyn {}
  | DifferentBaseSem {}
  | MismatchedSemParams {}
  | MismatchedSynParams {}
  | InvalidSemPatterns {}

  syn CompositionWarning = 

  sem checkComposition : MLangProgram -> [CompositionError] 
  sem checkComposition =
  | prog -> 
    let result : Result CompositionWarning CompositionError CompositionCheckEnv
    = _foldl accumSynBase _emptyCompositionCheckEnv prog.decls in 
    match _consume result with (_, errOrResult) in 
    (switch errOrResult 
     case Left _ then error "Error during composition check!"
     case Right _ then printLn "Valid composition!"
     end) ;
    []

  sem accumSynBase : CompositionCheckEnv -> 
                     Decl -> 
                     Result CompositionWarning CompositionError CompositionCheckEnv
  sem accumSynBase env =
  | DeclLang l ->
   _foldl accumSynBase env l.decls
  | DeclSyn s -> 
    match s.includes with [] then 
      _ok (insertBaseMap env s.ident s.ident)
    else 
      let includeList = map 
        (lam incl. match mapLookup incl env.baseMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq nameCmp includeList in 

      if eqi 1 (setSize includeSet) then
        _ok (insertBaseMap env s.ident (head includeList))
      else
        _err (DifferentBaseSyn {})
  | DeclSem s ->
    match s.includes with [] then 
      _ok (insertBaseMap env s.ident s.ident)
    else 
      let includeList = map 
        (lam incl. match mapLookup incl env.baseMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq nameCmp includeList in 

      if eqi 1 (setSize includeSet) then
        _ok (insertBaseMap env s.ident (head includeList))
      else
        _err (DifferentBaseSem {})
end

lang TestLang = MLangSym + MLangCompositionCheck end

mexpr 
use TestLang in 
-- let p : MLangProgram = {
--     decls = [
--         decl_lang_ "L1" [
--             decl_syn_ "Foo" [("Baz", tyint_)]
--         ],
--         decl_lang_ "L2" [
--             -- decl_type_ "Foo" [] tychar_,
--             decl_syn_ "Foo" [("BazBaz", tychar_)]
--         ],
--         decl_langi_ "L12" ["L1", "L2"] []
--     ],
--     expr = bind_ (use_ "L2") (int_ 10)
-- } in 

-- let p : MLangProgram = {
--     decls = [
--         decl_lang_ "L0" [
--             decl_syn_ "Foo" []
--         ],
--         decl_langi_ "L1" ["L0"] [
--             decl_syn_ "Foo" [("Baz", tyint_)]
--         ],
--         decl_langi_ "L2" ["L0"] [
--             decl_syn_ "Foo" [("BazBaz", tychar_)]
--         ],
--         decl_langi_ "L12" ["L0", "L1", "L2"] []
--     ],
--     expr = bind_ (use_ "L2") (int_ 10)
-- } in 

let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            -- decl_syn_ "Foo" []
            -- decl_sem_ "f" [] []
        ],
        decl_langi_ "L1" ["L0"] [
            decl_syn_ "Foo" [("Baz", tyint_)],
            decl_sem_ "f" [] []
        ],
        decl_langi_ "L2" ["L0"] [
            decl_syn_ "Foo" [("BazBaz", tychar_)],
            decl_sem_ "f" [] []
        ],
        decl_langi_ "L12" ["L0", "L1", "L2"] [
          decl_sem_ "f" [] []
        ]        
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
checkComposition p ;
utest nameCmp (nameSym "s1") (nameSym "s2") with 0 using neqi in 
()