include "./ast.mc"
include "./ast-builder.mc"
include "./pprint.mc"
include "./symbolize.mc"

include "common.mc"
include "name.mc"
include "set.mc"
include "result.mc"

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
    (switch (foldl accumSynBase (Right (mapEmpty nameCmp)) prog.decls)
     case Left _ then (error "Language composition error: included syns do not share base!")
     case Right _ then (printLn "Valid base for all syns and sems!")
     end) ;

    []

  sem accumSynBase : Either CompositionError (Map Name Name) -> Decl -> Either CompositionError (Map Name Name)
  sem accumSynBase env = 
  | decl -> 
    match env with Left err then env
    else switch decl
      case DeclLang l then foldl accumSynBase env l.decls
      case DeclSyn s then
        match env with Right m in 
        match s.includes with [] then 
          Right (mapInsert s.ident s.ident m)
        else 
          let includeList = map 
            (lam incl. match mapLookup incl m with Some b in b) 
            s.includes in 
          let includeSet = setOfSeq nameCmp includeList in 

          if eqi 1 (setSize includeSet) then
            Right (mapInsert s.ident (head includeList) m)
          else
            Left (DifferentBaseSyn {})
      case DeclSem s then
        match env with Right m in 
        match s.includes with [] then 
          Right (mapInsert s.ident s.ident m)
        else 
          let includeList = map 
            (lam incl. match mapLookup incl m with Some b in b) 
            s.includes in 
          let includeSet = setOfSeq nameCmp includeList in 

          if eqi 1 (setSize includeSet) then
            Right (mapInsert s.ident (head includeList) m)
          else
            Left (DifferentBaseSem {})
      case _ then env
      end
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
            decl_syn_ "Foo" [],
            decl_sem_ "f" [] []
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