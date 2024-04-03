include "./ast.mc"
include "./ast-builder.mc"
include "./pprint.mc"
include "./symbolize.mc"

include "common.mc"
include "name.mc"
include "set.mc"
include "result.mc"

type CompositionCheckEnv = {
  -- Mapping from the symbolized name of a syn or sem to their base declaration
  baseMap : Map Name Name,
  -- Mapping from symbolized name of a syn or sem to the amount of parameters
  paramMap : Map Name Int 
}

let _emptyCompositionCheckEnv = {
  baseMap = mapEmpty nameCmp,
  paramMap = mapEmpty nameCmp
}

let insertBaseMap : CompositionCheckEnv -> Name -> Name -> CompositionCheckEnv = 
  lam env. lam k. lam v. 
    {env with baseMap = mapInsert k v env.baseMap}
    
let insertParamMap : CompositionCheckEnv -> Name -> Int -> CompositionCheckEnv = 
  lam env. lam k. lam v. 
    {env with paramMap = mapInsert k v env.paramMap}

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
    = _foldl parseAll _emptyCompositionCheckEnv prog.decls in 
    match _consume result with (_, errOrResult) in 
    (switch errOrResult 
     case Right _ then printLn "Valid language composition!" 
     case Left err then
      (switch head err 
       case DifferentBaseSyn _ then error "Different base syn!"
       case DifferentBaseSem _ then error "Different base sem!"
       case MismatchedSynParams _ then error "Mismatched syn parameters!"
       case MismatchedSemParams _ then error "Mismatched sem parameters!"
       case InvalidSemPatterns _ then error "Invalid sem patterns!"
       end)
     end) ;
    []

  sem parseAll : CompositionCheckEnv -> 
                 Decl -> 
                 Result CompositionWarning CompositionError CompositionCheckEnv
  sem parseAll env = 
  | DeclLang l -> 
    _foldl parseAll env l.decls
  | DeclSem s & d ->
    _foldlfun env d [parseParams, parseBase]
  | DeclSyn s & d ->
    _foldlfun env d [parseParams, parseBase]

  sem parseParams : CompositionCheckEnv -> 
                    Decl -> 
                    Result CompositionWarning CompositionError CompositionCheckEnv
  sem parseParams env = 
  | DeclSyn s -> 
    let paramNum = length s.params in 

    match s.includes with [] then 
      _ok (insertParamMap env s.ident paramNum)
    else 
      let paramNum = length s.params in 

      let includeList = map 
        (lam incl. match mapLookup incl env.paramMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq subi includeList in 
      let includeSet = setInsert paramNum includeSet in 

      if eqi 1 (setSize includeSet) then
        _ok (insertParamMap env s.ident paramNum)
      else
        _err (MismatchedSynParams {})
  | DeclSem s ->
    let paramNum = length s.args in 

    match s.includes with [] then 
      _ok (insertParamMap env s.ident paramNum)
    else 
      let includeList = map 
        (lam incl. match mapLookup incl env.paramMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq subi includeList in 
      let includeSet = setInsert paramNum includeSet in 

      if eqi 1 (setSize includeSet) then
        _ok (insertParamMap env s.ident paramNum)
      else
        _err (MismatchedSemParams {})

  sem parseBase : CompositionCheckEnv -> 
                  Decl -> 
                  Result CompositionWarning CompositionError CompositionCheckEnv
  sem parseBase env =
  -- | DeclLang l ->
  --  _foldl parseBase env l.decls
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
          decl_sem_ "f" [("x", tyint_)] []
        ]        
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
checkComposition p ;
utest nameCmp (nameSym "s1") (nameSym "s2") with 0 using neqi in 
()