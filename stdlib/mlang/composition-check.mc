include "./ast.mc"
include "./ast-builder.mc"
include "./pprint.mc"
include "./symbolize.mc"

include "mexpr/pattern-analysis.mc"
include "mexpr/ast-builder.mc"

include "common.mc"
include "bool.mc"
include "name.mc"
include "set.mc"
include "result.mc"
include "digraph.mc"

type CompositionCheckEnv = {
  nextId : Int,
  -- Mapping from the symbolized name of a syn or sem to their base declaration
  baseMap : Map Name Name,
  -- Mapping from symbolized name of a syn or sem to the amount of parameters
  paramMap : Map Name Int,
  -- Mapping from symbolized names of a sem to its cases that are ordered by
  -- the subset relation on the patterns. 
  -- We also introduce a unique id for each case. We need this id to be able 
  -- to remove duplicate cases under languaage composition.
  semPatMap : Map Name [use MLangAst in {pat: Pat, thn : Expr, id : Int}] 
}

let collectPats : CompositionCheckEnv -> [Name] -> [use MLangAst in {pat: Pat, thn : Expr, id : Int}]
  = lam env. lam includes.
  let incl2pats = lam i : Name. 
    match mapLookup i env.semPatMap with Some pats then
      pats
    else error (concat 
      "Illegal state during composition-check! The name patterns for each "
      "included sem should have already been included!")
  in 
  join (map incl2pats includes)

let carthesianProduct : all a. all b. [a] -> [b] -> [(a, b)] = lam xs. lam ys.
  let work1 : a -> [b] -> [(a, b)] = lam x. lam ys. 
    map (lam y. (x, y)) ys
  in 
  join (map (lam x. work1 x ys) xs)

let indexPairs : Int -> [(Int, Int)] = lam n. 
  let indices = range 0 n 1 in 
  let pairs = carthesianProduct indices indices in
  let pred = lam p. match p with (x, y) in and (neqi x y) (gti x y) in 
  filter pred pairs 

let _emptyCompositionCheckEnv = {
  nextId = 0,
  baseMap = mapEmpty nameCmp,
  paramMap = mapEmpty nameCmp,
  semPatMap = mapEmpty nameCmp
}

let insertBaseMap : CompositionCheckEnv -> Name -> Name -> CompositionCheckEnv = 
  lam env. lam k. lam v. 
    {env with baseMap = mapInsert k v env.baseMap}
    
let insertParamMap : CompositionCheckEnv -> Name -> Int -> CompositionCheckEnv = 
  lam env. lam k. lam v. 
    {env with paramMap = mapInsert k v env.paramMap}

let insertSemPatMap = lam env. lam k. lam v.
  {env with semPatMap = mapInsert k v env.semPatMap}

lang MLangCompositionCheck = MLangAst + MExprPatAnalysis + MExprAst + MExprPrettyPrint
  syn CompositionError =
  | DifferentBaseSyn {
    synIdent : Name,
    info : Info 
  }
  | DifferentBaseSem {
    semIdent : Name,
    info : Info
  }
  | MismatchedSemParams {
    semIdent : Name,
    info : Info
  }
  | MismatchedSynParams {
    synIdent : Name,
    info : Info
  }
  | InvalidSemPatterns {
    semIdent : Name,
    info : Info
  }

  syn CompositionWarning = 

  sem raiseError : CompositionError -> ()
  sem raiseError = 
  | DifferentBaseSyn e -> 
    let msg = join [
      "Invalid language composition because the syn '",
      nameGetStr e.synIdent,
      "' includes syns with different bases!"
    ] in 
    errorMulti [(e.info, "")] msg
  | DifferentBaseSem e -> 
    let msg = join [
      "Invalid language composition because the semantic function '",
      nameGetStr e.semIdent,
      "' includes semantic functions with different bases!"
    ] in 
    errorMulti [(e.info, "")] msg
  | MismatchedSemParams e -> 
    let msg = join [
      "Invalid language composition because the semantic function '",
      nameGetStr e.semIdent,
      "' includes semantic functions with different number of parameters!"
    ] in 
    errorMulti [(e.info, "")] msg
  | MismatchedSynParams e ->     
    let msg = join [
      "Invalid language composition because the syn '",
      nameGetStr e.synIdent,
      "' includes syns with different number of parameters!"
    ] in 
    errorMulti [(e.info, "")] msg
  | InvalidSemPatterns e ->     
    let msg = join [
      "Invalid language composition because the semantic function '",
      nameGetStr e.semIdent,
      "' includes or defined patterns which are overlapping or equal!"
    ] in 
    errorMulti [(e.info, "")] msg

  sem checkComposition : MLangProgram -> Result CompositionWarning CompositionError CompositionCheckEnv
  sem checkComposition =| prog -> 
    _foldl parseAll _emptyCompositionCheckEnv prog.decls 

  sem parseAll : CompositionCheckEnv -> 
                 Decl -> 
                 Result CompositionWarning CompositionError CompositionCheckEnv
  sem parseAll env = 
  | DeclLang l -> 
    _foldl parseAll env l.decls
  | DeclSem s & d ->
    _foldlfun env d [parseParams, parseBase, parseCases]
  | DeclSyn s & d ->
    _foldlfun env d [parseParams, parseBase]
  | other -> _ok env

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
        _err (MismatchedSynParams {
          synIdent = s.ident,
          info = s.info
        })
  | DeclSem s ->
    let paramNum = countParams (DeclSem s) in 

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
        _err (MismatchedSemParams {
          semIdent = s.ident,
          info = s.info
        })

  sem parseBase : CompositionCheckEnv -> 
                  Decl -> 
                  Result CompositionWarning CompositionError CompositionCheckEnv
  sem parseBase env =
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
        _err (DifferentBaseSyn {
          synIdent = s.ident,
          info = s.info
        })
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
        _err (DifferentBaseSem {
          semIdent = s.ident, 
          info = s.info
        })

  sem parseCases env = 
  | DeclSem s -> 
    -- Assign unique ids to each case based on nextId in env
    let casesWithId = zipWith 
      (lam c. lam id. {id = addi env.nextId id, thn = c.thn, pat = c.pat})
      s.cases
      (range 0 (length s.cases) 1)
    in 
    let env = {env with nextId = addi env.nextId (length s.cases)} in 

    let pats = concat (collectPats env s.includes) casesWithId in

    recursive let removeDups = lam seenIds : Set Int. lam cases. 
      switch cases
        case [h] ++ t then
          if setMem h.id seenIds then
            removeDups seenIds t
          else 
             cons h (removeDups (setInsert h.id seenIds) t)
        case [] then []
      end
    in
    let pats = removeDups (setEmpty subi) pats in 

    let normPats = map patToNormpat (map (lam c. c.pat) pats) in 
    let pairs = indexPairs (length normPats) in 

    let isStrictSubpat = lam pat1. lam pat2.
      null (normpatIntersect pat1 (normpatComplement pat2))
    in

    let g = digraphAddVertices (range 0 (length pats) 1) (digraphEmpty subi (lam. lam. true)) in 

    let accGraph : (Digraph Int ())
                -> (Int, Int)
                -> Result CompositionWarning CompositionError (Digraph Int ())
      = lam g. lam p. 
        match p with (i, j) in 
        let ap = get normPats i in 
        let an = normpatComplement ap in 

        let bp = get normPats j in 
        let bn = normpatComplement bp in 

        let a_minus_b = normpatIntersect ap bn in
        let b_minus_a = normpatIntersect bp an in

        -- printLn (match getPatStringCode 0 pprintEnvEmpty (get pats i).pat with (_, s) in s) ;
        -- printLn (int2string (i)) ;
        -- printLn (match getPatStringCode 0 pprintEnvEmpty (get pats j).pat with (_, s) in s) ;
        -- printLn (int2string (j)) ;

        if and (null a_minus_b) (null b_minus_a) then 
          -- EQUAL
          -- printLn "equal" ;
          _err (InvalidSemPatterns {
            semIdent = s.ident, 
            info = s.info
          })
        else if null a_minus_b then 
          -- SUBSET
          -- printLn "subset" ;
          _ok (digraphAddEdge i j () g)
        else if null b_minus_a then 
          -- SUPERSET
          -- printLn "superset" ;
          _ok (digraphAddEdge j i () g)

        else
          let overlapping = normpatIntersect ap bp in
          if null overlapping then 
            -- DISJOINT
            -- printLn "disjoint" ;
            _ok g
          else
            -- OVERLAPPING
            -- printLn "overlapping" ;
            _err (InvalidSemPatterns {
              semIdent = s.ident, 
              info = s.info
            })
    in 
    let result = _foldl accGraph g pairs in 

    match _consume result with (_, errorsOrGraph) in
    switch errorsOrGraph 
    case Left errs then _err (head errs)
    case Right graph then 
      let order = digraphTopologicalOrder graph in
      let orderedCases = map (lam i. get pats i) order in 
      _ok (insertSemPatMap env s.ident orderedCases)
    end

end

lang TestLang = MLangSym + MLangCompositionCheck end

mexpr 
use TestLang in 
use MLangPrettyPrint in 

let handleResult = lam res.
  switch _consume res 
    case (_, Left errors) then iter raiseError errors
    case (_, Right _) then printLn "Langauge composition is valid!"
    end
in  

let assertValid = lam res. 
  switch _consume res 
  case (_, Left errors) then 
    printLn "Expected language composition to be valid, but found the following errors:" ;
    iter raiseError errors
  case _ then print "."
  end
in

let assertDifferentBaseSem = lam res. 
  switch _consume res 
  case (_, Left ([DifferentBaseSem _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

let assertDifferentBaseSyn = lam res. 
  switch _consume res 
  case (_, Left ([DifferentBaseSyn _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

let assertMismatchedSemsParams = lam res. 
  switch _consume res 
  case (_, Left ([MismatchedSemParams _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

let assertMIsmatchedSynParams = lam res. 
  switch _consume res 
  case (_, Left ([MismatchedSynParams _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

let assertInvalidSemParams = lam res. 
  switch _consume res 
  case (_, Left ([InvalidSemPatterns _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

-- Test invalid language composition due to lack of base 
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
assertDifferentBaseSyn (checkComposition p) ;
-- handleResult (checkComposition p) ;

let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_syn_ "Foo" []
        ],
        decl_langi_ "L1" ["L0"] [
            decl_syn_ "Foo" [("Baz", tyint_)]
        ],
        decl_langi_ "L2" ["L0"] [
            decl_syn_ "Foo" [("BazBaz", tychar_)]
        ],
        decl_langi_ "L12" ["L0", "L1", "L2"] []
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p) ;

-- Test invalid language composition due to lack of base
let p : MLangProgram = {
    decls = [
        decl_langi_ "L1" [] [
            decl_sem_ "f" [] []
        ],
        decl_langi_ "L2" [] [
            decl_sem_ "f" [] []
        ],
        decl_langi_ "L12" ["L1", "L2"] [
          decl_sem_ "f" [] []
        ]        
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertDifferentBaseSem (checkComposition p) ;

-- Test semantic functions with valid base
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
        ]        
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p) ;

let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_syn_ "Foo" [],
            decl_sem_ "f" [("x", tyint_), ("y", tyint_)] []
        ],
        decl_langi_ "L1" ["L0"] [
            decl_syn_ "Foo" [("Baz", tyint_)],
            decl_sem_ "f" [("x", tyint_), ("y", tyint_)] []
        ],
        decl_langi_ "L2" ["L0"] [
            decl_syn_ "Foo" [("BazBaz", tychar_)],
            decl_sem_ "f" [("x", tyint_), ("y", tyint_)] []
        ],
        decl_langi_ "L12" ["L0", "L1", "L2"] [
        ]        
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p) ;

-- Test semantic function with matching number of params
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_sem_ "f" [("x", tyint_), ("y", tyint_)] []
        ],
        decl_langi_ "L1" ["L0"] [
          decl_sem_ "f" [("x", tyint_), ("y", tyint_)] []
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p) ;

-- Test semantic function with non-matching number of params
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_sem_ "f" [("x", tyint_), ("y", tyint_)] []
        ],
        decl_langi_ "L1" ["L0"] [
          decl_sem_ "f" [("x", tyint_)] []
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertMismatchedSemsParams (checkComposition p) ;

-- Test that semantic params get copied correctly. 
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
match symbolizeMLang symEnvDefault p with (_, p) in 
assertDifferentBaseSem (checkComposition p) ;

-- Test sem with valid patterns
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_sem_ "f" [] [
              (por_ (pint_ 3) (pint_ 2), int_ 1),
              (por_ (pint_ 0) (pint_ 1), int_ 2)
            ]
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p) ;

-- Test invalid sem with equal patterns
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_sem_ "f" [] [
              (por_ (pint_ 0) (pint_ 1), int_ 1),
              (por_ (pint_ 0) (pint_ 1), int_ 2)
            ]
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertInvalidSemParams (checkComposition p) ;

-- Test sem with invalid overlapping patterns
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_sem_ "f" [] [
              (por_ (pint_ 0) (pint_ 1), int_ 1),
              (por_ (pint_ 0) (pint_ 2), int_ 2)
            ]
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertInvalidSemParams (checkComposition p) ;

-- Test invalid sem where patterns are spread accross langauges
-- Test sem with invalid overlapping patterns
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_sem_ "f" [] [
              (por_ (pint_ 0) (pint_ 1), int_ 1)
            ]
        ],
        decl_langi_ "L1" ["L0"] [
          decl_sem_ "f" [] [
              (por_ (pint_ 0) (pint_ 2), int_ 2)
          ]
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertInvalidSemParams (checkComposition p) ;

-- Test that the check on the number of parameters also works when
-- the number of parameters is specified through a type annotation. 
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_semty_ "f" (tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
        ],
        decl_langi_ "L1" ["L0"] [
          decl_sem_ "f" [("x", tyint_)] [
              (pvar_ "y", addi_ (var_ "x") (var_ "y"))
          ]
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p);

-- Test that the cehck on the number of parameters also works when 
-- a semantic function is implicitly present in a language
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_semty_ "f" (tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
        ],
        decl_langi_ "L1" ["L0"] [],
        decl_langi_ "L2" ["L1"] [
          decl_sem_ "f" [("x", tyint_)] [
              (pvar_ "y", addi_ (var_ "x") (var_ "y"))
          ]
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p);

-- Test that patterns which are included multiple times
-- are only considered once during language composition. Since L1 and L2 
-- both extend L0, they both include the case of L0. This case sould only be 
-- considered once in L12.
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
          decl_syn_ "Foo" [],
          decl_sem_ "f" [] [(pvarw_, int_ -1)]
        ],
        decl_langi_ "L1" ["L0"] [
          decl_syn_ "Foo" [("Bar", tyunit_)],
          decl_sem_ "f" [] [(pcon_ "Bar" pvarw_, int_ 0)]
        ],
        decl_langi_ "L2" ["L0"] [
          decl_syn_ "Foo" [("Baz", tyunit_)],
          decl_sem_ "f" [] [(pcon_ "Baz" pvarw_, int_ 1)]
        ],
        decl_langi_ "L12" ["L1", "L2"] []
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkComposition p);

()