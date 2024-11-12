-- Checks that the language composition in an MLang is valid. 
-- 
-- Language composition is valid if the following conditions are met: 
-- (1) Each semantic function and syntax declaration that includes multiple
--     other declarations, these declarations must share the same base.
-- (2) The number of arguments to a semantic function must be the same as that 
--     of the functions it includes.
-- (3) The number of type paramaters of a syntax declaration must be the same
--     as that of the syntax declarations it includes.
-- (4) The cases in a semantic function, including those that are included,
--     can only overlap if they orderable by strict subset. 


include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"
include "symbolize.mc"
include "language-composer.mc"

include "mexpr/pattern-analysis.mc"
include "mexpr/ast-builder.mc"

include "common.mc"
include "bool.mc"
include "name.mc"
include "set.mc"
include "result.mc"
include "digraph.mc"

type ComposotionCheckOptions = {
  disableStrictSumExtension : Bool
}

let defaultCompositionCheckOptions = {
  disableStrictSumExtension = false
}

type ExtendedCopat = use MLangAst in {
  copat : Copat,
  thn : Expr,
  id : Int,
  orig : (String, String)
}

type CompositionCheckEnv = {
  -- NOTE(voorberg, 04/06/2024): It might be cleaner to move the options out
  -- of the environment since they will not be updated during the checks anyways.
  options : ComposotionCheckOptions,

  nextId : Int,
  -- Mapping from the symbolized name of a syn or sem to their base declaration
  baseMap : Map (String, String) Name,
  baseMap2 : Map Name Name,
  -- Mapping from symbolized name of a syn to the amount of parameters
  paramMap : Map (String, String) Int,
  -- Mapping form a symbolized sem name to the symbolized names of its arguments if they are defined.
  semArgsMap : Map (String, String) (Option [Name]),
  -- ,

  -- Mapping from symbolized names of a sem to its cases that are ordered by
  -- the subset relation on the patterns. 
  -- We also introduce a unique id for each case. We need this id to be able 
  -- to remove duplicate cases under languaage composition.
  semPatMap : Map (String, String) [use MLangAst in {pat: Pat, thn : Expr, id : Int, orig : (String, String)}],

  -- Cosem cases. Note that we again introduce an ID to distinguish cases.
  cosemCaseMap : Map (String, String) (Set ExtendedCopat),

  semTyVarMap : Map (String, String) [Name],

  semSymMap : Map (String, String) Name,

  semBaseToTyAnnot : Map Name (use MExprAst in Type),

  symToPair : Map Name (String, String),

  langToSems : Map String [Name]
}

let _foldlMfun : all w. all e. all a. all b.
  a -> b -> [(a -> b -> Result w e a)] -> Result w e a
  = lam a. lam b. lam fs. 
    result.foldlM (lam a. lam f. f a b) a fs

let collectPats = lam env. lam includes.
  let incl2pats = lam i : (String, String). 
    match mapLookup i env.semPatMap with Some pats then
      pats
    else error (concat 
      "Illegal state during composition-check! The name patterns for each "
      "included sem should have already been included!")
  in 
  join (map incl2pats includes)

let tupleStringCmp = tupleCmp2 cmpString cmpString

let cmpExtCopat : ExtendedCopat -> ExtendedCopat -> Int = 
  lam lhs. lam rhs. subi lhs.id rhs.id

let collectCopats = lam env. lam includes.
  let incl2pats = lam i : (String, String). 
    match mapLookup i env.cosemCaseMap with Some cases then
      cases
    else error (concat 
      " * Illegal state during composition-check! The co-patterns for each \n"
      " * included cosem should have already been parsed!")
  in 
  foldl setUnion (setEmpty cmpExtCopat) (map incl2pats includes)

let _emptyCompositionCheckEnv : CompositionCheckEnv = {
  options = defaultCompositionCheckOptions,
  nextId = 0,
  baseMap = mapEmpty tupleStringCmp,
  baseMap2 = mapEmpty nameCmp,
  paramMap = mapEmpty tupleStringCmp,
  semPatMap = mapEmpty tupleStringCmp,
  semArgsMap = mapEmpty tupleStringCmp,
  cosemCaseMap = mapEmpty tupleStringCmp,
  semTyVarMap = mapEmpty tupleStringCmp,
  semSymMap = mapEmpty tupleStringCmp,
  semBaseToTyAnnot = mapEmpty nameCmp,
  symToPair = mapEmpty nameCmp,
  langToSems = mapEmpty cmpString
}

let insertBaseMap : CompositionCheckEnv -> (String, String) -> Name -> Name -> CompositionCheckEnv = 
  lam env. lam k. lam k2. lam v. 
    {env with baseMap = mapInsert k v env.baseMap,
              baseMap2 = mapInsert k2 v env.baseMap2}
    
let insertParamMap : CompositionCheckEnv -> (String, String) -> Int -> CompositionCheckEnv = 
  lam env. lam k. lam v. 
    {env with paramMap = mapInsert k v env.paramMap}

let insertArgsMap : CompositionCheckEnv -> (String, String) -> Option [Name] -> CompositionCheckEnv =  
  lam env. lam k. lam v.
    {env with semArgsMap = mapInsert k v env.semArgsMap}

let insertSemPatMap = lam env. lam k. lam v.
  {env with semPatMap = mapInsert k v env.semPatMap}

-- TODO(voorberg, 09/09/2024): Refactor to avoid code duplication between syn, sem and cosyn. 
-- E.g. checking the params and base is identical for cosyn and syn.
-- TODO(voorberg, 15/09/202): A composition check should be added that ensures
-- that the labels in a constructor's type are disjoint under product extension.
lang MLangCompositionCheck = MLangAst + MExprPatAnalysis + MExprAst + MExprPrettyPrint + RecordCopatAst
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
  | SyntaxBaseHasIncludes {
    ident : Name,
    info : Info
  }
  | SyntaxSumExtHasNoIncludes {
    ident : Name,
    info : Info
  }
  | OverlappingCopatterns {
    ident : Name,
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
  | SyntaxBaseHasIncludes e -> 
    let msg =  join [
      "Invalid language composition because the declaration '",
      nameGetStr e.ident,
      "' includes other declarations even though it is a base declaration",
      " as indicated by the '=' symbol! You can use the",
      "--disable-strict-sum-extension flag to disable this check."
    ] in 
    errorMulti [(e.info, "")] msg
  | SyntaxSumExtHasNoIncludes e ->
    let msg = join [
      "Invalid language composition because the declaration '",
      nameGetStr e.ident,
      "' does not include any other other declarations even though it is",
      "syntactically declared as a sum extension through the += symbol!",
      "You can use the",
      "--disable-strict-sum-extension flag to disable this check."
    ] in 
    errorMulti [(e.info, "")] msg
  | OverlappingCopatterns e ->
    let msg = join [
      " * Invalid language composition because the declaration '",
      nameGetStr e.ident,
      "' contains overlapping co-patterns!"
    ] in 
    errorMulti [(e.info, "")] msg
  
  sem checkComposition : MLangProgram -> Result CompositionWarning CompositionError CompositionCheckEnv
  sem checkComposition =| prog -> 
    checkCompositionWithOptions defaultCompositionCheckOptions prog

  sem checkCompositionWithOptions : ComposotionCheckOptions -> 
                                    MLangProgram -> 
                                    Result CompositionWarning CompositionError CompositionCheckEnv
  sem checkCompositionWithOptions options =| prog -> 
    let env = {_emptyCompositionCheckEnv with options = options} in 
    result.foldlM validateTopLevelComposition env prog.decls 

  sem validateTopLevelComposition : CompositionCheckEnv -> 
                                    Decl -> 
                                    Result CompositionWarning CompositionError CompositionCheckEnv
  sem validateTopLevelComposition env = 
  | DeclLang l -> 
    result.foldlM (validateLangDeclComposition (nameGetStr l.ident)) env l.decls
  | other -> result.ok env

  sem validateLangDeclComposition langStr env = 
  | DeclSem s & d ->
    _foldlMfun env d [validateSynSemParams langStr, validateSynSemBase langStr, validateStrictSumExtension, validateSemCaseOrdering langStr]
  | DeclSyn s & d ->
    _foldlMfun env d [validateSynSemParams langStr, validateSynSemBase langStr, validateStrictSumExtension]
  | SynDeclProdExt s & d ->
    validateSynSemBase langStr env d
  | DeclCosyn _ & d -> 
    _foldlMfun env d [validateSynSemParams langStr, validateSynSemBase langStr]
  | DeclCosem _ & d ->
    _foldlMfun env d [validateSynSemParams langStr, 
                      validateSynSemBase langStr, 
                      validateCosemPatterns langStr]
  | other -> result.ok env

  sem validateCosemPatterns langStr env = 
  | DeclCosem d ->  
    let includedCases = collectCopats env d.includes in 

    let work = lam env. lam cas.
      match cas with (copat, thn) in 
      ({env with nextId = addi env.nextId 1}, {copat = copat, 
                                               thn = thn, 
                                               id = env.nextId,
                                               orig = (langStr, nameGetStr d.ident)}) in 
    match mapAccumL work env d.cases with (env, newCases) in 
    let newCases = setOfSeq cmpExtCopat newCases in 

    let allCases = setUnion newCases includedCases in 

    let propError = lam acc : Either CompositionError (Set String). lam cas. 
      switch acc 
        case Left err then Left err
        case Right s then 
          match cas with {copat = RecordCopat {fields = fields}} in 
          let fields = setOfSeq cmpString fields in 
          if setDisjoint s fields then
            Right (setUnion s fields)
          else 
            Left (OverlappingCopatterns {ident = d.ident, info = d.info})
      end
    in 
    
    match setFold propError (Right (setEmpty cmpString)) allCases with Left err then 
      result.err err
    else
      let env = {env with cosemCaseMap = mapInsert (langStr, nameGetStr d.ident) allCases env.cosemCaseMap} in 
      result.ok env 


  sem validateSynSemParams : String ->
                             CompositionCheckEnv -> 
                             Decl -> 
                             Result CompositionWarning CompositionError CompositionCheckEnv
  sem validateSynSemParams langStr env = 
  | DeclCosem s ->
    let args = map (lam a. a.ident) s.args in 
    let includeParams : [[Name]] = mapOption (lam incl. match mapLookup incl env.semArgsMap with Some res in res) s.includes in 

    let errIfUnequalAmount : [Name] -> Option CompositionError = lam params.
      if eqi (length params) (length args) then
        None ()
      else 
        Some (MismatchedSemParams {
          semIdent = s.ident,
          info = s.info
        })
    in

    let errs = mapOption errIfUnequalAmount includeParams in 

    if neqi (length errs) 0 then
      result.err (head errs)
    else 
       result.ok (insertArgsMap env (langStr, nameGetStr s.ident) (Some args))
  | DeclCosyn s ->  
    let str = nameGetStr s.ident in 
    let paramNum = length s.params in 

    match s.includes with [] then 
      result.ok (insertParamMap env (langStr, str) paramNum)
    else 
      let paramNum = length s.params in 

      let includeList = map 
        (lam incl. match mapLookup incl env.paramMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq subi includeList in 
      let includeSet = setInsert paramNum includeSet in 

      if eqi 1 (setSize includeSet) then
        result.ok (insertParamMap env (langStr, str) paramNum)
      else
        result.err (MismatchedSynParams {
          synIdent = s.ident,
          info = s.info
        })
  | DeclSyn s -> 
    let str = nameGetStr s.ident in 
    let paramNum = length s.params in 

    match s.includes with [] then 
      result.ok (insertParamMap env (langStr, str) paramNum)
    else 
      let paramNum = length s.params in 

      let includeList = map 
        (lam incl. match mapLookup incl env.paramMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq subi includeList in 
      let includeSet = setInsert paramNum includeSet in 

      if eqi 1 (setSize includeSet) then
        result.ok (insertParamMap env (langStr, str) paramNum)
      else
        result.err (MismatchedSynParams {
          synIdent = s.ident,
          info = s.info
        })
  | DeclSem {ident = ident, args = None _} ->
    result.ok (insertArgsMap env (langStr, nameGetStr ident) (None ()))
  | DeclSem s ->
    match s.args with Some args in 
    let args = map (lam a. a.ident) args in 
    let includeParams : [[Name]] = mapOption (lam incl. match mapLookup incl env.semArgsMap with Some res in res) s.includes in 

    let errIfUnequalAmount : [Name] -> Option CompositionError = lam params.
      if eqi (length params) (length args) then
        None ()
      else 
        Some (MismatchedSemParams {
          semIdent = s.ident,
          info = s.info
        })
    in

    let errs = mapOption errIfUnequalAmount includeParams in 

    if neqi (length errs) 0 then
      result.err (head errs)
    else 
       result.ok (insertArgsMap env (langStr, nameGetStr s.ident) (Some args))

  sem validateSynSemBase : String -> 
                           CompositionCheckEnv -> 
                           Decl -> 
                           Result CompositionWarning CompositionError CompositionCheckEnv
  sem validateSynSemBase langStr env =
  | DeclCosem s -> 
    let env = {env with symToPair = mapInsert s.ident (langStr, nameGetStr s.ident) env.symToPair,
                        langToSems = mapInsert langStr (cons s.ident (mapLookupOrElse (lam. []) langStr env.langToSems)) env.langToSems
    } in

    match s.includes with [] then 
      if s.isBase then 
        result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident s.ident)
      else 
        result.err (DifferentBaseSem {
          semIdent = s.ident,
          info = s.info
        })
    else 
      if s.isBase then 
        result.err (DifferentBaseSem {
          semIdent = s.ident,
          info = s.info
        })
      else 
        let includeList = map 
          (lam incl. match mapLookup incl env.baseMap with Some b in b) 
          s.includes in 
        let includeSet = setOfSeq nameCmp includeList in 

        if eqi 1 (setSize includeSet) then
          result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident (head includeList))
        else
          result.err (DifferentBaseSem {
            semIdent = s.ident,
            info = s.info
          })
  | DeclCosyn s -> 
    let env = {env with symToPair = mapInsert s.ident (langStr, nameGetStr s.ident) env.symToPair} in

    match s.includes with [] then 
      result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident s.ident)
    else 
      let includeList = map 
        (lam incl. match mapLookup incl env.baseMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq nameCmp includeList in 

      if eqi 1 (setSize includeSet) then
        result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident (head includeList))
      else
        result.err (DifferentBaseSyn {
          synIdent = s.ident,
          info = s.info
        })
  | DeclSyn s -> 
    let env = {env with symToPair = mapInsert s.ident (langStr, nameGetStr s.ident) env.symToPair} in


    match s.includes with [] then 
      result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident s.ident)
    else 
      let includeList = map 
        (lam incl. match mapLookup incl env.baseMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq nameCmp includeList in 

      if eqi 1 (setSize includeSet) then
        result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident (head includeList))
      else
        result.err (DifferentBaseSyn {
          synIdent = s.ident,
          info = s.info
        })
  | SynDeclProdExt s ->
    let env = {env with symToPair = mapInsert s.ident (langStr, nameGetStr s.ident) env.symToPair} in

    match s.includes with [] then 
      result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident s.ident)
    else 
      let includeList = map 
        (lam incl. match mapLookup incl env.baseMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq nameCmp includeList in 

      if eqi 1 (setSize includeSet) then
        result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident (head includeList))
      else
        result.err (DifferentBaseSyn {
          synIdent = s.ident,
          info = s.info
        })
  | DeclSem s ->
    let env = {env with semSymMap = mapInsert (langStr, nameGetStr s.ident) s.ident env.semSymMap,
                        langToSems = mapInsert langStr (cons s.ident (mapLookupOrElse (lam. []) langStr env.langToSems)) env.langToSems
    } in 
    match s.includes with [] then 
      let env = {env with semBaseToTyAnnot = mapInsert s.ident s.tyAnnot env.semBaseToTyAnnot} in 
      result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident s.ident)
    else 
      let includeList = map 
        (lam incl. match mapLookup incl env.baseMap with Some b in b) 
        s.includes in 
      let includeSet = setOfSeq nameCmp includeList in 

      if eqi 1 (setSize includeSet) then
        result.ok (insertBaseMap env (langStr, nameGetStr s.ident) s.ident (head includeList))
      else
        result.err (DifferentBaseSem {
          semIdent = s.ident, 
          info = s.info
        })

  sem _strictSumExtensionHelper env ident info includes = 
  | BaseKind _ -> 
    if null includes then 
      result.ok env
    else result.err (SyntaxBaseHasIncludes {
      ident = ident,
      info = info
    })
  | SumExtKind _ -> 
    if null includes then 
      result.err (SyntaxSumExtHasNoIncludes {
        ident = ident,
        info = info
      })
    else 
      result.ok env

  sem validateStrictSumExtension env = 
  | DeclSem s ->
    if env.options.disableStrictSumExtension then
      result.ok env
    else
      _strictSumExtensionHelper env s.ident s.info s.includes s.declKind
  | DeclSyn s ->
    if env.options.disableStrictSumExtension then
      result.ok env
    else
      _strictSumExtensionHelper env s.ident s.info s.includes s.declKind
  | _ -> 
    result.ok env 

  sem validateSemCaseOrdering langStr env = 
  | DeclSem s -> 
    recursive let gatherTyVars = lam ty. 
      switch ty
        case TyAll tyall then cons tyall.ident (gatherTyVars tyall.ty)
        case _ then []
      end
    in 
    let env = {env with semTyVarMap = mapInsert (langStr, nameGetStr s.ident) (gatherTyVars s.tyAnnot) env.semTyVarMap} in 

    -- Assign unique ids to each case based on nextId in env
    let casesWithId = zipWith 
      (lam c. lam id. {orig = (langStr, nameGetStr s.ident),
                       id = addi env.nextId id,
                       thn = c.thn,
                       pat = c.pat})
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
    let pairs = pairWithLater (range 0 (length normPats) 1) in 

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
          result.err (InvalidSemPatterns {
            semIdent = s.ident, 
            info = s.info
          })
        else if null a_minus_b then 
          -- SUBSET
          -- printLn "subset" ;
          result.ok (digraphAddEdge i j () g)
        else if null b_minus_a then 
          -- SUPERSET
          -- printLn "superset" ;
          result.ok (digraphAddEdge j i () g)

        else
          let overlapping = normpatIntersect ap bp in
          if null overlapping then 
            -- DISJOINT
            -- printLn "disjoint" ;
            result.ok g
          else
            -- OVERLAPPING
            -- printLn "overlapping" ;
            result.err (InvalidSemPatterns {
              semIdent = s.ident, 
              info = s.info
            })
    in 
    let res = result.foldlM accGraph g pairs in 

    match result.consume res with (_, errorsOrGraph) in
    switch errorsOrGraph 
    case Left errs then result.err (head errs)
    case Right graph then 
      let order = digraphTopologicalOrder graph in
      let orderedCases = map (lam i. get pats i) order in 
      result.ok (insertSemPatMap env (langStr, nameGetStr s.ident) orderedCases)
    end

end

lang TestLang = MLangSym + MLangCompositionCheck end

mexpr 
use TestLang in 
use MLangPrettyPrint in 
use LanguageComposer in 

let checkCompositionDisableStrictness = lam p : MLangProgram.
  checkCompositionWithOptions {disableStrictSumExtension = true} p
in

let handleResult = lam res.
  switch result.consume res 
    case (_, Left errors) then iter raiseError errors
    case (_, Right _) then printLn "Langauge composition is valid!"
    end
in  

let assertValid = lam res. 
  switch result.consume res 
  case (_, Left errors) then 
    printLn "Expected language composition to be valid, but found the following errors:" ;
    iter raiseError errors
  case _ then print "."
  end
in

let assertDifferentBaseSem = lam res. 
  switch result.consume res 
  case (_, Left ([DifferentBaseSem _] ++ _)) then print "."
  case _ then error "Assertion failed! DifferentBaseSem error was expected!"
  end
in

let assertOverlappingCopatterns = lam res. 
  switch result.consume res 
  case (_, Left ([OverlappingCopatterns _] ++ _)) then print "."
  case _ then error "Assertion failed! OverlappingCopatterns error was expected!"
  end
in

let assertDifferentBaseSyn = lam res. 
  switch result.consume res 
  case (_, Left ([DifferentBaseSyn _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

let assertMismatchedSemsParams = lam res. 
  switch result.consume res 
  case (_, Left ([MismatchedSemParams _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

let assertMIsmatchedSynParams = lam res. 
  switch result.consume res 
  case (_, Left ([MismatchedSynParams _] ++ _)) then print "."
  case _ then error "Assertion failed!"
  end
in

let assertInvalidSemParams = lam res. 
  switch result.consume res 
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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertDifferentBaseSyn (checkCompositionDisableStrictness p) ;
-- handleResult (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p) ;

-- Test invalid language composition of sems due to lack of base
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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertDifferentBaseSem (checkCompositionDisableStrictness p) ;

-- Test invalid language composition of co-sems due to lack of base
let p : MLangProgram = {
    decls = [
        decl_langi_ "L1" [] [
            decl_cosem_ "f" [] [] false
        ],
        decl_langi_ "L2" [] [
            decl_cosem_ "f" [] [] false
        ],
        decl_langi_ "L12" ["L1", "L2"] [
          decl_cosem_ "f" [] [] false
        ]        
    ],
    expr = bind_ (use_ "L2") (int_ 10)
} in 
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertDifferentBaseSem (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertMismatchedSemsParams (checkCompositionDisableStrictness p) ;

-- Test co-semantic function with non-matching number of params
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_cosem_ "f" [("x", tyint_), ("y", tyint_)] [] true
        ],
        decl_langi_ "L1" ["L0"] [
          decl_cosem_ "f" [("x", tyint_)] [] false
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertMismatchedSemsParams (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertDifferentBaseSem (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertInvalidSemParams (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertInvalidSemParams (checkCompositionDisableStrictness p) ;

-- Test co-sem with invalid overlapping co-patterns
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_cosyn_ "Foo" [] true (tyrecord_ [("x", tyint_), ("y", tyint_), ("z", tyint_)]),
            decl_cosem_ "f" [] [(record_copat_ "Foo" ["x", "y"], never_), 
                                (record_copat_ "Foo" ["y", "z"], never_)] true
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertOverlappingCopatterns (checkCompositionDisableStrictness p) ;

-- Test co-sem with valid non-overlapping co-patterns
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
            decl_cosyn_ "Foo" [] true (tyrecord_ [("x", tyint_), ("y", tyint_), ("z", tyint_)]),
            decl_cosem_ "f" [] [(record_copat_ "Foo" ["x"], never_), 
                                (record_copat_ "Foo" ["y", "z"], never_)] true
        ]
    ],
    expr = bind_ (use_ "L0") (int_ 10)
} in 
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertInvalidSemParams (checkCompositionDisableStrictness p) ;

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p);

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p);

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
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p);

-- Test syn with parameters
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
          decl_syn_params_ "Foo" ["a"] [
            ("Bar", tyvar_ "a")
          ]
        ],
        decl_langi_ "L1" ["L0"] []
    ],
    expr = uunit_
} in 
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p);

-- Test sem with arguments not defind on base definition
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
          decl_semty_ "f" tyunknown_
        ],
        decl_langi_ "L1" ["L0"] [
          decl_sem_ "f" [("x", tyint_)] []
        ]
    ],
    expr = uunit_
} in 
let p = composeProgram p in
match symbolizeMLang symEnvDefault p with (_, p) in 
assertValid (checkCompositionDisableStrictness p);

()