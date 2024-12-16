include "cuda/constant-app.mc"
include "cuda/inline-higher.mc"
include "cuda/lang-fix.mc"
include "cuda/pmexpr-ast.mc"
include "cuda/well-formed.mc"
include "futhark/well-formed.mc"
include "mexpr/anf.mc"
include "mexpr/cse.mc"
include "mexpr/lamlift.mc"
include "mexpr/demote-recursive.mc"
include "mexpr/monomorphize.mc"
include "pmexpr/build.mc"
include "pmexpr/classify.mc"
include "pmexpr/copy-analysis.mc"
include "pmexpr/extract.mc"
include "pmexpr/inline-higher-order.mc"
include "pmexpr/nested-accelerate.mc"
include "pmexpr/parallel-patterns.mc"
include "pmexpr/parallel-rewrite.mc"
include "pmexpr/tailrecursion.mc"
include "pmexpr/utest-size-constraint.mc"

let _cudaCheckRankId = nameSym "checkTensorRank"
let _cudaCheckRankImpl =
  let a = nameSym "a" in
  let maxrank = nameSym "maxRank" in
  let t = nameSym "t" in
  nlet_ _cudaCheckRankId
    (ntyall_ a (tyarrows_ [tytensor_ (ntyvar_ a), tyint_, tyunit_]))
    (nlam_ t (tytensor_ (ntyvar_ a)) (nlam_ maxrank tyint_
      (if_ (gti_ (tensorRank_ (tytensor_ (ntyvar_ a)) (nvar_ t)) (nvar_ maxrank))
        (error_ (str_ "Found tensor with rank exceeding maximum"))
        unit_)))
let _futharkCheckRegularId = nameSym "checkSequenceRegular"
let _futharkCheckRegularImpl =
  let a = nameSym "a" in
  let s = nameSym "s" in
  let k = nameSym "k" in
  let x = nameSym "x" in
  let y = nameSym "y" in
  nlet_ _futharkCheckRegularId
    (ntyall_ a (tyarrow_ (tyseq_ (tyseq_ (ntyvar_ a))) tyunit_))
    (nlam_ s (tyseq_ (tyseq_ (ntyvar_ a))) (bindall_ [
      nlet_ k tyint_ (length_ (head_ (nvar_ s))),
      if_
        (foldl_
          (nlam_ x tybool_ (nlam_ y (tyseq_ (ntyvar_ a))
            (if_ (eqi_ (nvar_ k) (length_ (nvar_ y)))
              (nvar_ x)
              false_)))
            true_
            (tail_ (nvar_ s)))
        unit_
        (error_ (str_ "Irregular sequence found"))]))

lang PMExprCompileWellFormedInstrumentation = VarAst
  sem instrumentationMap : () -> Map Name Expr
  sem instrumentationMap =
  | () ->
    mapFromSeq nameCmp [
      (_cudaCheckRankId, _cudaCheckRankImpl),
      (_futharkCheckRegularId, _futharkCheckRegularImpl)]

  sem findUsedImplementations : Expr -> Map Name (Bool, Expr)
  sem findUsedImplementations =
  | ast ->
    findUsedImplementationsH
      (mapMapWithKey (lam. lam e. (false, e)) (instrumentationMap ()))
      ast

  sem findUsedImplementationsH : Map Name (Bool, Expr) -> Expr
                              -> Map Name (Bool, Expr)
  sem findUsedImplementationsH acc =
  | TmVar t ->
    match mapLookup t.ident acc with Some entry then
      mapInsert t.ident (true, entry.1) acc
    else acc
  | t -> sfold_Expr_Expr findUsedImplementationsH acc t

  sem addGlobalDefinitions : Expr -> Expr
  sem addGlobalDefinitions =
  | ast ->
    mapFoldWithKey
      (lam acc. lam. lam entry.
        match entry with (isUsed, expr) in
        if isUsed then bind_ expr acc else acc)
      ast (findUsedImplementations ast)
end

-- NOTE(larshum, 2022-06-27): This language fragment defines the accelerate
-- compilation up to the well-formedness checks for each backend. In the
-- future, it should define the entire compilation process.
lang PMExprCompileWellFormedBase =
  PMExprCompileWellFormedInstrumentation + PMExprBuild + MExprLambdaLift +
  PMExprExtractAccelerate + PMExprNestedAccelerate + PMExprTensorCopyAnalysis +
  PMExprClassify

  type WellFormedConfig = {
    dynamicChecks : Bool,
    tensorMaxRank : Int
  }

  sem checkWellFormedAst : (Map Name AccelerateData, Expr) -> Class -> Expr

  sem checkWellFormedAsts : ClassificationResult -> ClassificationResult
  sem checkWellFormedAsts =
  | asts ->
    mapMapWithKey
      (lam class. lam entry.
        (entry.0, checkWellFormedAst entry class))
      asts

  sem instrumentWellFormedChecksBody
    : WellFormedConfig -> Expr -> Class -> Expr

  sem instrumentWellFormedChecks
    : Set Name -> WellFormedConfig -> Class -> Expr -> Expr
  sem instrumentWellFormedChecks accelerateIds config class =
  | TmLet t ->
    let f = lam e.
      instrumentWellFormedChecks accelerateIds config class e in
    let body =
      if setMem t.ident accelerateIds then
        instrumentWellFormedChecksBody config t.body class
      else f t.body in
    TmLet {t with body = body, inexpr = f t.inexpr}
  | t -> smap_Expr_Expr (instrumentWellFormedChecks accelerateIds config class) t

  -- Performs compilation up to the point where well-formedness checks can be
  -- performed. This allows reusing the well-formedness checking code
  -- regardless of whether acceleration is enabled or not.
  sem checkWellFormed : WellFormedConfig -> Expr -> {seqAst : Expr, accelerateData : Map Name AccelerateData, accelerateAsts : ClassificationResult}
  sem checkWellFormed config =
  | ast ->
    match addIdentifierToAccelerateTerms ast with (accelerateData, ast) in
    match liftLambdasWithSolutions ast with (solutions, ast) in
    let ast = typeCheck ast in
    let accelerateIds = mapMap (lam. ()) accelerateData in
    let accelerateAst = extractAccelerateTerms accelerateIds ast in
    match eliminateDummyParameter (mapMap (lam x. x.vars) solutions) accelerateData accelerateAst
    with (accelerateData, accelerateAst) in
    checkNestedAccelerate accelerateIds accelerateAst;
    let accelerateData = eliminateTensorCopying accelerateData ast in
    let accelerateAsts = classifyAccelerated accelerateData accelerateAst in
    let ast =
      if config.dynamicChecks then
        mapFoldWithKey
          (lam ast. lam class. lam entry.
            match entry with (accelerateData, _) in
            let accelerateIds = mapMap (lam. ()) accelerateData in
            instrumentWellFormedChecks accelerateIds config class ast)
          ast accelerateAsts
      else ast in
    { seqAst = addGlobalDefinitions ast
    , accelerateData = accelerateData
    , accelerateAsts = checkWellFormedAsts accelerateAsts}
end

lang PMExprCudaWellFormed =
  PMExprCompileWellFormedBase + CudaPMExprAst + CudaLanguageFragmentFix +
  CudaInlineHigherOrder + MExprANF + MExprMonomorphize

  sem cudaCheckTensorRank : Int -> Name -> Expr -> Type -> Expr
  sem cudaCheckTensorRank tensorMaxRank id acc =
  | TySeq t ->
    let innerId = nameSym "x" in
    let body = cudaCheckTensorRank tensorMaxRank innerId unit_ t.ty in
    match body with TmRecord _ then acc
    else bind_ (ulet_ "" (iter_ (nulam_ innerId body) (nvar_ id))) acc
  | TyTensor t ->
    -- NOTE(larshum, 2022-06-28): This is correct given that a nested tensor is
    -- not considered well-formed.
    bind_
      (ulet_ ""
        (appf2_ (nvar_ _cudaCheckRankId) (nvar_ id) (int_ tensorMaxRank)))
      acc
  | TyRecord t ->
    mapFoldWithKey
      (lam acc. lam sid. lam ty.
        let innerId = nameSym "x" in
        let fieldBody = cudaCheckTensorRank tensorMaxRank innerId unit_ ty in
        match fieldBody with TmRecord _ then acc
        else
          let keyId = sidToString sid in
          bind_
            (ulet_ ""
              (bind_ (nulet_ innerId (recordproj_ keyId (nvar_ id))) fieldBody))
            acc)
      acc t.fields
  | TyArrow _ | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> acc
  | ty ->
    let msg = "Dynamic CUDA well-formedness generation failed for type" in
    errorSingle [infoTy ty] msg

  sem instrumentCudaWellFormedChecks : Int -> Expr -> Expr
  sem instrumentCudaWellFormedChecks tensorMaxRank =
  | TmLam t ->
    checkCudaParameterTypeWellFormedness t.info () t.tyParam;
    let body = instrumentCudaWellFormedChecks tensorMaxRank t.body in
    TmLam {t with body = cudaCheckTensorRank tensorMaxRank t.ident body t.tyParam}
  | body -> body

  sem checkCudaParameterTypeWellFormedness : Info -> () -> Type -> ()
  sem checkCudaParameterTypeWellFormedness info acc =
  | ty & (TyArrow _) ->
    let tystr = use MExprPrettyPrint in type2str ty in
    errorSingle [info]
      (join ["Type ", tystr, " cannot be passed to accelerated expressions ",
             "using the functional backend."])
  | ty -> sfold_Type_Type (checkCudaParameterTypeWellFormedness info) acc ty

  sem instrumentWellFormedChecksBody config ast =
  | Cuda _ -> instrumentCudaWellFormedChecks config.tensorMaxRank ast

  sem checkWellFormedAst entry =
  | Cuda _ ->
    match entry with (_, ast) in
    let ast = monomorphize ast in
    let ast = fixLanguageFragmentSemanticFunction ast in
    let ast = normalizeTerm ast in
    let ast = inlinePartialFunctions ast in
    (use CudaWellFormed in wellFormed ast);
    ast
end

lang PMExprFutharkWellFormed =
  PMExprCompileWellFormedBase + PMExprUtestSizeConstraint + PMExprRewrite +
  PMExprTailRecursion + MExprCSE + MExprANF + PMExprParallelPattern +
  PMExprInlineFunctions + MExprDemoteRecursive

  sem futharkCheckSequenceRegularity : Name -> Expr -> Type -> Expr
  sem futharkCheckSequenceRegularity id acc =
  | TySeq {ty = ty & (TySeq _)} ->
    let innerId = nameSym "x" in
    let innerCheck = futharkCheckSequenceRegularity innerId unit_ ty in
    match innerCheck with TmRecord _ then
      bind_
        (ulet_ "" (app_ (nvar_ _futharkCheckRegularId) (nvar_ id)))
        acc
    else
      bindall_
        [ ulet_ "" (app_ (nvar_ _futharkCheckRegularId) (nvar_ id))
        , ulet_ "" (iter_ (nulam_ innerId innerCheck) (nvar_ id))
        , acc ]
  | TySeq t -> acc
  | TyRecord t ->
    mapFoldWithKey
      (lam acc. lam sid. lam ty.
        let innerId = nameSym "x" in
        let fieldBody = futharkCheckSequenceRegularity innerId unit_ ty in
        match fieldBody with TmRecord _ then acc
        else
          let keyId = sidToString sid in
          bind_
            (ulet_ ""
              (bind_ (nulet_ innerId (recordproj_ keyId (nvar_ id))) fieldBody))
            acc)
      acc t.fields
  | TyArrow _ | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> acc
  | ty ->
    let msg = "Dynamic Futhark well-formedness generation failed for type" in
    errorSingle [infoTy ty] msg

  sem instrumentFutharkWellFormedChecks : Expr -> Expr
  sem instrumentFutharkWellFormedChecks =
  | TmLam t ->
    checkFutharkParameterTypeWellFormedness t.info () t.tyParam;
    let body = instrumentFutharkWellFormedChecks t.body in
    TmLam {t with body = futharkCheckSequenceRegularity t.ident body t.tyParam}
  | body -> body

  sem checkFutharkParameterTypeWellFormedness : Info -> () -> Type -> ()
  sem checkFutharkParameterTypeWellFormedness info acc =
  | ty & (TyRecord _ | TyArrow _) ->
    let tystr = use MExprPrettyPrint in type2str ty in
    errorSingle [info]
      (join ["Type ", tystr, " cannot be passed to accelerated expressions ",
             "using the functional backend."])
  | ty -> sfold_Type_Type (checkFutharkParameterTypeWellFormedness info) acc ty

  sem instrumentWellFormedChecksBody config ast =
  | Futhark _ -> instrumentFutharkWellFormedChecks ast

  sem patternRewrite : Expr -> Expr
  sem patternRewrite =
  | ast ->
    let parallelPatterns = [
      getMapPattern (), getMap2Pattern (), getReducePattern ()
    ] in
    parallelPatternRewrite parallelPatterns ast

  sem checkWellFormedAst entry =
  | Futhark _ ->
    match entry with (_, ast) in
    let ast = replaceUtestsWithSizeConstraint ast in
    let ast = rewriteTerm ast in
    let ast = tailRecursive ast in
    let ast = cseGlobal ast in
    let ast = normalizeTerm ast in
    let ast = patternRewrite ast in
    let ast = demoteRecursive ast in
    let ast = inlineHigherOrderFunctions ast in
    (use FutharkWellFormed in wellFormed ast);
    ast
end

lang PMExprCompileWellFormed = PMExprCudaWellFormed + PMExprFutharkWellFormed
end

lang TestLang = PMExprCompileWellFormed + PMExprPrettyPrint end

mexpr

use TestLang in

let fnid = nameSym "f" in
let x = nameSym "x" in
let t =
  nlet_ fnid (tyarrow_ (tyseq_ (tyseq_ tyint_)) (tyseq_ (tyseq_ tyint_)))
    (nlam_ x (tyseq_ (tyseq_ tyint_)) (nvar_ x))
in
let ids = setOfSeq nameCmp [fnid] in
let config = {dynamicChecks = true, tensorMaxRank = 3} in
let t =
  addGlobalDefinitions
    (instrumentWellFormedChecks ids config (Futhark ()) t) in
-- printLn (expr2str t);
()
