include "c/ast.mc"
include "c/pprint.mc"
include "cuda/compile.mc"
include "cuda/constant-app.mc"
include "cuda/kernel-translate.mc"
include "cuda/lang-fix.mc"
include "cuda/pmexpr-ast.mc"
include "cuda/pmexpr-compile.mc"
include "cuda/pmexpr-pprint.mc"
include "cuda/pprint.mc"
include "cuda/well-formed.mc"
include "cuda/wrapper.mc"
include "futhark/alias-analysis.mc"
include "futhark/deadcode.mc"
include "futhark/for-each-record-pat.mc"
include "futhark/generate.mc"
include "futhark/pprint.mc"
include "futhark/record-lift.mc"
include "futhark/size-parameterize.mc"
include "futhark/well-formed.mc"
include "futhark/wrapper.mc"
include "mexpr/boot-parser.mc"
include "mexpr/cse.mc"
include "mexpr/lamlift.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/type-lift.mc"
include "mexpr/utesttrans.mc"
include "ocaml/generate.mc"
include "ocaml/mcore.mc"
include "ocaml/pprint.mc"
include "options.mc"
include "parse.mc"
include "pmexpr/ast.mc"
include "pmexpr/build.mc"
include "pmexpr/c-externals.mc"
include "pmexpr/classify.mc"
include "pmexpr/compile.mc"
include "pmexpr/demote.mc"
include "pmexpr/extract.mc"
include "pmexpr/nested-accelerate.mc"
include "pmexpr/parallel-rewrite.mc"
include "pmexpr/pprint.mc"
include "pmexpr/recursion-elimination.mc"
include "pmexpr/replace-accelerate.mc"
include "pmexpr/rules.mc"
include "pmexpr/tailrecursion.mc"
include "pmexpr/utest-size-constraint.mc"
include "pmexpr/well-formed.mc"
include "sys.mc"

lang PMExprCompile =
  BootParser +
  MExprSym + MExprTypeCheck + MExprRemoveTypeAscription +
  MExprUtestTrans + PMExprAst + MExprANF + PMExprDemote + PMExprRewrite +
  PMExprTailRecursion + PMExprParallelPattern +
  MExprLambdaLift + MExprCSE + PMExprRecursionElimination +
  PMExprExtractAccelerate + PMExprClassify + PMExprCExternals +
  PMExprUtestSizeConstraint + PMExprReplaceAccelerate +
  PMExprNestedAccelerate + OCamlGenerate + OCamlTypeDeclGenerate +
  OCamlGenerateExternalNaive + PMExprBuild + PMExprCompileWellFormed
end

lang MExprFutharkCompile =
  FutharkGenerate + FutharkDeadcodeElimination + FutharkSizeParameterize +
  FutharkCWrapper + FutharkRecordParamLift + FutharkForEachRecordPattern +
  FutharkAliasAnalysis + FutharkWellFormed
end

lang MExprCudaCompile =
  MExprUtestTrans + MExprRemoveTypeAscription + CudaPMExprAst +
  CudaPMExprCompile + MExprTypeLift +
  SeqTypeNoStringTypeLift + TensorTypeTypeLift + CudaCompile + CudaKernelTranslate +
  CudaPrettyPrint + CudaCWrapper + CudaWellFormed + CudaConstantApp +
  CudaLanguageFragmentFix
end

let parallelKeywords = [
  "accelerate",
  "map2",
  "parallelFlatten",
  "reduce",
  "parallelLoop",
  "seqLoop",
  "seqLoopAcc",
  "printFloat"
]

let keywordsSymEnv =
  {symEnvEmpty with varEnv =
    mapFromSeq
      cmpString
      (map (lam s. (s, nameSym s)) parallelKeywords)}

let parallelPatterns = [
  getMapPattern (),
  getMap2Pattern (),
  getReducePattern ()
]

let pprintOCamlTops = use OCamlPrettyPrint in
  lam tops : [Top].
  pprintOcamlTops tops

let pprintFutharkAst = use FutharkPrettyPrint in
  lam ast : FutProg.
  printFutProg ast

let pprintPMExprAst = use PMExprPrettyPrint in
  lam ast : Expr.
  expr2str ast

let pprintCudaPMExprAst = use CudaPMExprPrettyPrint in
  lam ast : Expr.
  expr2str ast

let pprintCAst =
  use CPrettyPrint in
  use CProgPrettyPrint in
  lam ast : CProg.
  printCProg [] ast

let pprintCudaAst = use CudaPrettyPrint in
  lam ast : CudaProg.
  printCudaProg cCompilerNames ast

let futharkTranslation : Set Name -> Expr -> FutProg =
  lam entryPoints. lam ast.
  use MExprFutharkCompile in
  let ast = generateProgram entryPoints ast in
  let ast = liftRecordParameters ast in
  let ast = useRecordPatternInForEach ast in
  let ast = aliasAnalysis ast in
  let ast = deadcodeElimination ast in
  parameterizeSizes ast

let cudaTranslation =
  use MExprCudaCompile in
  lam options : Options. lam accelerateData : Map Name AccelerateData. lam ast : Expr.
  let ast = toCudaPMExpr ast in
  match typeLift ast with (typeEnv, ast) in
  let ast = removeTypeAscription ast in
  let opts : CompileCOptions = {
    tensorMaxRank = options.accelerateTensorMaxRank,
    use32BitInts = options.use32BitIntegers,
    use32BitFloats = options.use32BitFloats
  } in
  match compile typeEnv opts ast with (ccEnv, types, tops, _, _) in
  let ctops = join [types, tops] in
  match translateCudaTops accelerateData ccEnv ctops
  with (wrapperMap, cudaTops) in
  let wrapperProg = generateWrapperCode accelerateData wrapperMap
                                        options.accelerateTensorMaxRank ccEnv in
  (CuPProg { includes = cudaIncludes, tops = cudaTops }, wrapperProg)

let mergePrograms : CudaProg -> CudaProg -> CudaProg =
  lam cudaProg. lam wrapperProg.
  use MExprCudaCompile in
  -- NOTE(larshum, 2022-04-01): We split up the tops such that the types
  -- declarations and global definitions are placed in the left side, and
  -- function definitions (the wrapper functions) are placed in the right side.
  recursive let splitWrapperTops : ([CuTop], [CuTop]) -> [CuTop] -> ([CuTop], [CuTop]) =
    lam acc. lam tops.
    match tops with [t] ++ tops then
      match acc with (ltops, rtops) in
      let acc =
        match t with CuTTop {attrs = _, top = CTFun _} then
          (ltops, snoc rtops t)
        else (snoc ltops t, rtops) in
      splitWrapperTops acc tops
    else acc in
  match cudaProg with CuPProg {includes = lincludes, tops = cudaTops} in
  match wrapperProg with CuPProg {includes = rincludes, tops = wrapperTops} in
  match splitWrapperTops ([], []) wrapperTops with (topDecls, topWrapperFunctions) in
  let mergedTops = join [topDecls, cudaTops, topWrapperFunctions] in
  CuPProg {includes = concat lincludes rincludes, tops = mergedTops}

let generateGpuCode =
  use PMExprCompile in
  lam options : Options. lam asts : Map Class (Map Name AccelerateData, Expr).
  mapMapWithKey
    (lam class. lam entry.
      match entry with (accelerateData, ast) in
      match class with Cuda _ then
        use MExprCudaCompile in
        match cudaTranslation options accelerateData ast
        with (cudaProg, wrapperProg) in
        CudaCompileResult (mergePrograms cudaProg wrapperProg)
      else match class with Futhark _ then
        use MExprFutharkCompile in
        let accelerateIds = mapMap (lam. ()) accelerateData in
        let futharkProg = futharkTranslation accelerateIds ast in
        let wrapperProg = generateWrapperCode accelerateData in
        FutharkCompileResult (futharkProg, wrapperProg)
      else never)
    asts

let checkWellFormedness = lam options. lam ast.
  use PMExprCompile in
  let config = {
    dynamicChecks = options.checkWellFormed,
    tensorMaxRank = options.accelerateTensorMaxRank
  } in
  match checkWellFormed config ast
  with {seqAst = seqAst, accelerateData = accelerateData,
        accelerateAsts = accelerateAsts} in
  (seqAst, accelerateData, accelerateAsts)

let generateTests = lam ast. lam testsEnabled.
  use PMExprCompile in
  if testsEnabled then utestGen (removeTypeAscription ast)
  else (symEnvEmpty, utestStrip ast)

let compileAccelerated =
  lam options. lam file.
  use PMExprCompile in
  let ast = parseParseMCoreFile {
    keepUtests = true,
    pruneExternalUtests = false,
    pruneExternalUtestsWarning = false,
    findExternalsExclude = false,
    eliminateDeadCode = true,
    keywords = parallelKeywords
  } file in
  let ast = makeKeywords [] ast in

  let ast = symbolizeExpr keywordsSymEnv ast in
  let ast = typeCheck ast in
  let ast = removeTypeAscription ast in

  match checkWellFormedness options ast
  with (ast, accelerateData, accelerateAsts) in

  -- Generate GPU code for the AST of each accelerate backend in use.
  let gpuResult = generateGpuCode options accelerateAsts in

  -- Construct a sequential version of the AST where parallel constructs have
  -- been demoted to sequential equivalents
  let ast = demoteParallel ast in

  -- Generate utests or strip them from the program.
  match generateTests ast options.runTests with (symEnv, ast) in
  let ast = symbolizeExpr symEnv ast in

  match typeLift ast with (typeLiftEnv, ast) in
  match generateTypeDecls typeLiftEnv with (generateEnv, typeTops) in

  -- Replace auxilliary accelerate terms in the AST by eliminating
  -- the let-expressions (only used in the accelerate AST) and adding
  -- data conversion of parameters and result.
  match replaceAccelerate accelerateData generateEnv ast
  with (recordDeclTops, ast) in

  -- Generate the OCaml AST (with externals support)
  let env : GenerateEnv =
    chooseExternalImpls (externalGetSupportedExternalImpls ()) generateEnv ast
  in
  let exprTops = generateTops env ast in
  let syslibs =
    setOfSeq cmpString
      (map (lam x : (String, String). x.0) (externalListOcamlPackages ()))
  in
  match collectLibraries env.exts syslibs with (libs, clibs) in

  -- Add an external declaration of a C function in the OCaml AST,
  -- for each accelerate term.
  let externalTops = getExternalCDeclarations accelerateData in

  let ocamlTops = join [externalTops, recordDeclTops, typeTops, exprTops] in

  let buildOptions = {
    debugGenerate = options.debugGenerate,
    output = options.output,
    file = file,
    libs = libs,
    clibs = clibs,
    ocamlTops = ocamlTops,
    acceleratedCode = gpuResult
  } in
  buildAccelerated buildOptions

let compileAccelerate = lam files. lam options : Options. lam args.
  use PMExprCompile in
  iter (compileAccelerated options) files
