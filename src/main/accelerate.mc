include "c/ast.mc"
include "c/pprint.mc"
include "cuda/compile.mc"
include "cuda/constant-app.mc"
include "cuda/gpu-utils.mc"
include "cuda/lang-fix.mc"
include "cuda/pmexpr-ast.mc"
include "cuda/pmexpr-compile.mc"
include "cuda/pmexpr-pprint.mc"
include "cuda/pprint.mc"
include "cuda/kernel-translate.mc"
include "cuda/tensor-memory.mc"
include "cuda/well-formed.mc"
include "cuda/wrapper.mc"
include "futhark/alias-analysis.mc"
include "futhark/deadcode.mc"
include "futhark/for-each-record-pat.mc"
include "futhark/generate.mc"
include "futhark/pprint.mc"
include "futhark/record-lift.mc"
include "futhark/size-parameterize.mc"
include "futhark/wrapper.mc"
include "mexpr/boot-parser.mc"
include "mexpr/cse.mc"
include "mexpr/lamlift.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/resolve-alias.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/type-lift.mc"
include "mexpr/utesttrans.mc"
include "ocaml/generate.mc"
include "ocaml/mcore.mc"
include "ocaml/pprint.mc"
include "options.mc"
include "sys.mc"
include "pmexpr/ast.mc"
include "pmexpr/c-externals.mc"
include "pmexpr/copy-analysis.mc"
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
include "parse.mc"

lang PMExprCompile =
  BootParser +
  MExprSym + MExprTypeCheck + MExprRemoveTypeAscription + MExprResolveAlias +
  MExprUtestTrans + PMExprAst + MExprANF + PMExprDemote + PMExprRewrite +
  PMExprTailRecursion + PMExprParallelPattern + PMExprCExternals +
  MExprLambdaLift + MExprCSE + PMExprRecursionElimination +
  PMExprExtractAccelerate + PMExprUtestSizeConstraint +
  PMExprReplaceAccelerate + PMExprNestedAccelerate + PMExprWellFormed +
  OCamlGenerate + OCamlTypeDeclGenerate + OCamlGenerateExternalNaive +
  PMExprCopyAnalysis
end

lang MExprFutharkCompile =
  FutharkGenerate + FutharkDeadcodeElimination + FutharkSizeParameterize +
  FutharkCWrapper + FutharkRecordParamLift + FutharkForEachRecordPattern +
  FutharkAliasAnalysis
end

lang MExprCudaCompile =
  MExprUtestTrans + MExprRemoveTypeAscription + CudaPMExprAst +
  CudaPMExprCompile + MExprTypeLift + TypeLiftAddRecordToEnvUnOrdered +
  SeqTypeNoStringTypeLift + TensorTypeTypeLift + CudaCompile + CudaKernelTranslate +
  CudaPrettyPrint + CudaCWrapper + CudaWellFormed + CudaConstantApp +
  CudaTensorMemory + CudaLanguageFragmentFix
end

type AccelerateHooks a b = {
  generateGpuCode : Map Name AccelerateData -> Expr -> (a, b),
  buildAccelerated : Options -> String -> [Top] -> a -> b -> Unit
}

let parallelKeywords = [
  "accelerate",
  "map2",
  "parallelFlatten",
  "parallelReduce",
  "seqLoop",
  "seqLoopAcc",
  "parallelLoop",
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

let pprintOCamlTops : [Top] -> String = lam tops.
  use OCamlPrettyPrint in
  pprintOcamlTops tops

let pprintFutharkAst : FutProg -> String = lam ast.
  use FutharkPrettyPrint in
  printFutProg ast

let pprintPMExprAst : Expr -> String = lam ast.
  use PMExprPrettyPrint in
  expr2str ast

let pprintCudaPMExprAst : Expr -> String = lam ast.
  use CudaPMExprPrettyPrint in
  expr2str ast

let pprintCAst : CPProg -> String = lam ast.
  use CPrettyPrint in
  use CProgPrettyPrint in
  printCProg [] ast

let pprintCudaAst : CuPProg -> String = lam ast.
  use CudaPrettyPrint in
  printCudaProg [] ast

let patternTransformation : Expr -> Expr = lam ast.
  use PMExprCompile in
  let ast = replaceUtestsWithSizeConstraint ast in
  let ast = rewriteTerm ast in
  let ast = tailRecursive ast in
  let ast = cseGlobal ast in
  let ast = normalizeTerm ast in
  let ast = parallelPatternRewrite parallelPatterns ast in
  eliminateRecursion ast

let validatePMExprAst : Set Name -> Expr -> () = lam accelerateIds. lam ast.
  use PMExprCompile in
  reportNestedAccelerate accelerateIds ast;
  wellFormed ast

let futharkTranslation : Set Name -> Expr -> FutProg =
  lam entryPoints. lam ast.
  use MExprFutharkCompile in
  let ast = patternTransformation ast in
  validatePMExprAst entryPoints ast;
  let ast = generateProgram entryPoints ast in
  let ast = liftRecordParameters ast in
  let ast = useRecordPatternInForEach ast in
  let ast = aliasAnalysis ast in
  let ast = deadcodeElimination ast in
  parameterizeSizes ast

let cudaTranslation : Options -> Map Name AccelerateData -> Expr -> (CuProg, CuProg) =
  lam options. lam accelerateData. lam ast.
  use MExprCudaCompile in
  let ast = fixLanguageFragmentSemanticFunction ast in
  let ast = constantAppToExpr ast in
  let ast = normalizeTerm ast in
  let ast = utestStrip ast in
  wellFormed ast;
  let ast = toCudaPMExpr ast in
  match typeLift ast with (typeEnv, ast) in
  let ast = removeTypeAscription ast in
  let opts : CompileCOptions = {
    use32BitInts = options.use32BitIntegers,
    use32BitFloats = options.use32BitFloats
  } in
  match compile typeEnv opts ast with (ccEnv, types, tops, _, _) in
  let ctops = join [types, tops] in
  match translateCudaTops accelerateData ccEnv ctops
  with (wrapperMap, cudaTops) in
  let cudaTops = addCudaTensorMemoryManagement cudaTops in
  let wrapperProg = generateWrapperCode accelerateData wrapperMap ccEnv in
  (CuPProg { includes = cudaIncludes, tops = cudaTops }, wrapperProg)

let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let duneBuildBase : [String] -> [String] -> String =
  lam libs. lam clibs.
  let libstr = strJoin " " (distinct eqString (cons "boot" libs)) in
  let flagstr =
    let clibstr =
      strJoin " " (map (concat "-cclib -l") (distinct eqString clibs))
    in
    concat ":standard -w -a " clibstr
  in
  strJoin "\n" [
    "(env",
    "  (dev",
    "    (flags (", flagstr, "))",
    "    (ocamlc_flags (-without-runtime))))",
    "(executable",
    "  (name program)",
    "  (libraries ", libstr, ")"]

let futharkDuneBuildMakeRule = lam.
  strJoin "\n" [
    "program.exe: program.ml wrap.c gpu.c",
    "\tdune build $@"]

let futharkGPUBuildMakeRule = lam.
  strJoin "\n" [
    "gpu.c gpu.h: gpu.fut",
    "\tfuthark cuda --library $^"]

let futharkCPUBuildMakeRule = lam.
  strJoin "\n" [
    "gpu.c gpu.h: gpu.fut",
    "\tfuthark multicore --library $^"]

let duneFutharkCFiles = lam. "(foreign_stubs (language c) (names gpu wrap)))"

let buildConfigFutharkCPU : [String] -> [String] -> (String, String) =
  lam libs. lam clibs.
  let dunefile = strJoin "\n" [
    duneBuildBase libs clibs,
    duneFutharkCFiles ()] in
  let makefile = strJoin "\n" [
    futharkDuneBuildMakeRule (),
    futharkCPUBuildMakeRule ()] in
  (dunefile, makefile)

let buildConfigFutharkGPU : [String] -> [String] -> (String, String) =
  lam libs. lam clibs.
  let dunefile = strJoin "\n" [
    duneBuildBase libs clibs,
    "  (link_flags -cclib -lcuda -cclib -lcudart -cclib -lnvrtc)",
    duneFutharkCFiles ()] in
  let makefile = strJoin "\n" [
    futharkDuneBuildMakeRule (),
    futharkGPUBuildMakeRule ()] in
  (dunefile, makefile)

let buildConfigCuda : String -> [String] -> [String] -> (String, String) =
  lam dir. lam libs. lam clibs.
  let dunefile = strJoin "\n" [
    duneBuildBase libs clibs,
    "  (link_flags -I ", dir, " -cclib -lgpu -cclib -lcudart -cclib -lstdc++))"] in
  let makefile = strJoin "\n" [
    "program.exe: program.ml libgpu.a",
    "\tdune build $@",
    "libgpu.a: gpu.cu",
    "\tnvcc -I`ocamlc -where` $^ -lib -O3 -o $@"] in
  (dunefile, makefile)

let writeFiles : String -> [(String, String)] -> Unit = lam dir. lam fileStrs.
  let tempfile = lam f. sysJoinPath dir f in
  iter
    (lam fstr : (String, String).
      match fstr with (filename, text) in
      writeFile (tempfile filename) text)
    fileStrs

-- TODO(larshum, 2021-09-17): Remove dependency on Makefile. For now, we use
-- it because dune cannot set environment variables.
let buildBinaryUsingMake : String -> String -> Unit =
  lam sourcePath. lam td.
  let dir = sysTempDirName td in
  let r = sysRunCommand ["make"] "" dir in
  (if neqi r.returncode 0 then
    print (join ["Make failed:\n\n", r.stderr]);
    sysTempDirDelete td;
    exit 1
  else ());
  let binPath = sysJoinPath dir "_build/default/program.exe" in
  let destFile = filenameWithoutExtension (filename sourcePath) in
  sysMoveFile binPath destFile;
  sysChmodWriteAccessFile destFile;
  sysTempDirDelete td ();
  ()

let buildFuthark : Options -> String -> [String] -> [String] -> [Top] -> CProg
                -> FutProg -> Unit =
  lam options. lam sourcePath. lam libs. lam clibs. lam ocamlTops.
  lam wrapperProg. lam futharkProg.
  match
    if options.cpuOnly then buildConfigFutharkCPU libs clibs
    else buildConfigFutharkGPU libs clibs
  with (dunefile, makefile) in
  let td = sysTempDirMake () in
  writeFiles (sysTempDirName td) [
    ("program.ml", pprintOCamlTops ocamlTops),
    ("program.mli", ""),
    ("wrap.c", pprintCAst wrapperProg),
    ("gpu.fut", pprintFutharkAst futharkProg),
    ("dune-project", "(lang dune 2.0)"),
    ("dune", dunefile),
    ("Makefile", makefile)];
  buildBinaryUsingMake sourcePath td

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

let buildCuda : Options -> String -> [String] -> [String] -> [Top] -> CudaProg
             -> CudaProg -> Unit =
  lam options. lam sourcePath. lam libs. lam clibs. lam ocamlTops.
  lam wrapperProg. lam cudaProg.
  let cudaProg = mergePrograms cudaProg wrapperProg in
  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  match
    if options.cpuOnly then
      error "CUDA backend does not support CPU compilation"
    else buildConfigCuda dir libs clibs
  with (dunefile, makefile) in
  writeFiles dir [
    ("program.ml", pprintOCamlTops ocamlTops),
    ("program.mli", ""),
    ("gpu.cu", pprintCudaAst cudaProg),
    ("gpu-utils.cu", gpu_utils_code),
    ("dune", dunefile),
    ("dune-project", "(lang dune 2.0)"),
    ("Makefile", makefile)];
  (if options.debugGenerate then
    printLn (join ["Output files saved at '", dir, "'"]);
    exit 0
  else ());
  buildBinaryUsingMake sourcePath td

-- NOTE(larshum, 2022-03-30): For now, we use a very simple solution which runs
-- the compilation up until the well-formedness checks.
let checkWellFormedCuda : Expr -> () = lam ast.
  match
    use PMExprCompile in
    let ast = symbolizeExpr keywordsSymEnv ast in
    let ast = typeCheck ast in
    let ast = removeTypeAscription ast in
    match addIdentifierToAccelerateTerms ast with (accelerated, ast) in
    match liftLambdasWithSolutions ast with (solutions, ast) in
    let accelerateIds : Set Name = mapMap (lam. ()) accelerated in
    let accelerateAst = extractAccelerateTerms accelerateIds ast in
    eliminateDummyParameter solutions accelerated accelerateAst
  with (accelerateData, ast) in
  use MExprCudaCompile in
  let ast = fixLanguageFragmentSemanticFunction ast in
  let ast = constantAppToExpr ast in
  let ast = normalizeTerm ast in
  let ast = utestStrip ast in
  wellFormed ast

let compileAccelerated : Options -> AccelerateHooks -> String -> Unit =
  lam options. lam hooks. lam file.
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
  let ast = resolveAliases ast in

  -- Translate accelerate terms into functions with one dummy parameter, so
  -- that we can accelerate terms without free variables and so that it is
  -- lambda lifted.
  match addIdentifierToAccelerateTerms ast with (accelerated, ast) in

  -- Perform lambda lifting and return the free variable solutions
  match liftLambdasWithSolutions ast with (solutions, ast) in

  -- Extract the accelerate AST
  let accelerateIds : Set Name = mapMap (lam. ()) accelerated in
  let accelerateAst = extractAccelerateTerms accelerateIds ast in

  -- Eliminate the dummy parameter in functions of accelerate terms with at
  -- least one free variable parameter.
  match eliminateDummyParameter solutions accelerated accelerateAst
  with (accelerated, accelerateAst) in

  -- Perform analysis to find variables unused after the accelerate call.
  let accelerated = findUnusedAfterAccelerate accelerated ast in

  -- Translate the PMExpr AST into a representation of the GPU code and the
  -- wrapper code.
  match hooks.generateGpuCode accelerated accelerateAst with (gpuProg, wrapperProg) in

  -- Eliminate all utests in the MExpr AST
  let ast = utestStrip ast in

  -- Construct a sequential version of the AST where parallel constructs have
  -- been demoted to sequential equivalents
  let ast = demoteParallel ast in

  match typeLift ast with (typeLiftEnv, ast) in
  match generateTypeDecls typeLiftEnv with (generateEnv, typeTops) in

  -- Replace auxilliary accelerate terms in the AST by eliminating
  -- the let-expressions (only used in the accelerate AST) and adding
  -- data conversion of parameters and result.
  match replaceAccelerate accelerated generateEnv ast
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
  let externalTops = getExternalCDeclarations accelerated in

  let ocamlTops = join [externalTops, recordDeclTops, typeTops, exprTops] in
  hooks.buildAccelerated options file libs clibs ocamlTops wrapperProg gpuProg

let compileAccelerate = lam files. lam options : Options. lam args.
  use PMExprAst in
  let hooks =
    if options.runTests then
      error "Flag --test may not be used for accelerated code generation"
    else if options.accelerateCuda then
      { generateGpuCode = lam accelerateData : Map Name AccelerateData. lam ast : Expr.
          cudaTranslation options accelerateData ast
      , buildAccelerated = buildCuda}
    else if options.accelerateFuthark then
      { generateGpuCode = lam accelerateData : Map Name AccelerateData. lam ast : Expr.
          use MExprFutharkCompile in
          let accelerateIds = mapMap (lam. ()) accelerateData in
          let futharkProg = futharkTranslation accelerateIds ast in
          let wrapperProg = generateWrapperCode accelerateData in
          (futharkProg, wrapperProg)
      , buildAccelerated = buildFuthark}
    else
      error "Neither CUDA nor Futhark was chosen as acceleration target"
  in iter (compileAccelerated options hooks) files
