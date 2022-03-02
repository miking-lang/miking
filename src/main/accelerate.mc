include "c/ast.mc"
include "c/pprint.mc"
include "cuda/compile.mc"
include "cuda/constant-app.mc"
include "cuda/memory.mc"
include "cuda/pmexpr-ast.mc"
include "cuda/pprint.mc"
include "cuda/kernel-translate.mc"
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
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "options.mc"
include "sys.mc"
include "pmexpr/ast.mc"
include "pmexpr/c-externals.mc"
include "pmexpr/demote.mc"
include "pmexpr/extract.mc"
include "pmexpr/nested-accelerate.mc"
include "pmexpr/parallel-rewrite.mc"
include "pmexpr/recursion-elimination.mc"
include "pmexpr/replace-accelerate.mc"
include "pmexpr/rules.mc"
include "pmexpr/tailrecursion.mc"
include "pmexpr/utest-size-constraint.mc"
include "pmexpr/well-formed.mc"
include "parse.mc"

lang PMExprCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprRemoveTypeAscription + MExprUtestTrans +
  PMExprAst + MExprANF + PMExprDemote + PMExprRewrite + PMExprTailRecursion +
  PMExprParallelPattern + PMExprCExternals + MExprLambdaLift + MExprCSE +
  PMExprRecursionElimination + PMExprExtractAccelerate +
  PMExprReplaceAccelerate + PMExprNestedAccelerate +
  PMExprUtestSizeConstraint + PMExprWellFormed +
  OCamlGenerate + OCamlTypeDeclGenerate
end

lang MExprFutharkCompile =
  FutharkGenerate + FutharkDeadcodeElimination + FutharkSizeParameterize +
  FutharkCWrapper + FutharkRecordParamLift + FutharkForEachRecordPattern +
  FutharkAliasAnalysis
end

lang MExprCudaCompile =
  CudaPMExprAst + CudaMemoryManagement + MExprTypeLift + SeqTypeTypeLift +
  CudaCompile + CudaKernelTranslate + CudaPrettyPrint + CudaCWrapper +
  CudaWellFormed + CudaConstantApp
end

type AccelerateHooks a b = {
  generateGpuCode : Map Name AccelerateData -> Expr -> (a, b),
  buildAccelerated : Options -> String -> [Top] -> a -> b -> Unit
}

let parallelKeywords = [
  "accelerate",
  "map2",
  "parallelFlatten",
  "parallelReduce"
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
  let ast = generateProgram entryPoints ast in
  let ast = liftRecordParameters ast in
  let ast = useRecordPatternInForEach ast in
  let ast = aliasAnalysis ast in
  let ast = deadcodeElimination ast in
  parameterizeSizes ast

let cudaTranslation : Options -> Map Name AccelerateData -> Expr -> (CuProg, CuProg) =
  lam options. lam accelerateData. lam ast.
  use MExprCudaCompile in
  wellFormed ast;
  let ast = constantAppToExpr ast in
  match toCudaPMExpr accelerateData ast with (cudaMemEnv, ast) in
  match typeLift ast with (typeEnv, ast) in
  let opts : CompileCOptions = {
    use32BitInts = options.use32BitIntegers,
    use32BitFloats = options.use32BitFloats
  } in
  match compile typeEnv opts ast with (_, types, tops, _, _) in
  let ctops = join [types, tops] in
  let ccEnv = {compileCEnvEmpty opts with typeEnv = typeEnv} in
  match translateCudaTops cudaMemEnv ccEnv ctops with (wrapperMap, cudaTops) in
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

let duneBuildBase = lam ocamloptFlags.
  strJoin "\n" [
    "(env",
    "  (dev",
    "    (flags (:standard -w -a))",
    "    (ocamlc_flags (-without-runtime))))",
    "(executable",
    "  (name program)",
    "  (libraries boot)"]

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

let buildConfigFutharkCPU : Unit -> (String, String) = lam.
  let dunefile = strJoin "\n" [
    duneBuildBase (),
    duneFutharkCFiles ()] in
  let makefile = strJoin "\n" [
    futharkDuneBuildMakeRule (),
    futharkCPUBuildMakeRule ()] in
  (dunefile, makefile)

let buildConfigFutharkGPU : Unit -> (String, String) = lam.
  let dunefile = strJoin "\n" [
    duneBuildBase (),
    "  (link_flags -cclib -lcuda -cclib -lcudart -cclib -lnvrtc)",
    duneFutharkCFiles ()] in
  let makefile = strJoin "\n" [
    "export LIBRARY_PATH=/usr/local/cuda/lib64",
    "export LD_LIBRARY_PATH=/usr/local/cuda/lib64/",
    "export CPATH=/usr/local/cuda/include",
    futharkDuneBuildMakeRule (),
    futharkGPUBuildMakeRule ()] in
  (dunefile, makefile)

let buildConfigCuda : String -> (String, String) = lam dir.
  let dunefile = strJoin "\n" [
    duneBuildBase (),
    "  (link_flags -I ", dir, " -cclib -lgpu -cclib -lcudart -cclib -lstdc++))"] in
  let makefile = strJoin "\n" [
    "export LIBRARY_PATH=/usr/local/cuda/lib64",
    "export LD_LIBRARY_PATH=/usr/local/cuda/lib64/",
    "export CPATH=/usr/local/cuda/include",
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

let buildFuthark : Options -> String -> [Top] -> CProg -> FutProg -> Unit =
  lam options. lam sourcePath. lam ocamlTops. lam wrapperProg. lam futharkProg.
  match
    if options.cpuOnly then buildConfigFutharkCPU ()
    else buildConfigFutharkGPU ()
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
  lam lprog. lam rprog.
  use MExprCudaCompile in
  match lprog with CuPProg {includes = lincludes, tops = ltops} in
  match rprog with CuPProg {includes = rincludes, tops = rtops} in
  CuPProg {includes = concat lincludes rincludes, tops = concat ltops rtops}

let buildCuda : Options -> String -> [Top] -> CudaProg -> CudaProg -> Unit =
  lam options. lam sourcePath. lam ocamlTops. lam wrapperProg. lam cudaProg.
  let cudaProg = mergePrograms cudaProg wrapperProg in
  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  match
    if options.cpuOnly then
      error "CUDA backend does not support CPU compilation"
    else buildConfigCuda dir
  with (dunefile, makefile) in
  writeFiles dir [
    ("program.ml", pprintOCamlTops ocamlTops),
    ("program.mli", ""),
    ("gpu.cu", pprintCudaAst cudaProg),
    ("dune", dunefile),
    ("dune-project", "(lang dune 2.0)"),
    ("Makefile", makefile)];
  buildBinaryUsingMake sourcePath td

let compileAccelerated : Options -> AccelerateHooks -> String -> Unit =
  lam options. lam hooks. lam file.
  use PMExprCompile in
  let ast = parseParseMCoreFile {
    keepUtests = true,
    pruneExternalUtests = false,
    pruneExternalUtestsWarning = false,
    findExternalsExclude = false,
    keywords = parallelKeywords
  } file in
  let ast = makeKeywords [] ast in

  let ast = symbolizeExpr keywordsSymEnv ast in
  let ast = typeAnnot ast in
  let ast = removeTypeAscription ast in

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

  -- Detect patterns in the accelerate AST to eliminate recursion. The
  -- result is a PMExpr AST.
  let pmexprAst = patternTransformation accelerateAst in

  -- Perform validation of the produced PMExpr AST to ensure it is valid
  -- in terms of the well-formed rules. If it is found to violate these
  -- constraints, an error is reported.
  validatePMExprAst accelerateIds pmexprAst;

  -- Translate the PMExpr AST into a representation of the GPU code and the
  -- wrapper code.
  match hooks.generateGpuCode accelerated pmexprAst with (gpuProg, wrapperProg) in

  -- Eliminate all utests in the MExpr AST
  let ast = utestStrip ast in

  -- Construct a sequential version of the AST where parallel constructs have
  -- been demoted to sequential equivalents
  let ast = demoteParallel ast in

  match typeLift ast with (env, ast) in
  match generateTypeDecls env with (env, typeTops) in

  -- Replace auxilliary accelerate terms in the AST by eliminating
  -- the let-expressions (only used in the accelerate AST) and adding
  -- data conversion of parameters and result.
  let ast = replaceAccelerate accelerated ast in

  -- Generate the OCaml AST
  let exprTops = generateTops env ast in

  -- Add an external declaration of a C function in the OCaml AST,
  -- for each accelerate term.
  let externalTops = getExternalCDeclarations accelerated in

  let ocamlTops = join [externalTops, typeTops, exprTops] in
  hooks.buildAccelerated options file ocamlTops wrapperProg gpuProg

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
