include "c/ast.mc"
include "c/pprint.mc"
include "futhark/deadcode.mc"
include "futhark/function-restrictions.mc"
include "futhark/generate.mc"
include "futhark/length-parameterize.mc"
include "futhark/pprint.mc"
include "futhark/record-inline.mc"
include "futhark/wrapper.mc"
include "mexpr/boot-parser.mc"
include "mexpr/cse.mc"
include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "mexpr/rewrite/extract.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/parallel-rewrite.mc"
include "mexpr/rewrite/recursion-elimination.mc"
include "mexpr/rewrite/replace-accelerate.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/tailrecursion.mc"
include "ocaml/c-externals.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "ocaml/sys.mc"

lang PMExprCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprUtestTrans + MExprParallelKeywordMaker +
  MExprANF + MExprRewrite + MExprTailRecursion + MExprParallelPattern +
  MExprLambdaLift + MExprCSE + PMExprRecursionElimination +
  PMExprExtractAccelerate + PMExprReplaceAccelerate + FutharkGenerate +
  FutharkFunctionRestrictions + FutharkRecordInline +
  FutharkDeadcodeElimination + FutharkLengthParameterize + FutharkCWrapper +
  OCamlCExternals + OCamlGenerate + OCamlTypeDeclGenerate
end

-- Pretty-printing of PMExpr terms. This is just used for debugging purposes.
lang PMExprPrettyPrint = MExprPrettyPrint + MExprParallelKeywordMaker
  sem isAtomic =
  | TmAccelerate _ -> false
  | TmParallelMap _ -> false
  | TmParallelMap2 _ -> false
  | TmParallelFlatMap _ -> false
  | TmParallelReduce _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmAccelerate t ->
    match printParen indent env t.e with (env, e) then
      (env, join ["accelerate ", e])
    else never
  | TmParallelMap t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelMap (", f, ") (", as, ")"])
      else never
    else never
  | TmParallelMap2 t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        match pprintCode indent env t.bs with (env, bs) then
          (env, join ["parallelMap2 (", f, ") (", as, ") (", bs, ")"])
        else never
      else never
    else never
  | TmParallelFlatMap t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelFlatMap (", f, ") (", as, ")"])
      else never
    else never
  | TmParallelReduce t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.ne with (env, ne) then
        match pprintCode indent env t.as with (env, as) then
          (env, join ["parallelReduce (", f, ") (", ne, ") (", as, ")"])
        else never
      else never
    else never
end

let parallelKeywords = [
  "accelerate",
  "parallelMap",
  "parallelMap2",
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

let pprintMExprAst : Expr -> String = lam ast.
  use MExprPrettyPrint in
  expr2str ast

let pprintPMExprAst : Expr -> String = lam ast.
  use PMExprPrettyPrint in
  expr2str ast

let pprintOCamlAst : Expr -> String = lam ast.
  use OCamlPrettyPrint in
  expr2str ast

let pprintFutharkAst : FutProg -> String = lam ast.
  use FutharkPrettyPrint in
  printFutProg ast

let pprintCAst : CPProg -> String = lam ast.
  use CPrettyPrint in
  use CProgPrettyPrint in
  printCProg [] ast

let patternTransformation : Expr -> Expr = lam ast.
  use PMExprCompile in
  let ast = rewriteTerm ast in
  let ast = tailRecursive ast in
  let ast = cseGlobal ast in
  let ast = normalizeTerm ast in
  let ast = parallelPatternRewrite parallelPatterns ast in
  eliminateRecursion ast

let futharkTranslation : Expr -> FutProg = lam entryPoints. lam ast.
  use PMExprCompile in
  let ast = generateProgram entryPoints ast in
  reportFutharkFunctionViolations ast;
  let ast = inlineRecords ast in
  let ast = deadcodeElimination ast in
  parameterizeLength ast

let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let compileAccelerated : String -> String -> String -> String -> Unit =
  lam sourcePath. lam ocamlProg. lam cProg. lam futharkProg.
  let dunefile = "
    (env
        (dev
          (flags (:standard -w -a))
          (ocamlc_flags (-without-runtime))))
    (executable
      (name program)
      (libraries boot)
      (link_flags -cclib -lcuda -cclib -lcudart -cclib -lnvrtc)
      (foreign_stubs (language c) (names gpu wrap)))
  " in
  let makefile = "
export LIBRARY_PATH=/usr/local/cuda/lib64
export LD_LIBRARY_PATH=/usr/local/cuda/lib64
export CPATH=/usr/local/cuda/include

program: program.ml wrap.c gpu.c
	dune build $@.exe

gpu.c gpu.h: gpu.fut
	futhark cuda --library $^
  " in

  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  let tempfile = lam f. sysJoinPath dir f in

  writeFile (tempfile "program.ml") ocamlProg;
  writeFile (tempfile "program.mli") "";
  writeFile (tempfile "wrap.c") cProg;
  writeFile (tempfile "gpu.fut") futharkProg;
  writeFile (tempfile "dune") dunefile;
  writeFile (tempfile "Makefile") makefile;

  let command = ["make"] in
  let r = sysRunCommand command "" dir in
  (if neqi r.returncode 0 then
    print (join ["Make failed:\n\n", r.stderr]);
    sysTempDirDelete td;
    exit 1
  else ());
  let binPath = tempfile "_build/default/program.exe" in
  let destinationFile = filenameWithoutExtension (filename sourcePath) in
  sysMoveFile binPath destinationFile;
  sysChmodWriteAccessFile destinationFile;
  sysTempDirDelete td ();
  ()

let compileGPU : String -> Unit = lam file.
  use PMExprCompile in
  let ast = parseMCoreFile parallelKeywords file in
  let ast = makeKeywords [] ast in
  let ast = symbolizeExpr keywordsSymEnv ast in
  let ast = utestStrip ast in
  let ast = typeAnnot ast in
  let ast = removeTypeAscription ast in
  match addIdentifierToAccelerateTerms ast with (accelerated, ast) then
    let accelerateIds : Set Name = mapMap (lam. ()) accelerated in
    let ast = liftLambdas ast in
    let accelerateAst = extractAccelerateTerms accelerateIds ast in
    printLn (pprintPMExprAst accelerateAst);

    -- Generate Futhark code
    let pmexprAst = patternTransformation accelerateAst in
    let futharkAst = futharkTranslation accelerateIds pmexprAst in
    let futharkProg = pprintFutharkAst futharkAst in

    -- Generate C wrapper code
    let cAst = generateWrapperCode accelerated in
    let cProg = pprintCAst cAst in

    -- Generate OCaml code
    match typeLift ast with (env, ast) then
      match generateTypeDecl env ast with (env, ast) then
        match replaceAccelerate accelerated ast with (externals, ast) then
          let ast = generate env ast in
          let ast = insertExternalCDeclarations externals ast in
          let ocamlProg = pprintOCamlAst ast in
          compileAccelerated file ocamlProg cProg futharkProg
        else never
      else never
    else never
  else never

let gpu = lam files. lam options : Options. lam args.
  iter compileGPU files
