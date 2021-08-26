-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/utesttrans.mc"
include "mexpr/tuning/decision-points.mc"
include "mexpr/tuning/tune.mc"
include "ocaml/ast.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "ocaml/external-includes.mc"
include "ocaml/sys.mc"

lang MCoreCompile =
  BootParser +
  MExprHoles +
  MExprSym + MExprTypeAnnot + MExprUtestTrans +
  OCamlPrettyPrint + OCamlTypeDeclGenerate + OCamlGenerate +
  OCamlGenerateExternalNaive
end

let pprintMcore = lam ast.
  use MExprPrettyPrint in
  expr2str ast

let pprintOcaml = lam ast.
  use OCamlPrettyPrint in
  expr2str ast

let generateTests = lam ast. lam testsEnabled.
  use MCoreCompile in
  if testsEnabled then
    let ast = symbolize ast in
    let ast = typeAnnot ast in
    let ast = removeTypeAscription ast in
    utestGen ast
  else
    let symEnv = symEnvEmpty in
    (symEnv, utestStrip ast)

let collectLibraries = lam extNameMap : ExternalNameMap.
  let f = lam libs. lam lib. setInsert lib libs in
  let g =
    lam libs. lam impl :  ExternalImpl. foldl f libs impl.libraries
  in
  let h = lam libs. lam. lam impls. foldl g libs impls in
  let libs =
    mapFoldWithKey h (setEmpty cmpString) extNameMap
  in
  setToSeq libs

-- NOTE(larshum, 2021-03-22): This does not work for Windows file paths.
let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let insertTunedOrDefaults = lam ast. lam file.
  use MCoreCompile in
  if options.useTuned then
    let tuneFile = tuneFileName file in
    if fileExists tuneFile then
      let table = tuneReadTable tuneFile in
      let ast = symbolize ast in
      let ast = normalizeTerm ast in
      insert [] table ast
    else error (join ["Tune file ", tuneFile, " does not exist"])
  else default ast

let ocamlCompile =
  lam options : Options. lam libs. lam sourcePath. lam ocamlProg.
  let compileOptions : CompileOptions =
    {
      (if options.disableOptimizations then
        {defaultCompileOptions with optimize = false}
       else defaultCompileOptions)

       with libraries = libs
    }
  in
  let p : CompileResult = ocamlCompileWithConfig compileOptions ocamlProg in
  let destinationFile = filenameWithoutExtension (filename sourcePath) in
  sysMoveFile p.binaryPath destinationFile;
  sysChmodWriteAccessFile destinationFile;
  p.cleanup ();
  destinationFile

let ocamlCompileAst = lam options : Options. lam sourcePath. lam mexprAst.
  use MCoreCompile in

  -- If option --test, then generate utest runner calls. Otherwise strip away
  -- all utest nodes from the AST.
  match generateTests mexprAst options.runTests with (symEnv, ast) then

    -- Re-symbolize the MExpr AST and re-annotate it with types
    let ast = symbolizeExpr symEnv ast in
    let ast = typeAnnot ast in

    -- If option --debug-type-annot, then pretty print the AST
    (if options.debugTypeAnnot then printLn (pprintMcore ast) else ());

    -- Translate the MExpr AST into an OCaml AST
    match typeLift ast with (env, ast) then
      match generateTypeDecl env ast with (env, ast) then
        let env : GenerateEnv =
          chooseExternalImpls globalExternalImplsMap env ast
        in
        let ast = generate env ast in

        -- Collect external library dependencies
        let libs = collectLibraries env.exts in

        let ocamlProg = pprintOcaml ast in

        -- Print the AST after code generation
        (if options.debugGenerate then printLn ocamlProg else ());

        -- Compile OCaml AST
        if options.exitBefore then exit 0
        else ocamlCompile options libs sourcePath ocamlProg

      else never
    else never
  else never

-- Main function for compiling a program
-- files: a list of files
-- options: the options structure to the main program
-- args: the program arguments to the executed program, if any
let compile = lam files. lam options : Options. lam args.
  use MCoreCompile in
  let compileFile = lam file.
    let ast = makeKeywords [] (parseMCoreFile decisionPointsKeywords file) in

    -- Insert tuned values, or use default values if no .tune file present
    let ast = insertTunedOrDefaults ast file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (pprintMcore ast) else ());

    -- Compile MExpr AST
    ocamlCompileAst options file ast
  in
  iter compileFile files
