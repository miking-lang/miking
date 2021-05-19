
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "ocaml/ast.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "ocaml/external-includes.mc"

lang MCoreCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprUtestTrans +
  OCamlPrettyPrint + OCamlTypeDeclGenerate + OCamlGenerate +
  OCamlGenerateExternalNaive + OCamlObjWrap
end

let pprintMcore = lam ast.
  use MExprPrettyPrint in
  expr2str ast

let pprintOcaml = lam ast.
  use OCamlPrettyPrint in
  expr2str ast

-- Hack for pretty-printing the preamble and inserting it into the beginning of
-- the OCaml file, after all type definitions.
let _preambleStr = lam.
  let str = pprintOcaml (bind_ _preamble (int_ 0)) in
  subsequence str 0 (subi (length str) 1)

recursive let _withPreamble = lam expr.
  use OCamlAst in
  match expr with OTmVariantTypeDecl t then
    OTmVariantTypeDecl {t with inexpr = _withPreamble t.inexpr}
  else
    OTmPreambleText {text = _preambleStr (), inexpr = expr}
end

let generateTests = lam ast. lam testsEnabled.
  use MCoreCompile in
  if testsEnabled then
    let ast = symbolize ast in
    let ast = typeAnnot ast in
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
  p.cleanup ()

-- Main function for compiling a program
-- files: a list of files
-- options: the options structure to the main program
-- args: the program arguments to the executed program, if any
let compile = lam files. lam options : Options. lam args.
  use MCoreCompile in
  let compileFile = lam file.
    let ast = parseMCoreFile [] file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (pprintMcore ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (symEnv, ast) then

      -- Re-symbolize the MExpr AST and re-annotate it with types
      let ast = symbolizeExpr symEnv ast in
      let ast = typeAnnot ast in

      -- If option --debug-type-annot, then pretty print the AST
      (if options.debugTypeAnnot then printLn (pprintMcore ast) else ());

      -- Translate the MExpr AST into an OCaml AST and Compile
      match typeLift ast with (env, ast) then
        match generateTypeDecl env ast with (env, ast) then
          let env : GenerateEnv = env in
          let extEnv : ExternalEnv =
            let env = externalInitialEnv env.aliases env.constrs in
            chooseExternalImpls globalExternalImplsMap env ast
          in
          let ast = generateExternals extEnv ast in
          let ast = generate env ast in
          let ast = objWrap ast in
          let ast = _withPreamble ast in

          -- Collect external library dependencies
          let libs = collectLibraries extEnv.usedImpls in

          let ocamlProg = pprintOcaml ast in

          -- Print the AST after code generation
          (if options.debugGenerate then printLn ocamlProg else ());

          -- Compile OCaml AST
          if options.exitBefore then exit 0
          else ocamlCompile options libs file ocamlProg

        else never
      else never
    else never
  in
  iter compileFile files
