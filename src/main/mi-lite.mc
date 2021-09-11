-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The mi-lite is a lightweight compiler using the minimal amount of code
-- needed for bootstrapping. It is used in place of mi in the first
-- bootstrapping stage to speed up compile times.

include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "ocaml/compile.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"

lang MCoreLiteCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprUtestTrans +
  OCamlPrettyPrint + OCamlTypeDeclGenerate + OCamlGenerate +
  OCamlGenerateExternalNaive
end

-- NOTE(larshum, 2021-03-22): This does not work for Windows file paths.
let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let collectLibraries = lam extNameMap : ExternalNameMap.
  let f = lam libs. lam lib. setInsert lib libs in
  let g =
    lam libs. lam impl : ExternalImpl. foldl f libs impl.libraries
  in
  let h = lam libs. lam. lam impls. foldl g libs impls in
  let libs =
    mapFoldWithKey h (setEmpty cmpString) extNameMap
  in
  setToSeq libs

let ocamlCompile : Options -> [String] -> String -> String -> Unit =
  lam options. lam libs. lam sourcePath. lam ocamlProg.
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

let ocamlCompileAst =
  lam options : Options. lam sourcePath. lam ast. lam debugTypeAnnotHook.
  lam debugGenerateHook. lam exitBeforeHook.
  use MCoreLiteCompile in
  let ast = typeAnnot ast in
  let ast = removeTypeAscription ast in

  -- If option --debug-type-annot, then pretty-print the AST
  debugTypeAnnotHook ast;

  -- Translate the MExpr AST into an OCaml AST
  match typeLift ast with (env, ast) then
    match generateTypeDecl env ast with (env, ast) then
      let env : GenerateEnv =
        chooseExternalImpls globalExternalImplsMap env ast
      in
      let ast = generate env ast in

      -- Collect external library dependencies
      let libs = collectLibraries env.exts in

      let ocamlProg = expr2str ast in

      -- Print the AST after code generation
      debugGenerateHook ocamlProg;

      -- If option --exit-before, exit the program here
      exitBeforeHook ();

      -- Compile OCamlAst
      ocamlCompile options libs sourcePath ocamlProg
    else never
  else never

let compile : Options -> String -> Unit = lam options. lam file.
  use MCoreLiteCompile in
  let ast = parseMCoreFile [] file in
  let ast = utestStrip ast in
  let ast = symbolize ast in
  ocamlCompileAst options file ast (lam. ()) (lam. ()) (lam. ())

mexpr

let printMenu = lam. print "Usage: mi-lite [0|1] file" in

if neqi (length argv) 3 then
  printMenu ()
else match get argv 1 with "0" then
  let options = {options with disableOptimizations = true} in
  compile options (get argv 2)
else match get argv 1 with "1" then
  compile options (get argv 2)
else printMenu ()
