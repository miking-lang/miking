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

let collectlibraries : ExternalNameMap -> ([String], [String])
= lam extNameMap.
  let f = lam s. lam str. setInsert str s in
  let g = lam acc : (Set String, Set String). lam impl :  ExternalImpl.
    match acc with (libs, clibs) then
      (foldl f libs impl.libraries, foldl f clibs impl.cLibraries)
    else never
  in
  let h = lam acc. lam. lam impls. foldl g acc impls in
  match mapFoldWithKey h (setEmpty cmpString, setEmpty cmpString) extNameMap
  with (libs, clibs) then (setToSeq libs, setToSeq clibs)
  else never

let ocamlCompile : Options -> [String] -> [String] -> String -> String -> String =
  lam options. lam libs. lam clibs. lam sourcePath. lam ocamlProg.
  let compileOptions : CompileOptions =
    let opts = {{
        defaultCompileOptions
        with libraries = libs }
        with cLibraries = clibs }
    in
    if options.disableOptimizations then
      { opts with optimize = false}
    else opts
  in
  let p : CompileResult = ocamlCompileWithConfig compileOptions ocamlProg in
  let destinationFile = filenameWithoutExtension (filename sourcePath) in
  sysMoveFile p.binaryPath destinationFile;
  sysChmodWriteAccessFile destinationFile;
  p.cleanup ();
  destinationFile

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
      match collectlibraries env.exts with (libs, clibs) then
        let ocamlProg = expr2str ast in

        -- Print the AST after code generation
        debugGenerateHook ocamlProg;

        -- If option --exit-before, exit the program here
        exitBeforeHook ();

        -- Compile OCamlAst
        ocamlCompile options libs clibs sourcePath ocamlProg
      else never
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
