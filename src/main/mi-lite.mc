-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The mi-lite is a lightweight compiler with minimal dependencies intended to
-- be used solely for the first bootstrapping stage.

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

let compileOCaml : [String] -> String -> String -> Unit =
  lam libs. lam file. lam ocamlProgram.
  let options : CompileOptions = {defaultCompileOptions with libraries = libs} in
  let p : CompileResult = ocamlCompileWithConfig options ocamlProgram in
  let destinationFile = filenameWithoutExtension (filename file) in
  sysMoveFile p.binaryPath destinationFile;
  sysChmodWriteAccessFile destinationFile;
  p.cleanup ()

let compile : String -> Unit = lam file.
  use MCoreLiteCompile in
  let ast = parseMCoreFile [] file in
  let ast = utestStrip ast in
  let ast = symbolize ast in
  let ast = typeAnnot ast in
  let ast = removeTypeAscription ast in
  match typeLift ast with (env, ast) then
    match generateTypeDecl env ast with (env, ast) then
      let env : GenerateEnv =
        chooseExternalImpls globalExternalImplsMap env ast
      in
      let ast = generate env ast in
      let libs = collectLibraries env.exts in
      compileOCaml libs file (expr2str ast)
    else never
  else never

mexpr

if neqi (length argv) 2 then
  print "Usage: mi-lite file"
else
  compile (get argv 1)
