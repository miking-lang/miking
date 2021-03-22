
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "ocaml/ast.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"

lang MCoreCompile =
  BootParser +
  MExprSym + MExprTypeAnnot +
  OCamlPrettyPrint + OCamlTypeDeclGenerate + OCamlGenerate + OCamlObjWrap
end

-- Hack for pretty-printing the preamble and inserting it into the beginning of
-- the OCaml file, after all type definitions.
let _preambleStr =
  use OCamlPrettyPrint in
  let str = expr2str (bind_ _preamble (int_ 0)) in
  subsequence str 0 (subi (length str) 1)

recursive let _withPreamble = lam expr.
  use OCamlAst in
  match expr with OTmVariantTypeDecl t then
    OTmVariantTypeDecl {t with inexpr = _withPreamble t.inexpr}
  else
    OTmPreambleText {text = _preambleStr, inexpr = expr}
end

let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let ocamlCompile = lam sourcePath. lam ocamlAst.
  use MCoreCompile in
  let p = ocamlCompile (expr2str ocamlAst) in
  let destinationFile = filenameWithoutExtension (filename sourcePath) in
  phMoveFile p.binaryPath destinationFile;
  phChmodWriteAccessFile destinationFile

let compile = lam files. lam options.
  use MCoreCompile in
  let compileFile = lam file.
    let ast = parseMCoreFile file in
    let names = map (lam x. match x with (s,_) then nameSym s else never) builtin in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then print (expr2str ast) else ());

    -- Symbolize the MExpr AST and annotate it with types
    let ast = symbolizeExpr (symVarNameEnv names) ast in
    let ast = typeAnnot ast in

    -- Translate the MExpr AST into an OCaml AST
    let ocamlAst =
      match generateTypeDecl ast with (env, ast) then
        let ast = generate env ast in
        let ast = objWrap ast in
        _withPreamble ast
      else never
    in

    -- Compile OCaml AST
    ocamlCompile file ocamlAst
  in
  map compileFile files
