
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "ocaml/ast.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"

lang MCoreCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprUtestTrans +
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

let ocamlCompile = lam sourcePath. lam ocamlAst.
  use MCoreCompile in
  let p = ocamlCompile (expr2str ocamlAst) in
  -- Imperfect solution: assumes the path contains at most one dot
  let pathWithoutExtension =
    match strLastIndex '.' sourcePath with Some idx then
      subsequence sourcePath 0 idx
    else sourcePath
  in
  phMoveFile p.binaryPath pathWithoutExtension;
  phChmodWriteAccessFile pathWithoutExtension

let compile = lam files. lam options.
  use MCoreCompile in
  let builtinNames = map (lam x. x.0) builtinEnv in
  let compileFile = lam file.
    let ast = parseMCoreFile file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    let ast =
      if options.runTests then
        -- Add type annotations as they are required by utestGen
        let ast = typeAnnot ast in
        utestGen ast
      else
        utestStrip ast
    in

    -- Symbolize the MExpr AST and annotate it with types
    let ast = symbolizeExpr (symVarNameEnv builtinNames) ast in
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
  iter compileFile files
