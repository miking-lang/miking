
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

lang MCoreGenerate =
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

recursive let _withPreamble = lam expr. lam options.
  use OCamlAst in
  match expr with OTmVariantTypeDecl t then
    OTmVariantTypeDecl {t with inexpr = _withPreamble t.inexpr options}
  else
    if options.excludeIntrinsicsPremable then
      OTmPreambleText {text = "\n", inexpr = expr}
    else
      OTmPreambleText {text = _preambleStr, inexpr = expr}
end

let ocamlPprint = lam ocamlAst.
  use MCoreGenerate in
  expr2str ocamlAst

let generateTests = lam ast. lam testsEnabled.
  use MCoreGenerate in
  if testsEnabled then
    let ast = symbolize ast in
    let ast = typeAnnot ast in
    utestGen ast
  else
    let symEnv = {symEnvEmpty with varEnv = builtinNameMap} in
    (symEnv, utestStrip ast)

let generateFile = lam file. lam options.
  use MCoreGenerate in
  let ast = parseMCoreFile file in

  -- If option --debug-parse, then pretty print the AST
  (if options.debugParse then printLn (expr2str ast) else ());

  -- If option --test, then generate utest runner calls. Otherwise strip away
  -- all utest nodes from the AST.
  match generateTests ast options.runTests with (symEnv, ast) then

    -- Re-symbolize the MExpr AST and re-annotate it with types
    let ast = symbolizeExpr symEnv ast in
    let ast = typeAnnot ast in

    -- Translate the MExpr AST into an OCaml AST
    let ocamlAst =
      match typeLift ast with (env, ast) then
        match generateTypeDecl env ast with (env, ast) then
          let ast = generate env ast in
          let ast = objWrap ast in
          _withPreamble ast options
        else never
      else never
    in

    -- Generate OCaml AST
    ocamlPprint ocamlAst
  else never

let generate = lam files. lam options.
  use MCoreGenerate in
  let generateAndPprintFile = lam file.
      printLn (generateFile file options)
  in
  iter generateAndPprintFile files
