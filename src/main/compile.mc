
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

-- NOTE(larshum, 2021-03-22): This does not work for Windows file paths.
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

let generateTests = lam ast. lam testsEnabled.
  use MCoreCompile in
  if testsEnabled then
    let ast = symbolize ast in
    let ast = typeAnnot ast in
    match typeLift emptyTypeLiftEnv ast with (env, ast) then
      (env, utestGen env ast)
    else never
  else
    ([], utestStrip ast)

-- We need to reconstruct the type lift environment because the utest generator
-- needs types to be annotated and lifted, but it has to be performed once
-- again after the utests have been generated.
let reconstructTypeLiftEnv = lam env.
  use MExprAst in
  let recordEnv = foldl (lam acc. lam entry.
    match entry with (id, TyRecord {fields = fields}) then
      mapInsert fields id acc
    else acc) (mapEmpty (mapCmp _cmpType)) env in
  let variantEnv = foldl (lam acc. lam entry.
    match entry with (id, TyVariant {constrs = constrs}) then
      mapInsert id constrs acc
    else acc
  ) (mapEmpty nameCmp) env in
  { typeEnv = env
  , records = recordEnv
  , variants = variantEnv }

let compile = lam files. lam options.
  use MCoreCompile in
  let compileFile = lam file.
    let ast = parseMCoreFile file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (env, ast) then
      -- Re-symbolize the MExpr AST and re-annotate it with types
      let ast = symbolize ast in
      let constructors = foldl (lam acc. lam entry.
        match entry with (id, TyVariant {constrs = constrs}) then
          mapUnion acc constrs
        else acc) (mapEmpty nameCmp) env in
      let typeAnnotEnv = {{{_typeEnvEmpty with varEnv = builtinNameTypeMap}
                                          with conEnv = constructors}
                                          with tyEnv = env} in
      let ast = typeAnnotExpr typeAnnotEnv ast in

      -- Translate the MExpr AST into an OCaml AST
      let ocamlAst =
        let typeLiftEnv = reconstructTypeLiftEnv env in
        match typeLift typeLiftEnv ast with (env, ast) then
          match generateTypeDecl env ast with (env, ast) then
            let ast = generate env ast in
            let ast = objWrap ast in
            _withPreamble ast
          else never
        else never
      in

      -- Compile OCaml AST
      ocamlCompile file ocamlAst

    else never
  in
  iter compileFile files
