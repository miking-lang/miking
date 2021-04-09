
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "generate.mc"

-- NOTE(larshum, 2021-03-22): This does not work for Windows file paths.
let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let ocamlCompile = lam sourcePath. lam ocamlProg.
  let p = ocamlCompile ocamlProg in
  let destinationFile = filenameWithoutExtension (filename sourcePath) in
  phMoveFile p.binaryPath destinationFile;
  phChmodWriteAccessFile destinationFile

let compile = lam files. lam options.
  let compileFile = lam file.
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
            _withPreamble ast
          else never
        else never
      in

      -- Compile OCaml AST
      if options.exitBefore then exit 0
      else ocamlCompile file ocamlAst
    else never
  in
  iter compileFile files
