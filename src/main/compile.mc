-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "mexpr/tuning/decision-points.mc"
include "ocaml/ast.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "ocaml/external-includes.mc"
include "ocaml/sys.mc"

lang MCoreCompile =
  BootParser +
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

let fileExists = lam path.
  match sysRunCommand ["ls", path] "" "." with {returncode = 0} then
    true
  else
    false

-- Insert tuned values if a .tune file is present
let insertTuned = lam ast. lam file.
  let tuneFile = concat (filenameWithoutExtension file) ".tune" in
  if fileExists tuneFile then
    use BootParser in
    print "parsing file: "; printLn tuneFile;
    let table =
      match parseMExprString [] (readFile tuneFile)
      with TmSeq {tms = values}
      then
        mapFromList subi (mapi (lam i. lam e. (i, e)) values)
      else error "Parsing of tuned values failed"
    in

    use MExprHoles in
    let ast = makeKeywords [] ast in
    let ast = symbolize ast in
    let ast = normalizeTerm ast in
    insert [] table ast
  else ast

let ocamlCompileAst = lam options : Options. lam sourcePath. lam mexprAst.
  use MCoreCompile in

  -- Translate the MExpr AST into an OCaml AST
  match typeLift mexprAst with (env, ast) then
    match generateTypeDecl env ast with (env, ast) then
      match chooseAndGenerateExternals globalExternalMap ast
      with (extNameMap, ast) then
        let ast = generate env ast in

        -- Collect external library dependencies
        let libs = collectLibraries extNameMap in

        let ocamlProg = pprintOcaml ast in

        -- Print the AST after code generation
        (if options.debugGenerate then printLn ocamlProg else ());

        -- Compile OCaml AST
        if options.exitBefore then exit 0
        else
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
    let ast = parseMCoreFile decisionPointsKeywords file in

    -- If program has been tuned, then insert tuned values
    let ast = insertTuned ast file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (pprintMcore ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (symEnv, ast) then

      -- Re-symbolize the MExpr AST and re-annotate it with types
      let ast = symbolizeExpr symEnv ast in
      let ast = typeAnnot ast in

      -- Compile MExpr AST
      ocamlCompileAst options file ast
    else never
  in
  iter compileFile files
