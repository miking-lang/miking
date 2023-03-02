-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The mi-lite is a lightweight compiler using the minimal amount of code
-- needed for bootstrapping. It is used in place of mi in the first
-- bootstrapping stage to speed up compile times.

include "options.mc"
include "parse.mc"
include "mexpr/boot-parser.mc"
include "mexpr/pprint.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "ocaml/mcore.mc"

lang MCoreLiteCompile =
  BootParser + MExprSym + MExprTypeCheck + MCoreCompileLang +
  MExprLowerNestedPatterns + MExprPrettyPrint

  -- NOTE(larshum, 2022-12-30): We define the stripping of utests here instead
  -- of reusing the definition from utest-generate to significantly reduce the
  -- code size.
  sem stripUtests : Expr -> Expr
  sem stripUtests =
  | TmUtest t -> stripUtests t.next
  | t -> smap_Expr_Expr stripUtests t
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

let ocamlCompile : Options -> String -> [String] -> [String] -> String -> String =
  lam options. lam sourcePath. lam libs. lam clibs. lam ocamlProg.
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
  let destinationFile =
    switch options.output
    case None () then filenameWithoutExtension (filename sourcePath)
    case Some o then o
    end
  in
  sysMoveFile p.binaryPath destinationFile;
  sysChmodWriteAccessFile destinationFile;
  p.cleanup ();
  destinationFile

let compile : Options -> String -> () = lam options. lam file.
  use MCoreLiteCompile in
  let ast = parseParseMCoreFile {
    keepUtests = options.runTests,
    pruneExternalUtests = not options.disablePruneExternalUtests,
    pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
    findExternalsExclude = true,
    eliminateDeadCode = not options.keepDeadCode,
    keywords = []
  } file in
  let ast = stripUtests ast in
  let ast = symbolize ast in
  let ast = typeCheck ast in
  let ast = lowerAll ast in
  let hooks = mkEmptyHooks (ocamlCompile options file) in
  compileMCore ast hooks;
  ()

mexpr

let printMenu = lam. print "Usage: mi-lite [0|1] file outfile" in

if neqi (length argv) 4 then
  printMenu ()
else match get argv 1 with "0" then
  let options = {optionsDefault with disableOptimizations = true, output = Some (get argv 3)} in
  compile options (get argv 2)
else match get argv 1 with "1" then
  let options = {optionsDefault with output = Some (get argv 3)} in
  compile options (get argv 2)
else printMenu ()
