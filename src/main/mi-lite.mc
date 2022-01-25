-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The mi-lite is a lightweight compiler using the minimal amount of code
-- needed for bootstrapping. It is used in place of mi in the first
-- bootstrapping stage to speed up compile times.

include "options.mc"
include "parse.mc"
include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "ocaml/mcore.mc"

lang MCoreLiteCompile = BootParser + MExprSym + MExprUtestTrans
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

let compile : Options -> String -> Unit = lam options. lam file.
  use MCoreLiteCompile in
  let ast = parseParseMCoreFile {
    keepUtests = options.runTests,
    pruneExternalUtests = not options.disablePruneExternalUtests,
    pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
    findExternalsExclude = true,
    keywords = []
  } file in
  let ast = utestStrip ast in
  let ast = symbolize ast in
  let hooks = {emptyHooks with compileOcaml = ocamlCompile options file} in
  compileMCore ast hooks

mexpr

let printMenu = lam. print "Usage: mi-lite [0|1] file" in

if neqi (length argv) 3 then
  printMenu ()
else match get argv 1 with "0" then
  let options = {optionsDefault with disableOptimizations = true} in
  compile options (get argv 2)
else match get argv 1 with "1" then
  compile optionsDefault (get argv 2)
else printMenu ()
