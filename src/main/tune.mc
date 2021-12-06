
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "compile.mc"
include "options.mc"
include "sys.mc"
include "parse.mc"
include "tuning/context-expansion.mc"
include "tuning/tune.mc"

lang MCoreTune =
  BootParser + MExprHoles + MExprTune
end

let tableFromFile = lam file.
  if fileExists file then tuneFileReadTable file
  else error (join ["Tune file ", file, " does not exist"])

let dumpTable = lam file. lam env. lam table.
  let destination = tuneFileName file in
  tuneFileDumpTable destination env table

let tune = lam files. lam options : Options. lam args.

  let tuneOptions : TuneOptions = options.tuneOptions in

  let tuneFile = lam file.
    use MCoreTune in
    let ast = parseParseMCoreFile {
      keepUtests = options.runTests,
      pruneExternalUtests = not options.disablePruneExternalUtests,
      pruneExternalUtestsWarning = not options.disablePruneExternalUtestsWarning,
      findExternalsExclude = true,
      keywords = holeKeywords
    } file in
    let ast = makeKeywords [] ast in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = normalizeTerm ast in

    -- Context expand the holes
    match contextExpand [] ast with
      { ast = ast, table = table, tempFile = tempFile, cleanup = cleanup,
        env = env, tempDir = tempDir }
    then
      -- If option --tuned is given, then use tune file as defaults
      let table =
        if options.useTuned then tableFromFile (tuneFileName file) else table in

      -- Compile the program and write to temporary directory
      let binary = ocamlCompileAstWithUtests
        {options with output = Some (sysJoinPath tempDir "tune")} file ast in

      -- Do the tuning
      let result = tuneEntry binary tuneOptions tempFile env table in

      -- Write the best found values to filename.tune
      tuneFileDumpTable (tuneFileName file) (Some env) result;

      -- If option --compile is given, then compile the program using the
      -- tuned values
      (if options.compileAfterTune then
        compile [file] {options with useTuned = true} args
       else ());

      -- If option --enable-cleanup is given, then remove the tune file
      (if tuneOptions.cleanup then sysDeleteFile (tuneFileName file) else ());

      -- Clean up temporary files used during tuning
      cleanup ()
    else never
  in
  iter tuneFile files
