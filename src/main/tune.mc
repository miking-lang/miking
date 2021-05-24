
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "compile.mc"
include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/tuning/decision-points.mc"
include "mexpr/tuning/tune.mc"
include "ocaml/sys.mc"

lang MCoreTune =
  BootParser + MExprHoles + MExprTune
end

let tune = lam files. lam options : Options. lam args.

  let tuneFile = lam file.
    use MCoreTune in
    let ast = makeKeywords [] (parseMCoreFile decisionPointsKeywords file) in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = normalizeTerm ast in

    -- Flatten the decision points
    match flatten [] ast with
      { prog = prog, table = table, holes = holes,
        tempFile = tempFile, cleanup = cleanup }
    then
      -- Compile the program
      let binary = ocamlCompileAst options file prog in

      -- Runs the program with a given input
      let run = lam args : String.
        sysRunCommand (cons (join ["./", binary]) args) "" "."
      in
      -- Do the tuning
      let result = tuneEntry args run holes tempFile table in

      -- Write the best found values to filename.tune
      tuneDumpTable file result;

      -- Clean up temporary files used during tuning
      cleanup ()
    else never
  in
  iter tuneFile files
