
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "compile.mc"
include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/tuning/decision-points.mc"
include "mexpr/tuning/tune.mc"
include "mexpr/tuning/options.mc"
include "ocaml/sys.mc"

lang MCoreTune =
  BootParser + MExprHoles + MExprTune
end

let writeTuned = lam file : String. lam table : LookupTable.
  use MExprPrettyPrint in
  let destinationFile = concat (filenameWithoutExtension file) ".tune" in
  print "destination: "; printLn destinationFile;
  writeFile destinationFile
    (join
      [ "["
      , strJoin ", " (map expr2str (mapValues table))
      ,  "]"])

let tune = lam files. lam options : Options. lam args.

  let tuneFile = lam file.
    use MCoreTune in
    let ast = makeKeywords [] (parseMCoreFile decisionPointsKeywords file) in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = normalizeTerm ast in
    match flatten [] ast with (prog, table, holes) then
      let binary = ocamlCompileAst options file prog in
      let run = lam args : String.
        -- dprintLn (cons (join ["./", binary]) args);
        sysRunCommand (cons (join ["./", binary]) args) "" "."
      in
      let result = tuneEntry run holes table in
      print "best table: "; dprintLn (mapBindings result);
      writeTuned file result;
      printLn (expr2str (insert [] result ast))
    else never
  in
  iter tuneFile files
