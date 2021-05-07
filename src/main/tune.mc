
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "compile.mc"
include "options.mc"
include "mexpr/decision-points.mc"
include "mexpr/decision-points-tune.mc"
include "mexpr/boot-parser.mc"
include "ocaml/sys.mc"

lang MCoreTune =
  BootParser +  MExprHoles + MExprTune
end

let tune = lam files. lam options : Options.
  use MCoreTune in
  let tuneFile = lam file.
    let ast = makeKeywords [] (parseMCoreFile ["hole"] file) in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = normalizeTerm ast in
    match flatten [] ast with (prog, table) then
      let binary = ocamlCompile options file prog in
      let run = lam data : ([String], String).
        match data with (args, stdin) then
          dprintLn (cons (join ["./", binary]) args);
          sysRunCommand (cons (join ["./", binary]) args) stdin "."
        else never
      in
      tune run [(["0"], "")] table
    else never
  in
  iter tuneFile files
