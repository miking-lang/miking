
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
  BootParser +  MExprHoles + MExprTune
end

let tune = lam files. lam options : Options. lam args.

  let tuneFile = lam file.
    use MCoreTune in
    let ast = makeKeywords [] (parseMCoreFile ["hole"] file) in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = normalizeTerm ast in
    match flatten [] ast with (prog, table) then
      let binary = ocamlCompileAst options file prog in
      let run = lam args : String.
        -- dprintLn (cons (join ["./", binary]) args);
        sysRunCommand (cons (join ["./", binary]) args) "" "."
      in
      tuneEntry run table
    else never
  in
  iter tuneFile files
