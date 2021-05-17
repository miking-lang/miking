
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

let tuneOptions = {iters = 10, method = RandomWalk {}}

let getInput : String -> String = lam s.
  let prefix = "--input=" in
  if isPrefix eqc prefix s then
    subsequence s (length prefix) (length s)
  else error (concat "Not a valid input: " s)

recursive let parseArgs = lam args. lam acc.
  match args with [] then acc
  else match args with [a] ++ args then
    parseArgs args (snoc acc (getInput a))
  else never
end

let tune = lam files. lam options : Options. lam args.
  let inputData = parseArgs (tail args) [] in
  let inputData = map (lam d. (strSplit " " d, "")) inputData in
  dprintLn inputData;

  use MCoreTune in
  let tuneFile = lam file.
    let ast = makeKeywords [] (parseMCoreFile ["hole"] file) in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = normalizeTerm ast in
    match flatten [] ast with (prog, table) then
      let binary = ocamlCompileAst options file prog in
      let run = lam data : ([String], String).
        match data with (args, stdin) then
          dprintLn (cons (join ["./", binary]) args);
          sysRunCommand (cons (join ["./", binary]) args) stdin "."
        else never
      in
      tune run inputData tuneOptions table
    else never
  in
  iter tuneFile files
