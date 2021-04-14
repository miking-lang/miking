-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- File miking.mi is the main file of the Miking tool chain.

include "compile.mc"
include "seq.mc"
include "string.mc"
include "run.mc"
include "assoc.mc"

mexpr

-- Menu
let menu = strJoin "\n" [
  "Usage: mi [compile|run] <files>",
  "",
  "Options:",
  "  --debug-parse                    Print the AST after parsing",
  "  --debug-generate                 Print the AST after code generation",
  "  --exit-before                    Exit before evaluation or compilation",
  "  --test                           Generate utest code",
  "  --exclude-intrinsics-preamble    Exclude the intinsics preamble"]
in

-- Option structure
let options = {
  debugParse = false,
  debugGenerate = false,
  exitBefore = false,
  runTests = false,
  excludeIntrinsicsPreamble = false
} in

-- Option map, maps strings to structure updates
let optionsMap = [
("--debug-parse", lam o. {o with debugParse = true}),
("--debug-generate", lam o. {o with debugGenerate = true}),
("--exit-before", lam o. {o with exitBefore = true}),
("--test", lam o. {o with runTests = true}),
("--exclude-intrinsics-preamble", lam o. {o with excludeIntrinsicsPreamble = true})
] in

-- Commands map, maps command strings to functions. The functions
-- always take two arguments: a list of filename and an option structure.
let commandsMap = [
("run", run),
("compile", compile)
] in

-- Lookup for a string map
let mapStringLookup = assocLookup {eq = eqString} in

-- Simple handling of options before we have an argument parsing library.
let parseOptions = lam xs.
  foldl
    (lam accOps. lam s.
      match mapStringLookup s optionsMap with Some f
      then f accOps
      else printLn (concat "Unknown option " s); exit 1
    ) options xs
in

-- Main: find and run the correct command. See commandsMap above.

if lti (length argv) 2 then print menu else
  match mapStringLookup (get argv 1) commandsMap with Some cmd
  then
    let argvp = partition (isPrefix eqc "--") (tail (tail argv)) in
    cmd argvp.1 (parseOptions argvp.0)
  else
    [printLn (join ["Unknown command '", get argv 1, "'"]), exit 1]
