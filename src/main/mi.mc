-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- File miking.mi is the main file of the Miking tool chain.

include "compile.mc"
include "seq.mc"
include "string.mc"
include "run.mc"
include "assoc.mc"
include "options.mc"

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

-- Commands map, maps command strings to functions. The functions
-- always take two arguments: a list of filename and an option structure.
let commandsMap = [
("run", run),
("compile", compile)
] in

-- Main: find and run the correct command. See commandsMap above.

if lti (length argv) 2 then print menu else
  match mapStringLookup (get argv 1) commandsMap with Some cmd
  then
    let argvp = partition (isPrefix eqc "--") (tail (tail argv)) in
    cmd argvp.1 (parseOptions argvp.0)
  else
    [printLn (join ["Unknown command '", get argv 1, "'"]), exit 1]
