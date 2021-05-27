-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- File miking.mi is the main file of the Miking tool chain.

include "compile.mc"
include "seq.mc"
include "string.mc"
include "eval.mc"
include "run.mc"
include "assoc.mc"
include "options.mc"
include "tune.mc"

mexpr

-- Menu
let menu =
"Usage: mi <command> [<options>] file [<options>]

Commands:
  eval      Evaluates a .mc file using an internal interpreter
  compile   Compiles a .mc file into an executable with the same name
  run       Combines eval and compile, to run the program as fast as possible
  tune      Tunes a program with decision points

If no command is given, the file will be executed using the run command
and all arguments after the file are arguments to the .mc executed file.
In such case, options need to be written before the file name.

Options:
  --debug-parse           Print the AST after parsing
  --debug-generate        Print the AST after code generation
  --exit-before           Exit before evaluation or compilation
  --test                  Generate utest code
  --disable-optimizations Disables optimizations to decrease compilation time
  -- <args>               If the run or eval commands are used, then the texts
                          following -- are arguments to the executed program
"
in

-- Commands map, maps command strings to functions. The functions
-- always take two arguments: a list of filename and an option structure.
let commandsMap = [
("run", run),
("eval", eval),
("compile", compile),
("tune", tune)
] in

-- Main: find and run the correct command. See commandsMap above.

-- Does the command line include at least a file or a command?
if lti (length argv) 2 then print menu else

  let cmdString = get argv 1 in
  let rest = tail (tail argv) in
  -- Is it a known command?
  match mapStringLookup cmdString commandsMap with Some cmd
  then
    -- Yes, split into program arguments (after stand alone '--')
    let split = splitDashDash rest in
    let argvp = partition (isPrefix eqc "--") split.first in
    -- Invoke the selected command
    cmd argvp.1 (parseOptions argvp.0) (cons "mi" split.last)
  else
    -- No, not a well known command
    -- Is it a .mc file instead of a command
    if isSuffix eqChar ".mc" cmdString then
       -- Yes, run the 'run' command with arguments and default options
       run [cmdString] options (cons "mi" rest)
    else
       -- No, print error
       printLn (join ["Unknown command '", get argv 1, "'"]);
       exit 1
