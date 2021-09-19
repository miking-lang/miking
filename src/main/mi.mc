-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- File miking.mi is the main file of the Miking tool chain.

include "compile.mc"
include "accelerate.mc"
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
  eval       Evaluates a .mc file using an internal interpreter
  compile    Compiles a .mc file into an executable with the same name
  accelerate Compiles a .mc file into an accelerated executable with the same name
  run        Combines eval and compile, to run the program as fast as possible
  tune       Tunes a program with decision points

If no command is given, the file will be executed using the run command
and all arguments after the file are arguments to the .mc executed file.
In such case, options need to be written before the file name.

Options:
  --debug-parse           Print the AST after parsing
  --debug-generate        Print the AST after code generation
  --debug-type-annot      Print the AST after adding type annotations
  --debug-profile         Instrument profiling expressions to AST
  --exit-before           Exit before evaluation or compilation
  --test                  Generate utest code
  --disable-optimizations Disables optimizations to decrease compilation time
  -- <args>               If the run or eval commands are used, then the texts
                          following -- are arguments to the executed program
  --help                  Display this list of options
"
in

-- Commands map, maps command strings to functions. The functions
-- always take two arguments: a list of filename and an option structure.
let commandsMap = [
("run", run),
("eval", eval),
("compile", compile),
("accelerate", accelerate),
("tune", tune)
] in

-- Print the usage message and exit.
let usage = lam.
  print menu;
  exit 0
in

-- Check the program options, and print help if the user requested it.
let maybePrintHelp = lam o : Options.
  if o.printHelp then usage () else ()
in


-- Main: find and run the correct command. See commandsMap above.

-- Does the command line include at least a file or a command?
if lti (length argv) 2 then usage () else

  let cmdString = get argv 1 in
  let rest = tail (tail argv) in
  -- Is it a known command?
  match mapStringLookup cmdString commandsMap with Some cmd
  then
    -- Yes, split into program arguments (after stand alone '--')
    let split = splitDashDash rest in
    let argvp = partition (isPrefix eqc "--") split.first in
    let options = parseOptions argvp.0 in
    maybePrintHelp options;
    -- Invoke the selected command
    cmd argvp.1 options (cons "mi" split.last)
  else
    -- No, not a well known command
    -- Parse options as far as possible. Does user require help?
    let split = splitOptionPrefix (tail argv) in
    let options = parseOptions split.first in
    maybePrintHelp options;
    -- No help requested. Did user give a filename?
    match split.last with [file] ++ programArgv then
      if isSuffix eqChar ".mc" file then
        -- Yes, run the 'run' command with arguments and supplied options
        run [file] options (cons "mi" programArgv)
      else
        -- No, print error
        printLn (join ["Unknown command '", file, "'"]);
        exit 1
    else
      -- No command or filename. Print help message.
      usage ()
