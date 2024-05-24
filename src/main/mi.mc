-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- File miking.mi is the main file of the Miking tool chain.

include "parser/tool.mc"
include "accelerate.mc"
include "compile.mc"
include "seq.mc"
include "string.mc"
include "eval.mc"
include "run.mc"
include "assoc.mc"
include "options.mc"
include "options-config.mc"
include "tune.mc"
include "tune-config.mc"

mexpr

-- Menu
let mainMenu = join
[
"Usage: mi <command> [<options>] file [<options>]

Commands:
  eval       Evaluates a .mc file using an internal interpreter
  compile    Compiles a .mc file into an executable with the same name
  run        Combines eval and compile, to run the program as fast as possible
  tune       Tunes a program with holes
  syn        Run the built-in parser generator

If no command is given, the file will be executed using the run command
and all arguments after the file are arguments to the .mc executed file.
In such case, options need to be written before the file name.

Options:\n",
optionsHelpString optionsConfig,
"
  -- <args>                If the run or eval commands are used, then the texts
                           following -- are arguments to the executed program
"
]
in

let subMenu = lam sub : String. lam config : ParseConfig Options. join
[
"Usage: mi ",
sub,
" [<options>] file [<options>]

Options:\n",
optionsHelpString config,
"
  -- <args>                If the run or eval commands are used, then the texts
                           following -- are arguments to the executed program
"
]
in

-- Configuration structure for a sub command. The 'cmd' is a function that takes
-- three arguments: a list of filenames, an option structure, and arguments
-- passed to the (potentially) executed program. The 'config' is the parse
-- configuration for parsing options for the sub command.
type SubConfig = {
  name : String,
  cmd : [String] -> Options -> [String] -> (),
  config : ParseConfig Options
} in

let parserGen = lam args. lam. lam.
  match args with [synFile, outFile] then
    runParserGenerator {synFile = synFile, outFile = outFile}
  else
    printLn "Please provide exactly two arguments: the '.syn' file and the output '.mc' file.";
    exit 1
in

-- Commands map, maps command strings to functions.
let commandsMap : [(String, SubConfig)] = map (lam c : SubConfig. (c.name, c))
[ {name = "run", cmd = run, config = optionsConfig}
, {name = "eval", cmd = eval, config = optionsConfig}
, {name = "compile", cmd = compile, config = optionsConfig}
, {name = "tune", cmd = tune, config = tuneOptionsConfig}
, {name = "syn", cmd = parserGen, config = optionsConfig}
] in

-- Print the usage message and exit.
let usage = lam sub : Option SubConfig.
  print (
    match sub with Some config then
      let config : SubConfig = config in
      subMenu config.name config.config
    else mainMenu);
  exit 0
in

-- Check the program options, and print help if the user requested it.
let maybePrintHelp = lam o : Options. lam sub : Option SubConfig.
  if o.printHelp then usage sub else ()
in

let mapStringLookup = assocLookup {eq=eqString} in

-- Main: find and run the correct command. See commandsMap above.

-- Does the command line include at least a file or a command?
if lti (length argv) 2 then usage (None ()) else

  let cmdString = get argv 1 in
  let rest = tail (tail argv) in
  -- Is it a known command?
  match mapStringLookup cmdString commandsMap with Some c
  then
    let c : SubConfig = c in
    -- Yes, split into program arguments (after stand alone '--')
    let split = splitDashDash rest in
    let res : ArgResult Options = parseOptions split.first c.config in
    let options : Options = res.options in
    let files : [String] = res.strings in
    maybePrintHelp options (Some c);
    -- Invoke the selected command
    c.cmd files options (cons "mi" split.last)
  else
    -- No, not a well known command
    -- Parse options as far as possible. Does user require help?
    let split = splitOptionPrefix (tail argv) in
    let res : ArgResult Options = parseOptions split.first optionsConfig in
    let options : Options = res.options in
    maybePrintHelp options (None ());
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
      usage (None ())
