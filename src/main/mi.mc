-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- File miking.mi is the main file of the Miking tool chain.

include "argparser.mc"
include "seq.mc"
include "string.mc"
include "compile.mc"

mexpr

-- Option structure
let defaults = {
  help = false,
  debugParse = false,
  mode = "",
  files = []
} in

let config = [
  APFlag ('h', "help", "Prints a help message and exits",
          lam o. {o with help = true}),
  APLongFlag ("debug-parse", "Enables output of parsing",
              lam o. {o with debugParse = true}),
  APPositional [
    APName "mode",
    APPosition 0,
    APRequired (),
    APDescription "Set mode of the Miking compiler.",
    -- Allowed modes:
    APValue ("compile", "Compiles the provided MCore files."),
    APValue ("eval", "Evaluates the provided MCore files."),
    APValue ("repl", "Launches the MCore REPL. Specified input files are automatically included."),
    APApplyVal (lam m. lam o. {o with mode = m}),
    -- Perform sanity checks depending on which mode that was selected
    APPostCond (lam o. if eqstr o.mode "compile" then not (null o.files) else true,
                "No input files to compile"),
    APPostCond (lam o. if eqstr o.mode "eval" then not (null o.files) else true,
                "No input files to evaluate")
  ],
  APAny ("files", "MCore input files",
         lam f. lam o. {o with files = snoc o.files f})
] in

-- Compile time check that arguments settings are well formed. Right side will
-- be `Some String` where the string is a LF separated string with the error
-- messages.
utest argparserCheckError config with None () in

let apret = argparserParse config defaults argv in

let args =
  match apret with Left err then
    let _ = print (strJoin "\n" ["", errs, ""]) in
    error "Error parsing input arguments."
  else match apret with Right values then
    values
  else never
in

if args.help then
  let _ = print (argparserUsage config 80 argv) in
  exit 0
else --continue

()
