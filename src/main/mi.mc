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
  ArgParserFlag ('h', "help", "Prints a help message and exits",
                 lam o. {o with help = true}),
  ArgParserLongFlag ("debug-parse", "Enables output of parsing",
                     lam o. {o with debugParse = true}),
  ArgParserPositional [
    ArgParserName "MODE",
    ArgParserPosition 0,
    ArgParserRequired (),
    ArgParserDescription "Set mode of the Miking compiler.",
    -- Allowed modes:
    ArgParserValue ("compile", "Compiles the provided MCore files."),
    ArgParserValue ("eval", "Evaluates the provided MCore files."),
    ArgParserApplyVal (lam m. lam o. {o with mode = m})
  ],
  ArgParserMany ("files", "MCore input files",
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
