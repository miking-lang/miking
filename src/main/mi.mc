-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- File miking.mi is the main file of the Miking tool chain.

include "seq.mc"
include "string.mc"
include "compile.mc"

mexpr

-- Menu
let menu = strJoin "\n" [
  "Usage: mi [compile] <files>",
  "",
  "Options:",
  "  --debug-parse    Enables output of parsing"] in

-- Option structure
let options = {
  debugParse = false
} in

-- Option map, maps strings to structure updates
let optionsMap = [
("--debug-parse", lam o. {o with debugParse = true})
] in

-- Commands map, maps command strings to functions. The functions
-- always take an option structure as input.
let commandsMap = [
("compile", compile)
] in

-- Simple handling of options before we have an argument parsing library.
let parseOptions = lam xs.
  (foldl (lam acc. lam s1.
    match acc with (options,lst) then
      match findAssoc (lam s2. eqstr s1 s2) optionsMap with Some f
      then (f options, lst)
      else match s1 with "--" ++ _
           then  [printLn (concat "Unknown option " s1), exit 1]
           else (options, cons s1 xs)
    else never
  ) (options,[]) (reverse xs)).0 in


-- Main: find and run the correct command. See commandsMap above.
if lti (length argv) 2 then print menu else
  match findAssoc (lam s. eqstr (get argv 1) s) commandsMap with Some cmd
  then cmd (parseOptions argv)
  else print (strJoin "" ["Unknown command '", get argv 1, "'"])
