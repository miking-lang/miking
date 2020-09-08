-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- An argument parser library

include "bool.mc"
include "char.mc"
include "hashmap.mc"
include "option.mc"
include "seq.mc"
include "string.mc"

type ArgParserPositional a = {
	name: String,
	matchcond: String -> Bool,
	disablecond: String -> Bool,
	apply: String -> a -> a,
	description: String
	-- TBI: Priority, ex: if something is not a filename, then accept it as something else. Some semantics of strongest match.
}

type ArgParserOption a = {
	short: Option Char,
	long: String,
	apply: String -> a -> a,
	description: String,
  parameterized: Bool
}

type ArgParser a = {
	progname: String,
	posargs: [ArgParserPositional a],
	shortopts: HashMap Char String,
	opts: HashMap String (ArgParserOption a),
	values: a
}

-- Local hashmap definitions
let _str_traits = hashmapStrTraits
let _str_mem = hashmapMem _str_traits
let _str_lookupOrElse = hashmapLookupOrElse _str_traits
let _str_lookup = hashmapLookup _str_traits
let _str_insert = hashmapInsert _str_traits
let _str_remove = hashmapRemove _str_traits
let _str_keys = hashmapKeys _str_traits
let _str_values = hashmapValues _str_traits

let _char_traits = {eq = eqchar, hashfn = char2int}
let _char_mem = hashmapMem _char_traits
let _char_lookupOrElse = hashmapLookupOrElse _char_traits
let _char_lookup = hashmapLookup _char_traits
let _char_insert = hashmapInsert _char_traits
let _char_remove = hashmapRemove _char_traits
let _char_keys = hashmapKeys _char_traits
let _char_values = hashmapValues _char_traits

-- Local namespace collision test function
let _sanityCheckShort: Char -> ArgParser a -> () = lam short. lam parser.
  if any (eqchar short) ['-', '='] then
    error "Short option cannot be any of: \'-\', \'=\'"
  else
  if _char_mem short parser.shortopts then
    error (join ["Duplicate short option key \'", [short], "\'"])
  else ()

let _sanityCheckLong: String -> ArgParser a -> () = lam long. lam parser.
  if any (lam c. optionIsSome (index (eqchar c) long)) ['='] then
    error "Long option cannot be any of: \'=\'"
  else
  if _str_mem long parser.opts then
    error (join ["Duplicate long option key \"", long, "\""])
  else ()

-- Creates a new ArgParser
let argparserNew: String -> a -> ArgParser a = lam progname. lam defaults.
  {progname = progname,
   posargs = [],
   shortopts = hashmapEmpty,
   opts = hashmapEmpty,
   values = defaults}

-- Parse input arguments
recursive let argparserParse: [String] -> ArgParser a -> a = lam args. lam parser.
  if null args then
    -- All arguments parsed
    parser.values
  else -- continue scanning

  let lookupLongArg = lam arg: String.
    optionGetOrElse (lam _. error (join ["Unknown long option \"", arg, "\""]))
                    (_str_lookup arg parser.opts)
  in

  let lookupShortArg = lam arg: Char.
    let long = optionGetOrElse (lam _. error (join ["Unknown short option \'", [arg], "\'"]))
                               (_char_lookup arg parser.shortopts)
    in
    optionGetOrElse (lam _. error (join ["Internal error involving short option \'", [arg], "\'"]))
                    (_str_lookup long parser.opts)
  in

  -- isLong checks that arg starts with "--"
  let isLong = lam arg.
    if gti (length arg) 2
    then eqstr "--" (splitAt arg 2).0
    else false
  in

  -- isShort checks that arg starts with "-" but is followed by something different
  let isShort = lam arg.
    if gti (length arg) 1
    then and (eqchar '-' (head arg)) (neqchar '-' (get arg 1))
    else false
  in

  if isLong (head args) then
    -- Scanning a long argument, remove prefix "--"
    let arg: String = (splitAt (head args) 2).1 in

    -- Check if it is named --NAME=PARAM in a single input arg
    let parampos: Option Int = index (eqchar '=') arg in
    match parampos with Some idx then
      -- On the form --NAME=PARAM
      let parts = splitAt arg idx in
      let arg = parts.0 in
      let param = tail (parts.1) in -- Use tail to skip over the '=' sign

      let opt = lookupLongArg arg in
      if not opt.parameterized then
        error (join ["Unexpected parameter for non-parameterized long option \"", arg, "\""])
      else
        let newValues = opt.apply param parser.values in
        argparserParse (tail args) {parser with values = newValues}
    else
      -- On the form --NAME <maybe a parameter>
      let opt = lookupLongArg arg in
      if opt.parameterized then
        if lti (length args) 2 then
          error (join ["Missing parameter for long option \"", arg, "\""])
        else
          let param = get args 1 in
          let newValues = opt.apply param parser.values in
          argparserParse (splitAt args 2).1 {parser with values = newValues}
      else
        let newValues = opt.apply "" parser.values in
        argparserParse (tail args) {parser with values = newValues}

  else if isShort (head args) then
    -- Scanning a short argument, remove prefix '-'
    let shorts: [Char] = tail (head args) in

    let opt = lookupShortArg (head shorts) in

    -- Check if the short option is followed by an equality argument
    let hasEqArg =
      if geqi (length shorts) 2
      then eqchar '=' (get shorts 1)
      else false
    in

    if hasEqArg then
      -- Short option is on the form -O=PARAM
      let param = (splitAt shorts 2).1 in
      if null param then
        error (join ["Empty parameter for short option \'", [head shorts], "\'"])
      else if not opt.parameterized then
        error (join ["Unexpected parameter for non-parameterized short option \'", [head shorts], "\'"])
      else
        let newValues = opt.apply param parser.values in
        argparserParse (tail args) {parser with values = newValues}
    else
      -- Short option is on the form -O...
      if opt.parameterized then
        if not (null (tail shorts)) then
          -- Short option is on the form -OPARAM
          let param = tail shorts in
          let newValues = opt.apply param parser.values in
          argparserParse (tail args) {parser with values = newValues}
        else if lti (length args) 2 then
          error (join ["Missing parameter for short option \'", [head shorts], "\'"])
        else
          -- Short option is on the form -O PARAM
          let param = get args 1 in
          let newValues = opt.apply param parser.values in
          argparserParse (splitAt args 2).1 {parser with values = newValues}
      else
        -- Non-parameterized option, proceed with scanning the following chars
        -- as other short options (if they exist).
        let newArgs =
          if null (tail shorts) then
            tail args
          else
            cons (cons '-' (tail shorts)) (tail args)
        in
        let newValues = opt.apply "" parser.values in
        argparserParse newArgs {parser with values = newValues}

  else
    error (join ["Positional arguments are not yet implemented. Cannot handle \"", head args, "\" yet."]) 
end

-- Get a string describing the usage of the application.
let argparserUsage: Int -> ArgParser a -> String = lam maxwidth. lam parser.
  "TODO"

-- Adds a parameterized option to the argument parser with a short name and a
-- long name.
let argparserAddParamOption =
  lam short: Char.
  lam long: String.
  lam description: String.
  lam applyfn: String -> a -> a.
  lam parser: ArgParser a.
  -- Sanity checks
  let _ = _sanityCheckShort short parser in
  let _ = _sanityCheckLong long parser in

  let newopt: ArgParserOption a = {
    short = Some short,
    long = long,
    apply = applyfn,
    description = description,
    parameterized = true
  } in

  {{parser with shortopts = _char_insert short long parser.shortopts}
           with opts = _str_insert long newopt parser.opts}

-- Adds a non-parameterized option to the argument parser with a short name and
-- a long name.
let argparserAddOption =
  lam short: Char.
  lam long: String.
  lam description: String.
  lam applyfn: a -> a.
  lam parser: ArgParser a.
  -- Sanity checks
  let _ = _sanityCheckShort short parser in
  let _ = _sanityCheckLong long parser in

  let newopt: ArgParserOption a = {
    short = Some short,
    long = long,
    apply = (lam _: String. applyfn),
    description = description,
    parameterized = false
  } in

  {{parser with shortopts = _char_insert short long parser.shortopts}
           with opts = _str_insert long newopt parser.opts}

-- Adds a parameterized option to the argument parser that only has a long
-- name.
let argparserAddLongParamOption =
  lam long: String.
  lam description: String.
  lam applyfn: String -> a -> a.
  lam parser: ArgParser a.
  -- Sanity checks
  let _ = _sanityCheckLong long parser in

  let newopt: ArgParserOption a = {
    short = None (),
    long = long,
    apply = applyfn,
    description = description,
    parameterized = true
  } in

  {parser with opts = _str_insert long newopt parser.opts}

-- Adds a non-parameterized option to the argument parser that only has a long
-- name.
let argparserAddLongOption =
  lam long: String.
  lam description: String.
  lam applyfn: a -> a.
  lam parser: ArgParser a.
  -- Sanity checks
  let _ = _sanityCheckLong long parser in

  let newopt: ArgParserOption a = {
    short = None (),
    long = long,
    apply = (lam _: String. applyfn),
    description = description,
    parameterized = false
  } in

  {parser with opts = _str_insert long newopt parser.opts}


mexpr

type TestArgs = {
  help: Bool,
  version: Bool,
  debugParser: Bool,
  optLevel: Int
} in

let defaults: TestArgs = {
  help = false,
  version = false,
  debugParser = false,
  optLevel = 0
} in

let parser: ArgParser TestArgs = argparserNew "test" defaults in

let parser = argparserAddOption 'h' "help"
                                "Prints usage and a help message."
                                (lam o. {o with help = true})
                                parser
in

let parser = argparserAddOption 'v' "version"
                                "Prints version and exits."
                                (lam o. {o with version = true})
                                parser
in

let parser = argparserAddLongOption "debug-parser"
                                    "Shows debug prints during parsing."
                                    (lam o. {o with debugParser = true})
                                    parser
in

let parser = argparserAddParamOption 'O' "optimization-level"
                                     "Sets the optimization level."
                                     (lam p. lam o. {o with optLevel = string2int p})
                                     parser
in

utest argparserParse [] parser with defaults in
utest argparserParse ["-h"] parser with {defaults with help = true} in
utest argparserParse ["--help"] parser with {defaults with help = true} in
utest argparserParse ["--debug-parser"] parser with {defaults with debugParser = true} in

utest argparserParse ["-hv"] parser with {{defaults with help = true}
                                                    with version = true} in
utest argparserParse ["-vh"] parser with {{defaults with help = true}
                                                    with version = true} in

utest argparserParse ["-v", "--help"] parser with {{defaults with help = true}
                                                             with version = true} in

utest argparserParse ["--optimization-level=2"] parser with {defaults with optLevel = 2} in
utest argparserParse ["-O=2"] parser with {defaults with optLevel = 2} in
utest argparserParse ["-O", "2"] parser with {defaults with optLevel = 2} in
utest argparserParse ["-O2"] parser with {defaults with optLevel = 2} in
utest argparserParse ["-O42"] parser with {defaults with optLevel = 42} in

utest argparserParse ["-vhO2"] parser with {{{defaults with help = true}
                                                       with version = true}
                                                       with optLevel = 2} in

utest argparserParse ["-vhO", "2"] parser with {{{defaults with help = true}
                                                           with version = true}
                                                           with optLevel = 2} in

()
