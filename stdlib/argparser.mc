-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- An argument parser library.

include "bool.mc"
include "char.mc"
include "either.mc"
include "hashmap.mc"
include "math.mc"
include "option.mc"
include "seq.mc"
include "string.mc"

-- Public types
type APModifier a
-- OPTION ONLY MODIFIERS
con APShort: Char -> APModifier a
con APLong: String -> APModifier a
con APMetavar: String -> APModifier a
con APApply: (a -> a) -> APModifier a
-- POSITIONAL ONLY MODIFIERS
con APName: String -> APModifier a
con APPosition: Int -> APModifier a
con APMatchCond: (String -> Bool) -> APModifier a
con APRequired: () -> APModifier a
-- GENERIC MODIFIERS
con APDescription: String -> APModifier a
con APApplyVal: (String -> a -> a) -> APModifier a
con APValue: (String, String) -> APModifier a
con APValues: [String] -> APModifier a
con APValueDescription: (String, String) -> APModifier a
con APOnce: () -> APModifier a
con APPostCond: ((a -> Bool), String) -> APModifier a -- A check that will be performed if this has been matched with an input argument

type APConfiguration a
con APOption: [APModifier a] -> APConfiguration a
con APPositional: [APModifier a] -> APConfiguration a
con APFlag: (Char, String, String, a -> a) -> APConfiguration a
con APLongFlag: (String, String, a -> a) -> APConfiguration a
con APMetavarFlag: (Char, String, String, String, String -> a -> a) -> APConfiguration a
con APLongMetavarFlag: (String, String, String, String -> a -> a) -> APConfiguration a
con APMutuallyExclusiveOptions: [String] -> APConfiguration a
con APAny: (String, String, a -> a) -> APConfiguration a
con APMany: (String, String, a -> a) -> APConfiguration a


-- Internal types
type APOptionItem_ a = {
  short: Option Char,
  long: String,
  metavar: Option String,
  description: Option String,
  apply: String -> a -> a,
  -- values: <ValueName> -> <Description>
  values: HashMap String String,
  once: Bool,
  postconds: [((String -> Bool), String)]
}
type APPositionalItem_ a = {
  name: String,
  description: Option String,
  position: Option Int,
  apply: Option (String -> a -> a),
  matchconds: [String -> Bool],
  required: Bool,
  -- values: <ValueName> -> <Description>
  values: HashMap String String,
  once: Bool,
  postconds: [((a -> Bool), String)]
}
type ArgParser_ a = {
  -- The name of the program being run, specified by `head args`.
  name: String,
  -- Contains all options as a map from long option name -> option record
  options: HashMap String (APOptionItem_ a),
  -- Lookup from short option name -> long option name
  shortOptLookup: HashMap Char String,
  -- A map over long option names -> other options than cannot be specified with this option
  optExclusions: HashMap String [String],
  -- All positionals
  positionals: [APPositionalItem_ a],
  -- Lines of error messages that has been produced during the argument
  -- parsing. An empty list indicates that no error has occurred. These should
  -- ideally be printed as `strJoin "\n" ap.errors`. The reason for not
  -- embedding this into an Either type is to allow accumulation of as many
  -- errors as possible when forming the parser.
  errors: [String]
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


-- Takes the settings list to an APOption and returns either a tuple
-- containing the long option name with list of error messages, or a
-- well-formed option.
let formOption_: [APModifier a] -> Either (String, [String]) (APOptionItem_ a) = lam mods.
  let opt: APOptionItem_ a = {
    short = None (),
    long = "",
    metavar = None (),
    description = "",
    apply = lam _. lam o. o,
    values = hashmapEmpty,
    once = false,
    postconds = []
  } in

  let accrecord = {opt = opt, errs = [], hasLong = false, hasApply = false, unprocessed = []} in

  -- Set basic properties
  let state = foldl (lam acc. lam mod.
    match mod with APShort c then
      if optionIsNone acc.opt.short then
        {acc with opt = {acc.opt with short = Some c}}
      else
        {acc with errs = snoc acc.errs "Multiple short modifiers"}
    else match mod with APLong s then
      if not acc.hasLong then
        {{acc with opt = {acc.opt with long = s}}
              with hasLong = true}
      else
        {acc with errs = snoc acc.errs "Multiple long modifiers"}
    else match mod with APMetavar mv then
      if optionIsNone acc.opt.metavar then
        {acc with opt = {acc.opt with metavar = Some mv}}
      else
        {acc with errs = snoc acc.errs "Multiple metavars"}
    else match mod with APDescription s then
      {acc with opt = {acc.opt with description = s}}
    else match mod with APValue (val,desc) then
      {acc with opt = {acc.opt with values = _str_insert val desc acc.opt.values}}
    else match mod with APValues vs then
      if null vs then
        {acc with errs = snoc acc.errs "Empty value list"}
      else
        {acc with opt = {acc.opt with values = foldl (lam hm. lam v.
            if _str_mem v hm then
              hm -- do not overwrite binding if present!
            else
              _str_insert v "" hm
          ) acc.opt.values vs}}
    else match mod with APOnce _ then
      {acc with opt = {acc.opt with once = true}}
    else match mod with APPostCond pctup then
      {acc with opt = {acc.opt with postconds = cons pctup acc.opt.postconds}}
    else
      -- Process this at a later stage
      {acc with unprocessed = snoc acc.unprocessed mod}
  ) state mods in

  -- Process options that depends on previously processed settings
  let state = foldl (lam acc. lam mod.
    match mod with APValueDescription (val, desc) then
      -- Only add description to a value if it actually exists.
      if _str_mem val acc.opt.values then
        {acc with opt = {acc.opt with values = _str_insert val desc acc.opt.values}}
      else
        {acc with errs = snoc acc.errs (join ["Cannot set description for non-existent value \"", val, "\""])}
    else match mod with APApply fn then
      if acc.hasApply then
        {acc with errs = snoc acc.errs "Multiple apply functions"}
      else
        {{acc with opt = {acc.opt with apply = lam _. fn}}
              with hasApply = true}
    else match mod with APApplyVal fn then
      if optionIsNone acc.opt.metavar then
        {acc with errs = snoc acc.errs "Cannot apply value to an option without a metavar"}
      else if opt.hasApply then
        {acc with errs = snoc acc.errs "Multiple apply functions"}
      else
        {{acc with opt = {acc.opt with apply = fn}}
              with hasApply = true}
    else
      -- Process this at a later stage
      {acc with unprocessed = snoc acc.unprocessed mod}
  ) {state with unprocessed = []} state.unprocessed in

  -- Check for settings that are not applicable to an option
  let state = foldl (lam acc. lam mod.
    match mod with APName _ then
      {acc with errs = snoc acc.errs "Invalid option setting \"APName\""}
    else match mod with APPosition _ then
      {acc with errs = snoc acc.errs "Invalid option setting \"APPosition\""}
    else match mod with APMatchCond _ then
      {acc with errs = snoc acc.errs "Invalid option setting \"APMatchCond\""}
    else
      -- Process this at a later stage
      {acc with unprocessed = snoc acc.unprocessed mod}
  ) {state with unprocessed = []} state.unprocessed in

  -- Check that an option has a long name
  let state =
    if not state.hasLong then
      {{state with errs = snoc state.errs "Missing long option name"}
              with opt = {state.opt with long = "<unnamed>"}}
    else
      state
  in

  -- Check that a method of applying the option exists
  let state =
    if not state.hasApply then
      {state with errs = snoc state.errs "Missing option apply function"}
    else
      state
  in

  -- Print a warning if we still have unprocessed modifiers
  let _ =
    if not (null state.unprocessed) then
      print "WARNING: Internal check failed: Unprocessed option modifiers\n"
    else ()
  in

  if not (null state.errs) then
    Left (state.opt.long, state.errs)
  else
    Right state.opt


-- Takes the settings list to an APPositional and returns either a tuple
-- that contains identifying name with a list of error messages, or a
-- well-formed positional.
let formPositional_: [APModifier a] -> Either (String, [String]) (APPositionalItem_ a) = lam mods.
  let pos: APPositionalItem_ a = {
    name = "",
    description = "",
    position = None (),
    apply = lam _. lam o. o,
    matchconds = [],
    required = false,
    values = hashmapEmpty,
    once = false,
    postconds = []
  } in

  let accrecord = {pos = pos, errs = [], hasName = false, hasApply = false, unprocessed = []} in

  -- Set basic properties
  let state = foldl (lam acc. lam mod.
    match mod with APName s then
      if not acc.hasName then
        {{acc with pos = {acc.pos with name = s}}
              with hasName = true}
      else
        {acc with errs = snoc acc.errs "Multiple names for positional"}
    else match mod with APPosition i then
      if optionIsNone acc.pos.position then
        {acc with pos = {acc.pos with position = Some i}}
      else
        {acc with errs = snoc acc.errs "Multiple positions specified"}
    else match mod with APMatchCond condfn then
      {acc with pos = {acc.pos with matchconds = cons condfn acc.pos.matchconds}}
    else match mod with APDescription s then
      {acc with pos = {acc.pos with description = s}}
    else match mod with APValue (val,desc) then
      {acc with pos = {acc.pos with values = _str_insert val desc acc.pos.values}}
    else match mod with APValues vs then
      if null vs then
        {acc with errs = snoc acc.errs "Empty value list"}
      else
        {acc with pos = {acc.pos with values = foldl (lam hm. lam v.
            if _str_mem v hm then
              hm -- do not overwrite binding if present!
            else
              _str_insert v "" hm
          ) acc.pos.values vs}}
    else match mod with APOnce _ then
      {acc with pos = {acc.pos with once = true}}
    else match mod with APRequired _ then
      {acc with pos = {acc.pos with required = true}}
    else match mod with APPostCond pctup then
      {acc with pos = {acc.pos with postconds = cons pctup acc.pos.postconds}}
    else
      -- Process this at a later stage
      {acc with unprocessed = snoc acc.unprocessed mod}
  ) state mods in

  -- Process options that depends on previously processed settings
  let state = foldl (lam acc. lam mod.
    match mod with APValueDescription (val, desc) then
      -- Only add description to a value if it actually exists.
      if _str_mem val acc.pos.values then
        {acc with pos = {acc.pos with values = _str_insert val desc acc.pos.values}}
      else
        {acc with errs = snoc acc.errs (join ["Cannot set description for non-existent value \"", val, "\""])}
    else match mod with APApplyVal fn then
      if pos.hasApply then
        {acc with errs = snoc acc.errs "Multiple apply functions"}
      else
        {{acc with pos = {acc.pos with apply = fn}}
              with hasApply = true}
    else
      -- Process this at a later stage
      {acc with unprocessed = snoc acc.unprocessed mod}
  ) {state with unprocessed = []} state.unprocessed in

  -- Check for settings that are not applicable to a positional
  let state = foldl (lam acc. lam mod.
    match mod with APShort _ then
      {acc with errs = snoc acc.errs "Invalid positional setting \"APShort\""}
    else match mod with APLong _ then
      {acc with errs = snoc acc.errs "Invalid positional setting \"APLong\""}
    else match mod with APMetavar _ then
      {acc with errs = snoc acc.errs "Invalid positional setting \"APMetavar\""}
    else match mod with APApply _ then
      {acc with errs = snoc acc.errs "Invalid positional setting \"APApply\""}
    else
      -- Process this at a later stage
      {acc with unprocessed = snoc acc.unprocessed mod}
  ) {state with unprocessed = []} state.unprocessed in

  -- Check that positional has a name
  let state =
    if not state.hasName then
      {{state with errs = snoc state.errs "Missing positional name"}
              with pos = {state.pos with name = "<unnamed>"}}
    else
      state
  in

  -- Check that a method of applying the positional exists
  let state =
    if not state.hasApply then
      {state with errs = snoc state.errs "Missing apply function"}
    else
      state
  in

  -- Print a warning if we still have unprocessed modifiers
  let _ =
    if not (null state.unprocessed) then
      print "WARNING: Internal check failed: Unprocessed positional modifiers\n"
    else ()
  in

  if not (null state.errs) then
    Left (state.pos.name, state.errs)
  else
    Right state.pos


-- Adds a parsed option result to the ArgParser if it passes all checks.
-- Otherwise concatenates the error messages to the internal list of error
-- messages.
let addOption_: Either (String, [String]) (APOptionItem_ a) -> ArgParser_ a -> ArgParser_ a =
  lam eitherOpt. lam ap.
  match eitherOpt with Left (long, errs) then
    {ap with errors = join [
      ap.errors,
      [join ["Misformed option \"", long, "\":"]],
      map (concat "  - ") errs -- <- apply indendation
    ]}
  else match eitherOpt with Right opt then
    if _str_mem opt.long ap.options then
      {ap with errors = snoc ap.errors (
        join ["Duplicate long option name \"", opt.long, "\""]
       )}
    else if optionMapOr false (lam c. _char_mem c ap.shortOptLookup) opt.short then
      {ap with errors = snoc ap.errors (
        -- We know that opt.short is `Some c`, only using '-' as a placeholder.
        join ["Duplicate short option name \"", optionGetOr '-' opt.short, "\""]
       )}
    else
      -- Insert short lookup (if it exists)
      let ap = optionMapOr ap (lam c. _char_insert c opt.long ap.shortOptLookup) opt.short in
      {ap with options = _str_insert opt.long opt ap.options}
  else never

-- Adds a parsed positionalal result to the ArgParser if it passes all checks.
-- Otherwise concatenates the error messages to the internal list of error
-- messages.
let addPositional_: Either (String, [String]) (APPositionalItem_ a) -> ArgParser_ a -> ArgParser_ a =
  lam eitherPos. lam ap.
  match eitherPos with Left (name, errs) then
    {ap with errors = join [
      ap.errors,
      [join ["Misformed positional \"", name, "\":"]],
      map (concat "  - ") errs -- <- apply indendation
    ]}
  else match eitherPos with Right pos then
    if any (lam p. eqstr p.name pos.name) ap.positionals then
      {ap with errors = join [
        ap.errors,
        [join ["Duplicate positional name \"", name, "\":"]],
        map (concat "  - ") errs -- <- apply indendation
      ]}
    else
    {ap with positionals = snoc ap.positionals pos}
  else never


recursive let translateConfig_: [APConfiguration a] -> [APConfiguration a] -> ArgParser_ a -> ArgParser_ a =
  lam configs. lam postconfigs. lam ap.
  match configs with [config] ++ remaining then
    -- Scan primary configs
    let config = head configs in
    let remaining = tail configs in
    match config with APOption mods then
      let optret = formOption_ mods in
      translateConfig_ remaining postconfigs (addOption_ optret ap)
    else match configs with APPositional mods then
      let posret = formPositional_ mods in
      translateConfig_ remaining postconfigs (addPositional_ modret ap)
    else match configs with APFlag (short, long, description, apply) then
      let optret = formOption_ [
        APShort short,
        APLong long,
        APDescription description,
        APApply apply
      ] in
      translateConfig_ remaining postconfigs (addOption_ optret ap)
    else match configs with APLongFlag (long, description, apply) then
      let optret = formOption_ [
        APLong long,
        APDescription description,
        APApply apply
      ] in
      translateConfig_ remaining postconfigs (addOption_ optret ap)
    else match configs with APMetavarFlag (short, long, metavar, description, applyval) then
      let optret = formOption_ [
        APShort short,
        APLong long,
        APMetavar metvar,
        APDescription description,
        APApplyVal applyval
      ] in
      translateConfig_ remaining postconfigs (addOption_ optret ap)
    else match configs with APLongMetavarFlag (long, metavar, description, applyval) then
      let optret = formOption_ [
        APLong long,
        APMetavar metvar,
        APDescription description,
        APApplyVal applyval
      ] in
      translateConfig_ remaining postconfigs (addOption_ optret ap)
    else
      -- Handle this config after the primary configs. Most likely due to
      -- that it needs to have all names specified
      translateConfig_ remaining (snoc configs postconfigs) ap
  else match postconfigs with [postconfig] ++ remaining then
    match postconfig with APMutuallyExclusiveOptions longs then
      -- Check that all specified names actually exists
      let check = foldl (lam acc: Option [String]. lam long.
        if _str_mem long ap.options then
          acc -- OK
        else
          optionMapOr (Some long) (cons long) acc
      ) (None ()) longs in
      match check with Some invalidLongs then
        translateConfig_ [] remaining {ap with errors = snoc ap.errors (
          join ["Cannot set mutual exclusion for non-existent options: ",
                strJoin ", " invalidLongs])}
      else
        let updatedAp = foldl (lam accap. lam long.
          let existing = _str_lookupOrElse (lam _. []) long accap.optExclusions in
          -- Mark all _other_ longs as mutually exclusive to this one
          let mutExludes = filter (lam s. not eqstr long s) longs in
          {accap with optExclusions = _str_insert long (concat existing mutExludes) accap.optExclusions}
        ) ap longs in
        translateConfig_ [] remaining updatedAp
    else
      let _ = print "WARNING: Internal check failed: Unprocessed config modifier\n" in
      translateConfig_ [] remaining ap
  else
    -- No more configs to translate!
    ap
end


--- It can be difficult to
--- find the odd one out
--- when there is a bunch
--- of text to read at the
--  same time as trying to make
--- sure that you follow proper
--- formatting styles.

-- Constructs a parser based on the provided configuration
let createParser_: [APConfiguration a] -> String -> ArgParser_ a =
  lam configs. lam progname.
  let ap = {
    name = progname,
    options = hashmapEmpty,
    shortOptLookup = hashmapEmpty,
    optExclusions = hashmapEmpty,
    positionals = [],
    errors = []
  } in

  -- Scan configuration and form initial parser
  let ap = translateConfig_ configs [] ap in
  let ap = checkPositionalLogic_ ap in


  --
  if not (null ap.errors) then
    Left ap.errors
  else -- OK! No errors so far.

  -- Check that positionals are well-formed
  if not (null ap.errors) then
    Left ap.errors
  else
    Right ap

-- argparserParse:
  -- 1. transform shorthands to verbose modifier lists
  -- 2. form options from modifier lists
  -- 3. form positionals from lists
  -- 4. create lookup tables for options
  -- 5. create
let argparserParse: [APConfiguration a] -> a -> [String] -> Either String a =
  lam configs. lam defaults. lam args.
  let apret = createParser_ configs (head args) in
  match apret with Left errs then
    Left (strJoin "\n" (cons "Misformed ArgParser:" errs))
  else match apret with Right ap then
    --TODO
    defaults
  else never








type APPositional a = {
  name: String,
  matchcond: String -> Bool,
  disablecond: String -> Bool,
  apply: String -> a -> a,
  description: String
  -- TBI: Priority, ex: if something is not a filename, then accept it as something else. Some semantics of strongest match.
}

type APOption a = {
  short: Option Char,
  long: String,
  apply: String -> a -> a,
  description: String,
  parameterized: Bool,
  paramname: String
}

type ArgParser a = {
  progname: String,
  posargs: [APPositional a],
  shortopts: HashMap Char String,
  opts: HashMap String (APOption a),
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
  -- Format "usage: <progname> [OPTIONS] <POSITIONALS>"
  let prefix = join ["usage: ", parser.progname] in
  let indent = makeSeq (mini (length prefix) 20) ' ' in -- do not indent more than 20 characters

  let allOpts = _str_values parser.opts in

  -- Splits options into "Shorts With No Parameter" and the rest
  let splitSWNP = partition (lam opt. match opt.short with Some _ then not opt.parameterized else false) allOpts in

  -- Constructs the string [-abcdeFGHIJK]
  let shortNonParamStr = join ["[-", map (lam opt. optionGetOrElse (lam _. error "Logic error") opt.short) splitSWNP.0, "]"] in

  let opt2headerpart = lam opt: APOption a.
    let name = optionMapOr (concat "--" opt.long)
                           (lam c. ['-', c])
                           opt.short
    in
    let parampart = if opt.parameterized then cons ' ' opt.paramname else "" in
    join ["[", name, parampart, "]"]
  in

  let parts = cons shortNonParamStr (map opt2headerpart splitSWNP.1) in
  -- TODO: Missing positionals

  let fmtUsage = lam revacc: [String]. lam part: String.
    let totallength = addi (length (head revacc)) (addi (length part) 1) in
    if gti totallength maxwidth then
      -- Add a new line
      cons (join [indent, " ", part]) revacc
    else
      -- Add to existing line
      cons (join [head revacc, " ", part]) (tail revacc)
  in
  let lines = reverse (foldl fmtUsage [prefix] parts) in

  -- TODO: Add detailed descriptions here
  strJoin "\n" lines

-- Adds a parameterized option to the argument parser with a short name and a
-- long name.
let argparserAddParamOption =
  lam short: Char.
  lam long: String.
  lam paramname: String.
  lam description: String.
  lam applyfn: String -> a -> a.
  lam parser: ArgParser a.
  -- Sanity checks
  let _ = _sanityCheckShort short parser in
  let _ = _sanityCheckLong long parser in

  let newopt: APOption a = {
    short = Some short,
    long = long,
    apply = applyfn,
    description = description,
    parameterized = true,
    paramname = paramname
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

  let newopt: APOption a = {
    short = Some short,
    long = long,
    apply = (lam _: String. applyfn),
    description = description,
    parameterized = false,
    paramname = ""
  } in

  {{parser with shortopts = _char_insert short long parser.shortopts}
           with opts = _str_insert long newopt parser.opts}

-- Adds a parameterized option to the argument parser that only has a long
-- name.
let argparserAddLongParamOption =
  lam long: String.
  lam paramname: String.
  lam description: String.
  lam applyfn: String -> a -> a.
  lam parser: ArgParser a.
  -- Sanity checks
  let _ = _sanityCheckLong long parser in

  let newopt: APOption a = {
    short = None (),
    long = long,
    apply = applyfn,
    description = description,
    parameterized = true,
    paramname = paramname
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

  let newopt: APOption a = {
    short = None (),
    long = long,
    apply = (lam _: String. applyfn),
    description = description,
    parameterized = false,
    paramname = ""
  } in

  {parser with opts = _str_insert long newopt parser.opts}


mexpr

type TestArgs = {
  help: Bool,
  version: Bool,
  debugParser: Bool,
  optLevel: Int,
  defines: [String],
  multi: (String, String, String)
} in

let defaults: TestArgs = {
  help = false,
  version = false,
  debugParser = false,
  optLevel = 0,
  defines = [],
  multi = ("", "", ""),
  isOn = false
} in

let argspec = [
  APOption [
    APShort 'h',
    APLong "help",
    APDescription "Prints a help message and exits.",
    APApply (lam o. {o with help = true})
  ],
  APOption [
    APShort 'v',
    APLong "version",
    APDescription "Prints version and exits.",
    APApply (lam o. {o with version = true})
  ],
  APOption [
    APLong "debug-parser",
    APDescription "Shows debug prints during parsing.",
    APApply (lam o. {o with debugParser = true})
  ],
  APOption [
    APShort 'O',
    APLong "optimization-level",
    APMetavar "LEVEL",
    APDescription "Sets the optimization level.",
    APApplyVal (lam p. lam o. {o with optLevel = string2int p})
  ],
  APOption [
    APShort 'D',
    APLong "define",
    APMetavar "DEFINITION",
    APDescription "Add C preprocessor definition.",
    APApplyVal (lam p. lam o. {o with defines = snoc o.defines p})
  ],
  APOption [
    APLong "a-very-long-option-name",
    APMetavar "fooparam",
    APDescription "Shows debug prints during parsing.",
    APApplyVal (lam _. lam o. o)
  ],
  APOption [
    APLong "multi",
    APMetavars ["arg1", "arg2", "arg3"],
    APDescription "Takes multiple parameters.",
    APApplyVals (lam sl. lam o. {o with multi = (get sl 0, get sl 1, get sl 2)})
  ],
  APMutuallyExclusive [
    APOption [
      APLong "on",
      APDescription "Turns it on!",
      APApply (lam o. {o with isOn = true})
    ],
    APOption [
      APLong "off",
      APDescription "Turns it off!",
      APApply (lam o. {o with isOn = false})
    ]
  ],
  -- The above would be a wrapper for this, which allows for more complex behavior:
  APMutuallyExclusiveOptions [
    APLong "on",
    APLong "off"
  ],
  APLongFlag ("ocaml", "Targets OCaml backend", lam o. {o with ocaml = true}),
  APFlag ('V', "verbose", "Increases verbosity", lam o. {o with verbosity = addi o.verbosity 1}),
  -- What I expect to have in the end:
  AP.Positional [
    AP.Name "mcore file",
    AP.ApplyVal (lam f. lam o. {o with mcfiles = cons f o.mcfiles}),
    AP.MatchOn (Str.isSuffix ".mc"),
    AP.Description "MCore input source files. (ends in .mc)"
  ],
  AP.Positional [
    AP.Name "ragnar file",
    AP.ApplyVal (lam f. lam o. {o with rgfiles = cons f o.rgfiles}),
    AP.MatchOn (Str.isSuffix ".rg"),
    AP.Description "Ragnar input source files. (ends in .rg)"
  ],
  AP.Positional [
    AP.Name "mode",
    AP.ApplyVal (lam m. lam o. {o with mode = m}),
    AP.Position 1,
    AP.Values ["compile", "eval", "test", "repl"],
    AP.Description "The mode to use the compiler with.",
    AP.ValueDescription ("compile", "Compiles the input source files."),
    AP.ValueDescription ("eval", "Evaluates the input source files"),
    AP.ValueDescription ("test", "Runs the utest statements in the input source files."),
    AP.ValueDescription ("repl", "Launches the MCore REPL.")
  ],
  AP.Option [
    AP.Long "target",
    AP.Metavar "PLATFORM",
    AP.Values ["native", "ocaml", "amd64", "llvm"],
    AP.Default "native",
    AP.Description "Specifies compilation backend. (Default: native)",
    AP.ApplyVal (lam t. lam o. {o with o.target = t}),
    AP.Cond (lam o. eqstr o.mode "compile",
             "Can only specify target when compiling."),
    AP.Once ()
  ],
  AP.Flag ('a', "all", "Runs everything", lam o. {o with o.all = true})
] in

let args = argparserParse argspec (tail argv) in



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

let parser = argparserAddParamOption 'O' "optimization-level" "LEVEL"
                                     "Sets the optimization level."
                                     (lam p. lam o. {o with optLevel = string2int p})
                                     parser
in

let parser = argparserAddParamOption 'D' "define" "DEFINITION"
                                     "Add C preprocessor definition."
                                     (lam p. lam o. {o with defines = snoc o.defines p})
                                     parser
in

let parser = argparserAddLongParamOption "a-very-long-option-name" "fooparam"
                                         "Dummy option with a very long name."
                                         (lam _. lam o. o)
                                         parser
in

-- Used to test usage print with linewidth 80. Make sure this is commented out
-- when finished testing the usage print.
let _ = print (join ["\n", argparserUsage 80 parser, "\n"]) in

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
utest argparserParse ["--optimization-level", "71"] parser with {defaults with optLevel = 71} in
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

utest argparserParse ["-DMCORE"] parser with {defaults with defines = ["MCORE"]} in

utest argparserParse ["-Dh", "--define", "TEST"] parser with {defaults with defines = ["h", "TEST"]} in

()
