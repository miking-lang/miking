-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple and extensible library for command line
-- argument parsing.

include "string.mc"
include "seq.mc"
include "char.mc"
include "math.mc"

type ArgResult = {
  strings : [String],
  options : a
}

type ArgPart = {
  options : a,
  fail : Ref (Option ArgResult),
  str : String
}

type ParseOption = (String, String, String)
type ParseConfig = [([ParseOption], String, a -> String -> a)]

type ParseType
con ParseTypeInt : String -> ParseType
con ParseTypeIntMin : (String, Int) -> ParseType
con ParseTypeFloat : String -> ParseType

type ParseResult
con ParseOK : ArgResult -> ParseResult
con ParseFailUnknownOption : String -> ParseResult
con ParseFailMissingOpArg : String -> ParseResult
con ParseFailConversion : (ParseType, String) -> ParseResult

-- Creates a new string with new lines, and breaks between words.
-- Assumes that the string is currently at 'startPos', and
-- also adds 'indent' number of spaces before the next line.
let stringLineFormat = lam s. lam width. lam indent. lam startPos.
  recursive
    let next = lam s. lam acc. lam w. lam pos. lam space.
      let pos = addi (length w) pos in
      if leqi pos width then
        let pos = addi pos (length space) in
        let acc = concat acc w in
        let acc = if leqi pos width then concat acc space else acc in
          work s acc [] pos
      else
        let acc = concat acc (cons '\n' (make indent ' ')) in
        let w = concat w space in
        work s (concat acc w) [] (addi indent (length w))
    let work = lam s. lam acc. lam w. lam pos.
      match s with [c] ++ rest then
        if eqChar c ' ' then
          next rest acc w pos " "
        else
          work rest acc (snoc w c) pos
      else
        if eqi (length w) 0 then acc
        else next s acc w pos ""
  in
    work s [] [] startPos


type Options_argHelpOptions = {
  lineWidth : Int,
  indent : Int,
  spaceToText : Int
}

let argHelpOptions_defaults = {
  lineWidth = 80,
  indent = 2,
  spaceToText = 2
}

let argHelpOptions_general =
  lam options : Options_argHelpOptions.
  lam opConfig : a.
  let opStrings = map (lam e.
    match e with (lst, _, _) then
      let s2 = map (lam triple. match triple with (s1,s2,s3) then join [s1,s2,s3] else never) lst in
      strJoin ", " s2
    else never) opConfig
  in
  let maxLen = foldl (lam acc. lam x. maxi (length x) acc) 0 opStrings in
  let opDesc = map (lam e. match e with (_, s, _) then s else never) opConfig in
  let f = lam x. lam desc.
    let start = join [make options.indent ' ', x,
                      make (addi (subi maxLen (length x)) options.spaceToText) ' '] in
    let before = addi (addi maxLen options.indent) options.spaceToText in
     let x = concat start (stringLineFormat desc options.lineWidth before before) in
     x
  in
    strJoin "\n" (zipWith f opStrings opDesc)



let argHelpOptions = argHelpOptions_general argHelpOptions_defaults


-- argument value conversion --

let argToString = lam p : ArgPart.
  p.str

let argToInt = lam p : ArgPart.
  let v = string2int p.str in
  if stringIsInt p.str then string2int p.str
  else modref p.fail (Some (ParseTypeInt p.str)); 0

let argToFloat = lam p : ArgPart.
  if stringIsFloat p.str then string2float p.str
  else modref p.fail (Some (ParseTypeFloat p.str)); 0.

let argToIntMin = lam p : ArgPart. lam minVal.
  let v = argToInt p in
  match deref p.fail with None () then
    if lti v minVal then
      modref p.fail (Some (ParseTypeIntMin (p.str, minVal))); v
    else
      v
  else
    v



-- argParse --

type Options_argParse = {
  args : [String],
  optionsStartWith : [String]
}


let argParse_defaults = {
  args = tail argv,
  optionsStartWith = ["-"]
}




-- Main argument parsing function.
let argParse_general =
  lam options : Options_argParse. lam argParseDefaults. lam argParseConfig.
  recursive
    -- Match one option
    let matchOption = lam str. lam confLst : ParseConfig.
     match confLst with [(opLst, _, f)] ++ rest then
       match find (lam x. match x with (s, _, _)
                          then isPrefix eqChar s str else never) opLst
       with Some (s, sep, _)
       then Some (s, sep, f)
       else matchOption str rest
     else None ()
    -- Handle parsing of options
    let handleOptionParsing = lam f. lam o. lam opstr. lam s.
      let failCode = ref (None ()) in
      let argOptions = f {options = o, str = s, fail = failCode} in
      match deref failCode with Some pType then
        (Some (ParseFailConversion (pType, opstr)), argOptions)
      else
        (None (), argOptions)
    -- Main parsing loop
    let argMain = lam argOptions. lam strings. lam args.
      match args with [s] ++ xs then
        match matchOption s argParseConfig with Some (op, sep, f) then
          if eqi (length sep) 0 then
            -- No value to the option
            if eqString s op then
              let parse = handleOptionParsing f argOptions "" s in
              match parse with (Some ret, _) then
                ret
              else match parse with (None(), argOptions) then
                argMain argOptions strings xs
              else never
            else
              ParseFailUnknownOption s
          else
            -- TODO(davbr,2021-05-22): Add handling without space, e.g, "--foo=7"
            --                         and other separators than space
            if eqString s op then
              match xs with [s2] ++ xs then
                match matchOption s2 argParseConfig with Some _ then
                  ParseFailMissingOpArg s
                else
                  let parse = handleOptionParsing f argOptions s s2 in
                  match parse with (Some ret, _) then
                    ret
                  else match parse with (None(), argOptions) then
                    argMain argOptions strings xs
                  else never
              else
                 ParseFailMissingOpArg s
            else
              ParseFailUnknownOption s
        else
          if any (lam x. isPrefix eqChar x s) options.optionsStartWith then
            ParseFailUnknownOption s
          else
            -- Not an option, add to strings
            argMain argOptions (snoc strings s) xs
      else
        ParseOK {strings = strings, options = argOptions}
  in
    argMain argParseDefaults [] options.args



let argParse = argParse_general argParse_defaults

-- Error feedback --

let argPrintErrorString = lam result.
  switch result
  case ParseOK _ then
    "Parse OK."
  case ParseFailUnknownOption s then
    join ["Unknown option ", s, "."]
  case ParseFailMissingOpArg s then
    join ["Option ", s, " is missing an argument value."]
  case ParseFailConversion (ptype, s) then
    switch ptype
    case ParseTypeInt sval then
      join
        ["Option ", s, " expects an integer value, but received '", sval, "'."]
    case ParseTypeFloat sval then
      join ["Option ", s, " expects a float value, but received '", sval, "'."]
    case ParseTypeIntMin (_, minVal) then
      join
        ["Option ", s, " expects an integer value of at least ",
         int2string minVal, "."]
    end
  end

let argPrintError = lam result.
  print (join [argPrintErrorString result, "\n"])


mexpr


let s1 = "This is a test that we can take a look at." in
let s2 = "This is a \n   test that we \n   can take a \n   look at." in
utest stringLineFormat s1 16 3 5 with s2 in
let s2 = "This is a test\n   that we can\n   take a look\n   at." in
utest stringLineFormat s1 14 3 0 with s2 in
let s2 = "This is a \n test that we\n can take a \n look at." in
utest stringLineFormat s1 13 1 0 with s2 in

type Options = {
  foo : Bool,
  len : Int,
  message : String,
  real: Float
} in

let default = {
  foo = false,
  len = 7,
  message = "",
  real = 0.
} in

let config = [
  ([("--foo", "", "")],
    "This is a boolean option. ",
    lam p : ArgPart. let o : Options = p.options in {o with foo = true}),
  ([("--len", " ", "<value>")],
    "A number argument followed by equality and then the integer value.",
    lam p : ArgPart. let o : Options = p.options in {o with len = argToIntMin p 1}),
  ([("-m", " ", "<msg>"),("--message", " ", "<msg>")],
    "A string argument, with both short and long form arguments, and different separators.",
    lam p : ArgPart. let o : Options = p.options in {o with message = argToString p}),
  ([("--real", " ", "<value>")],
    "A number argument followed by equality and then the float value.",
    lam p : ArgPart. let o : Options = p.options in {o with real = argToFloat p })
] in

let testOptions = {
  argParse_defaults with
  args = ["file.mc", "--len", "12", "--foo", "-m", "mymsg", "--real", "1.", "f2"]
} in
let argParseCustom = argParse_general testOptions in
let res : ArgResult =
  match argParseCustom default config with ParseOK r then r
  else error "Incorrect type"
in
let opt : Options = res.options in
utest res.strings with ["file.mc", "f2"] using eqSeq eqString in
utest opt.foo with true in
utest opt.message with "mymsg" in
utest opt.len with 12 in

let testOptions = {argParse_defaults with args = ["--len", "noInt"]} in
let res = argParse_general testOptions default config in
utest res with ParseFailConversion (ParseTypeInt ("noInt"), "--len") in
utest argPrintErrorString res with
  "Option --len expects an integer value, but received 'noInt'."
in

let testOptions = {argParse_defaults with args = ["--real", "noFloat"]} in
let res = argParse_general testOptions default config in
utest res with ParseFailConversion (ParseTypeFloat ("noFloat"), "--real") in
utest argPrintErrorString res with
  "Option --real expects a float value, but received 'noFloat'."
in

let testOptions = {argParse_defaults with args = ["--len", "-2"]} in
let res = argParse_general testOptions default config in
utest res with ParseFailConversion (ParseTypeIntMin ("-2", 1), "--len") in
utest argPrintErrorString res
with "Option --len expects an integer value of at least 1." in

let testOptions = {argParse_defaults with args = ["--messageNo", "msg"]} in
let res = argParse_general testOptions default config in
utest res with ParseFailUnknownOption "--messageNo" in
utest argPrintErrorString res with "Unknown option --messageNo." in

let testOptions = {argParse_defaults with args = ["--message"]} in
let res = argParse_general testOptions default config in
utest res with ParseFailMissingOpArg "--message" in
utest argPrintErrorString res
with "Option --message is missing an argument value." in

let testOptions = {argParse_defaults
with args = ["--message", "--len", "78"]} in
let res = argParse_general testOptions default config in
utest res with ParseFailMissingOpArg "--message" in
utest argPrintErrorString res
with "Option --message is missing an argument value." in

let testOptions = {argParse_defaults with args = ["--unknown"]} in
let res = argParse_general testOptions default config in
utest res with ParseFailUnknownOption("--unknown") in


let text = argHelpOptions config in
--print "\n---\n"; print text; print "\n---\n";
utest length text with 448 in

()
