include "arg.mc"
include "common.mc"

-- Options type
type Options = {
  debugParse : Bool,
  debugGenerate : Bool,
  debugTypeAnnot : Bool,
  debugProfile : Bool,
  exitBefore : Bool,
  pruneExternalUtests : Bool,
  runTests : Bool,
  disableOptimizations : Bool,
  useTuned : Bool,
  compileAfterTune : Bool,
  cpuOnly : Bool,
  typeCheck : Bool,
  printHelp : Bool,
  output : Option String
}

-- Default values for options
let optionsDefault = {
  debugParse = false,
  debugGenerate = false,
  debugTypeAnnot = false,
  debugProfile = false,
  exitBefore = false,
  pruneExternalUtests = true,
  runTests = false,
  disableOptimizations = false,
  useTuned = false,
  compileAfterTune = false,
  cpuOnly = false,
  typeCheck = false,
  printHelp = false,
  output = None ()
}

-- Options configuration
let optionsConfig : ParseConfig = [
  ([("--debug-parse", "", "")],
    "Print the AST after parsing",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugParse = true}),
  ([("--debug-generate", "", "")],
    "Print the AST after code generation",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugGenerate = true}),
  ([("--debug-type-annot", "", "")],
    "Print the AST after adding type annotations",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugTypeAnnot = true}),
  ([("--debug-profile", "", "")],
    "Instrument profiling expressions to AST",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugProfile = true}),
  ([("--exit-before", "", "")],
    "Exit before evaluation or compilation",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with exitBefore = true}),
  ([("--disable-prune-utests", "", "")],
    "Disable pruning of utests with missing external dependencies",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with pruneExternalUtests = false}),
  ([("--test", "", "")],
    "Generate utest code",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with runTests = true}),
  ([("--disable-optimizations", "", "")],
    "Disables optimizations to decrease compilation time",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with disableOptimizations = true}),
  ([("--tuned", "", "")],
    "Use tuned values when compiling, or as defaults when tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with useTuned = true}),
  ([("--compile", "", "")],
    "Compile directly after tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with compileAfterTune = true}),
  ([("--cpu-only", "", "")],
    "Translate accelerated code to multicore CPU code",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with cpuOnly = true}),
  ([("--typecheck", "", "")],
    "Type check the program before evaluation or compilation",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with typeCheck = true}),
  ([("--output", " ", "<file>")],
    "Write output to <file> when compiling",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with output = Some (argToString p)}),
  ([("--help", "", "")],
    "Display this list of options",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with printHelp = true})
]

-- Get the help string for options
let optionsHelpString : ParseConfig -> String = lam config.
  argHelpOptions config

let parseOptions : [String] -> ParseConfig -> ArgResult Options = lam args. lam config.
  let result =
    argParse_general {args = args, optionsStartWith = ["--"]} optionsDefault config
  in
  match result with ParseOK r then r
  else argPrintError result; exit 1

-- Split the program arguments before and after the empty '--'
let splitDashDash = lam lst.
  match index (eqString "--") lst with Some n then
    let r = splitAt lst n in
    {first = r.0, last = tail r.1}
  else
    {first = lst, last = []}

-- Split the program arguments at the first occurrence of a non-option.
let splitOptionPrefix = lam lst.
  match index (compose not (isPrefix eqChar "--")) lst with Some n then
    let r = splitAt lst n in
    {first = r.0, last = r.1}
  else
    {first = lst, last = []}
