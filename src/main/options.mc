include "arg.mc"
include "common.mc"

-- Options type
type Options = {
  debugParse : Bool,
  debugGenerate : Bool,
  debugTypeAnnot : Bool,
  debugProfile : Bool,
  exitBefore : Bool,
  runTests : Bool,
  disableOptimizations : Bool,
  useTuned : Bool,
  compileAfterTune : Bool,
  cpuOnly : Bool,
  typeCheck : Bool,
  printHelp : Bool
}

-- Default values for options
let options = {
  debugParse = false,
  debugGenerate = false,
  debugTypeAnnot = false,
  debugProfile = false,
  exitBefore = false,
  runTests = false,
  disableOptimizations = false,
  useTuned = false,
  compileAfterTune = false,
  cpuOnly = false,
  typeCheck = false,
  printHelp = false
}

-- Options configuration
let config = [
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
  ([("--exit-before", "", "")],
    "Exit before evaluation or compilation",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with exitBefore = true}),
  ([("--test", "", "")],
    "Generate utest code",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with runTests = true}),
  ([("--disable-optimizations", "", "")],
    "Disables optimizations to decrease compilation time",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with runTests = true}),
  ([("--tuned", "", "")],
    "Use tuned values when compiling",
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
  ([("--help", "", "")],
    "Display this list of options",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with printHelp = true})
]

let optionsHelpString : Unit -> String = lam.
  argHelpOptions config

let parseOptions : [String] -> Options = lam args.
  let result =
    argParse_general {args = args, optionsStartWith = ["--"]} options config
  in
  match result with ParseOK r then r.options
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
