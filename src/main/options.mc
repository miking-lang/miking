include "arg.mc"
include "common.mc"
include "options-type.mc"
include "tuning/tune-options.mc"

-- Default values for options
let optionsDefault : Options = {
  toJVM = false,
  debugParse = false,
  debugGenerate = false,
  debugTypeAnnot = false,
  debugTypeCheck = false,
  debugProfile = false,
  debugShallow = false,
  debugConstantFold = false,
  debugPhases = false,
  exitBefore = false,
  disablePruneExternalUtests = false,
  disablePruneExternalUtestsWarning = false,
  runTests = false,
  runSpecificTest = None (),
  runtimeChecks = false,
  disableOptimizations = false,
  enableConstantFold = false,
  enableConstructorTypes = false,
  useTuned = false,
  compileAfterTune = false,
  accelerate = false,
  accelerateTensorMaxRank = 3,
  debugAccelerate = false,
  cpuOnly = false,
  use32BitIntegers = false,
  use32BitFloats = false,
  keepDeadCode = false,
  printHelp = false,
  toJavaScript = false,
  jsTarget = "generic",
  disableJsGeneralOptimizations = false,
  disableJsTCO = false,
  output = None (),
  tuneOptions = tuneOptionsDefault,
  mlangPipeline = false
}

-- Get the help string for options
let optionsHelpString : ParseConfig Options -> String = lam config.
  argHelpOptions config

let parseOptions : [String] -> ParseConfig Options -> ArgResult Options = lam args. lam config.
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
