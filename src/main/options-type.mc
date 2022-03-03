include "tuning/tune-options.mc"

-- Options type
type Options = {
  debugParse : Bool,
  debugGenerate : Bool,
  debugTypeAnnot : Bool,
  debugProfile : Bool,
  exitBefore : Bool,
  disablePruneExternalUtests : Bool,
  disablePruneExternalUtestsWarning : Bool,
  runTests : Bool,
  runtimeChecks : Bool,
  disableOptimizations : Bool,
  useTuned : Bool,
  compileAfterTune : Bool,
  accelerate : Bool,
  cpuOnly : Bool,
  typeCheck : Bool,
  printHelp : Bool,
  toJavaScript : Bool,
  output : Option String,
  tuneOptions : TuneOptions
}
