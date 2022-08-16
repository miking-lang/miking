include "tuning/tune-options.mc"

-- Options type
type Options = {
  debugParse : Bool,
  debugGenerate : Bool,
  debugTypeAnnot : Bool,
  debugTypeCheck : Bool,
  debugProfile : Bool,
  exitBefore : Bool,
  disablePruneExternalUtests : Bool,
  disablePruneExternalUtestsWarning : Bool,
  runTests : Bool,
  runtimeChecks : Bool,
  disableOptimizations : Bool,
  useTuned : Bool,
  compileAfterTune : Bool,
  accelerateCuda : Bool,
  accelerateFuthark : Bool,
  checkCudaWellFormed : Bool,
  cpuOnly : Bool,
  use32BitIntegers : Bool,
  use32BitFloats : Bool,
  keepDeadCode : Bool,
  printHelp : Bool,
  toJavaScript : Bool,
  jsTarget : String,
  disableJsGeneralOptimizations : Bool,
  disableJsTCO : Bool,
  output : Option String,
  tuneOptions : TuneOptions
}
