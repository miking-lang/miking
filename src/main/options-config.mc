include "arg.mc"
include "options-type.mc"

-- Options configuration
let optionsConfig : ParseConfig Options = [
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
      let o: Options = p.options in {o with disablePruneExternalUtests = true}),
  ([("--disable-prune-warning", "", "")],
    "Disable warning when pruning utests with missing external dependencies",
    lam p: ArgPart Options.
      let o: Options = p.options in
        {o with disablePruneExternalUtestsWarning = true}),
  ([("--test", "", "")],
    "Generate utest code",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with runTests = true}),
  ([("--runtime-checks", "", "")],
    "Enables runtime checks",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with runtimeChecks = true}),
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
  ([("--accelerate-cuda", "", "")],
    "Compile into an accelerated executable using the CUDA backend",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with accelerateCuda = true}),
  ([("--accelerate-futhark", "", "")],
    "Compile into an accelerated executable using the Futhark backend",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with accelerateFuthark = true}),
  ([("--check-cuda-well-formed", "", "")],
    join ["Runs the well-formedness checks for the CUDA backend, even when ",
          "compiling without acceleration"],
    lam p: ArgPart Options.
      let o: Options = p.options in {o with checkCudaWellFormed = true}),
  ([("--cpu-only", "", "")],
    "Translate accelerated code to multicore CPU code",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with cpuOnly = true}),
  ([("--use-32bit-integers", "", "")],
    "Enables use of 32-bit integers in the C compiler",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with use32BitIntegers = true}),
  ([("--use-32bit-floats", "", "")],
    "Enables use of 32-bit floating-point numbers in the C compiler",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with use32BitFloats = true}),
  ([("--keep-dead-code", "", "")],
    "Disable dead code elimination pass",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with keepDeadCode = true}),
  ([("--to-js", "", "")],
    "Compile a file to JavaScript",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with toJavaScript = true}),
  ([("--js-target", " ", "[web|node|=generic]")],
    "Specific JavaScript runtime to target, defaults to generic",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with jsTarget = Some (argToString p)}),
  ([("--output", " ", "<file>")],
    "Write output to <file> when compiling",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with output = Some (argToString p)}),
  ([("--help", "", "")],
    "Display this list of options",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with printHelp = true})
]
