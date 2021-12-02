include "arg.mc"
include "options-type.mc"

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
  ([("--accelerate", "", "")],
    "Compile into an accelerated executable",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with accelerate = true}),
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
