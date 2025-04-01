include "arg.mc"
include "options-type.mc"

-- Options configuration
let optionsConfig : ParseConfig Options = [
  ([("--to-jvm", "", "")],
    "Compile to JVM",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with toJVM = true}),
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
  ([("--debug-type-check", "", "")],
    "Print an interactive (HTML) representation of the AST after type checking",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugTypeCheck = true}),
  ([("--debug-profile", "", "")],
    "Instrument profiling expressions to AST",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugProfile = true}),
  ([("--debug-shallow", "", "")],
    "Print the AST after lowering nested patterns to shallow ones",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugShallow = true}),
  ([("--debug-constant-fold", "", "")],
    "Print the AST after constant folding and constant propagation",
     lam p: ArgPart Options.
      let o: Options = p.options in {o with debugConstantFold = true}),
  ([("--debug-dprint", "", "")],
    "Replace dprint with a generated pprint. Warning: might introduce 'unbound' errors if some functions aren't imported.",
     lam p: ArgPart Options.
      let o: Options = p.options in {o with debugDprint = true}),
  ([("--debug-phases", "", "")],
    "Show debug and profiling information about each pass",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugPhases = true}),
  ([("--debug-phase", " ", "<phase>")],
    "Print a json representation of the AST after the given pass. Can be given multiple times.",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugDumpPhases = setInsert (argToString p) o.debugDumpPhases}),
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
  ([("--enable-constant-fold", "", "")],
    "Enables constant folding and constant propagation",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with enableConstantFold = true}),
  ([("--enable-constructor-types", "", "")],
    "Enables constructor types and exhaustiveness checking",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with enableConstructorTypes = true}),
  ([("--tuned", "", "")],
    "Use tuned values when compiling, or as defaults when tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with useTuned = true}),
  ([("--compile", "", "")],
    "Compile directly after tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with compileAfterTune = true}),
  ([("--accelerate", "", "")],
    "Enables expression acceleration which outputs GPU code by default",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with accelerate = true}),
  ([("--tensor-max-rank", " ", "<rank>")],
    "Sets the maximum rank of tensors to <rank> in accelerated code",
    lam p: ArgPart Options.
      let o: Options = p.options in
      {o with accelerateTensorMaxRank = string2int (argToString p)}),
  ([("--debug-accelerate", "", "")],
    join ["Enables static and dynamic checks for accelerated expressions, ",
          "and runs the program on the CPU."],
    lam p: ArgPart Options.
      let o: Options = p.options in {o with debugAccelerate = true,
                                            runtimeChecks = true}),
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
      let o: Options = p.options in {o with jsTarget = argToString p}),
  ([("--js-disable-optimizations", "", "")],
    "Disable JavaScript general optimizations",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with disableJsGeneralOptimizations = true}),
  ([("--js-disable-tco", "", "")],
    "Disable JavaScript tail-call optimizations",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with disableJsTCO = true}),
  ([("--output", " ", "<file>")],
    "Write output to <file> when compiling",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with output = Some (argToString p)}),
  ([("--help", "", "")],
    "Display this list of options",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with printHelp = true}),
  ([("--mlang-pipeline", "", "")],
    "Compile using the MLang Pipeline. Note that this is an unstable, experimental feature!",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with mlangPipeline = true}),
      ([("--experimental-records", "", "")],
    "Compile using experimental records. Note that this is an unstable, experimental feature!",
    lam p: ArgPart Options.
      let o: Options = p.options in {o with experimentalRecords = true}),
  ([("--disable-strict-sum-extension", "", "")],
    (join ["Disable the strict composition checks for sum extension when",
      "using the --mlang-pipeline. By default, you must use '+=' when",
      "extending another syn or sem. When this flag is used, you are ",
      "also allowed to use '=' everywhere."]),
    lam p: ArgPart Options.
      let o: Options = p.options in {o with disableStrictSumExtension = true})
]
